(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

open Misc
open Idents
open Signature
open Signature
open Names
open Name_utils
open Heptagon
open Hept_utils
open Hept_mapfold

let to_be_inlined s = !Compiler_options.flatten || (List.mem s !Compiler_options.inline)

let fresh = Idents.gen_var "inline"

let mk_unique_node nd =
  let mk_bind vd =
    let id = fresh (Idents.name vd.v_ident) in
    (vd.v_ident, { vd with v_ident = id; v_clock = Clocks.fresh_clock () }) in
  let subst = List.map mk_bind (nd.n_block.b_local
                                @ nd.n_input @ nd.n_output) in

  let subst_var_dec _ () vd = (List.assoc vd.v_ident subst, ()) in

  let subst_edesc funs () ed =
    let ed, () = Hept_mapfold.edesc funs () ed in
    let find vn = (List.assoc vn subst).v_ident in
    (match ed with
      | Evar vn -> Evar (find vn)
      | Elast vn -> Elast (find vn)
      | Ewhen (e, cn, vn) -> Ewhen (e, cn, find vn)
      | Emerge (vn, e_l) -> Emerge (find vn, e_l)
      | _ -> ed), ()
  in

  let subst_eqdesc funs () eqd =
    let (eqd, ()) = Hept_mapfold.eqdesc funs () eqd in
    match eqd with
    | Eeq (pat, e) ->
        let rec subst_pat pat = match pat with
          | Evarpat vn -> Evarpat (try (List.assoc vn subst).v_ident
                                   with Not_found -> vn)
          | Etuplepat patl -> Etuplepat (List.map subst_pat patl) in
        (Eeq (subst_pat pat, e), ())
    | _ -> raise Errors.Fallback in

  let funs = { defaults with
                 var_dec = subst_var_dec;
                 eqdesc = subst_eqdesc;
                 edesc = subst_edesc; } in
  fst (Hept_mapfold.node_dec funs () nd)

let exp funs (env, newvars, newequs) exp =
  let exp, (env, newvars, newequs) = Hept_mapfold.exp funs (env, newvars, newequs) exp in
  match exp.e_desc with
  | Eiterator (it, { a_op = Enode nn; }, _, _, _, _) when to_be_inlined nn ->
      Format.eprintf
        "WARN: inlining iterators (\"%s %s\" here) is unsupported.@."
        (Hept_printer.iterator_to_string it) (fullname nn);
      (exp, (env, newvars, newequs))

  | Eapp ({ a_op = (Enode nn | Efun nn);
            a_async = None; (* Async can't be inlined *)
            a_unsafe = false; (* Unsafe can't be inlined *)
            a_inlined = inlined } as op, argl, rso) when inlined || to_be_inlined nn ->
    begin try
      let add_reset eq = match rso with
        | None -> eq
        | Some x -> mk_equation (Ereset (mk_block [eq], x)) in

      let ni = mk_unique_node (QualEnv.find nn env) in

      let static_subst =
        List.combine (List.map (fun p -> (local_qn p.p_name)) ni.n_params)
          op.a_params in

      (* Perform [static_exp] substitution. *)
      let ni =
        let apply_sexp_subst_sexp funs () sexp = match sexp.se_desc with
          | Svar s -> ((try List.assoc s static_subst
                        with Not_found -> sexp), ())
          | _ -> Global_mapfold.static_exp funs () sexp in

        let funs =
          { defaults with global_funs =
              { Global_mapfold.defaults with Global_mapfold.static_exp =
                  apply_sexp_subst_sexp; }; } in

        fst (Hept_mapfold.node_dec funs () ni) in

      let mk_input_equ vd e = mk_equation (Eeq (Evarpat vd.v_ident, e)) in
      let mk_output_exp vd = mk_exp (Evar vd.v_ident) vd.v_type ~linearity:vd.v_linearity in

      let newvars = ni.n_input @ ni.n_block.b_local @ ni.n_output @ newvars
      and newequs =
        List.map2 mk_input_equ ni.n_input argl
        @ List.map add_reset ni.n_block.b_equs
        @ newequs in

      (* For clocking reason we cannot create 1-tuples. *)
      let res_e = match ni.n_output with
        | [o] -> mk_output_exp o
        | _ ->
            mk_exp (Eapp ({ op with a_op = Etuple; },
                          List.map mk_output_exp ni.n_output, None)) exp.e_ty
                   ~linearity:exp.e_linearity in
      (res_e, (env, newvars, newequs))

    with
      | Not_found -> Format.eprintf "Could not inline %s@." (fullname nn);
        exp, (env, newvars, newequs)
    end
  | _ -> exp, (env, newvars, newequs)

let block funs (env, newvars, newequs) blk =
  let (blk, (env, newvars', newequs')) =
    Hept_mapfold.block funs (env, [], []) blk in
  ({ blk with b_local = newvars' @ blk.b_local; b_equs = newequs' @ blk.b_equs; },
   (env, newvars, newequs))

let node_dec funs (env, newvars, newequs) nd =
  let nd, (env, newvars, newequs) =
    Hept_mapfold.node_dec funs (env, newvars, newequs) nd in
  let nd = { nd with n_block =
      { nd.n_block with b_local = newvars @ nd.n_block.b_local;
        b_equs = newequs @ nd.n_block.b_equs } } in
  let env = QualEnv.add nd.n_name nd env in
   nd, (env, [], [])

let program p =
  let funs =
    { defaults with exp = exp; block = block; node_dec = node_dec; eq = eq; } in
  let (p, (_, newvars, newequs)) = Hept_mapfold.program funs (QualEnv.empty, [], []) p in
  assert (newvars = []);
  assert (newequs = []);
  p