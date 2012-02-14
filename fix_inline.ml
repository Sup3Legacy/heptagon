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
open Types
open Names
open Minils
open Mls_utils

let to_be_inlined s = !Compiler_options.flatten || (List.mem s !Compiler_options.inline)

let fresh = Idents.gen_var "inline"


(* Return a fresh vd, with the corresponding substitution added in subst *)
let freshen_vd _ (cenv,subst) vd =
  let new_id = fresh (Idents.name vd.v_ident) in
  let new_vd = { vd with v_ident = new_id; v_clock = Clocks.fresh_clock () } in
  let subst = Idents.Env.add vd.v_ident new_id subst in
  new_vd, (cenv,subst)

let var_dec funs (cenv,subst) vd =
  let new_vd, (cenv,subst) = freshen_vd funs (cenv,subst) vd in
  Mls_mapfold.var_dec funs (cenv,subst) new_vd

let var_ident _ (cenv,subst) id =
  let id =
    try Idents.Env.find id subst
    with _ -> Misc.internal_error "inlining ident not found"
  in
  id, (cenv,subst)

let apply_cenv_subst _ (cenv,subst) sexp = match sexp.se_desc with
  | Svar s ->
      (try QualEnv.find s cenv with Not_found -> sexp), (cenv,subst)
  | _ -> raise Errors.Fallback


(* [cenv] is the qualname environment to allow static param substitutions
   [subst] is the ident environment to allow ident substitutions
   Inputs and outputs should be declared above it and needed substitutions given in subst. *)
let node_block funs (cenv,subst) b =
  let funs =
    { defaults with var_dec = var_dec;
        global_funs = { Global_mapfold.defaults with Global_mapfold.var_ident = var_ident;
                        Global_mapfold.static_exp = apply_sexp_subst_sexp; }}
  in
  fst (Hept_mapfold.block_it funs (cenv,subst) nd.n_block), (cenv,subst)


let eqdesc funs (env,newvars,newequs) eqd = match eqd with
  | Eiterator (it, { a_op = Enode nn; }, _, _, _, _) when to_be_inlined nn ->
      Format.eprintf
        "WARN: inlining iterators (\"%s %s\" here) is unsupported.@."
        (Hept_printer.iterator_to_string it) (fullname nn);
      eq, (env, newvars, newequs)
  | Eapp ({ a_op = (Enode nn | Efun nn);
             a_unsafe = false; (* Unsafe can't be inlined *)
             a_inlined = inlined } as op, argl, rso) when inlined || to_be_inlined nn ->
      begin match nn with
      | Pervasives -> eq, (env,newvars,newequs)
      | Module m when m = Modules.g_env.current_mod ->

      | _ ->
          Format.eprintf "%aInlining of non local function is not supported for now.@."
            print_location loc;
          raise Errors.Error
      end
  | _ -> (* nothing to do *) eq, (env, newvars, newequs)


(*
  let exp, (env, newvars, newequs) = Hept_mapfold.exp funs (env, newvars, newequs) exp in
  match exp.e_desc with

  | Eapp ({ a_op = (Enode nn | Efun nn);
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

*)


let node_dec funs (env, newvars, newequs) nd =
  let nd, (env, newvars, newequs) = Hept_mapfold.node_dec funs (env, newvars, newequs) nd in
  let nd = { nd with n_block = { nd.n_block with b_local = newvars @ nd.n_block.b_local;
                                                 b_equs = newequs @ nd.n_block.b_equs } }
  in
  nd, (env, [], [])


let program p =
  (* [env] is the environment mapping a node name to its node_dec. *)
  (* TODO inlining between module should be dealt with and should change only this env.
     It'll come from inline annotations at the definition point. *)
  let env = List.filter (function Pnode _ -> true | _ -> false) p.p_desc in
  let env = List.fold_left (fun env pd -> match pd with
                              | Pnode nd -> QualName.Env.add nd.n_name nd env
                              | _ -> env)
                           QualName.Env.empty env
  in
  let funs = { defaults with node_dec = node_dec; exp = exp; } in
  let p, () = Hept_mapfold.program funs () p in
  p
