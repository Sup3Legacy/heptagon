(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)


(** Require function and node calls to be normalized :
  (y,..,y) = f (x,..,x)
  No expression is allowed around the call or as arguments.
  Thanks to that, The correct substitution is computed.
  There are 3 environments, one for the idents,
  one for the static params and one for the linear annotations
*)

open Misc
open Idents
open Signature
open Names
open Heptagon
open Hept_utils

let to_be_inlined s = !Compiler_options.flatten || (List.mem s !Compiler_options.inline)

let fresh = Idents.gen_var "inline"


(* [inline] tells whether we are inside an inlined node or not.
   [nenv] is the environment for the nodes' code.
   [cenv] is the qualname environment to allow static param substitutions
   [subst] is the ident environment to allow ident substitutions
   Inputs and outputs should be declared above it and needed substitutions given in subst. *)


let var_dec funs (inline, nenv, cenv, subst) vd =
(* Return a fresh vd, with the corresponding substitution added in subst *)
  let freshen_vd _ (inline, nenv, cenv, subst) vd =
    if inline then begin
      let new_id = fresh (Idents.name vd.v_ident) in
      let new_vd = { vd with v_ident = new_id; v_clock = Clocks.fresh_clock () } in
      let subst = Idents.Env.add vd.v_ident new_id subst in
      new_vd, (inline, nenv, cenv, subst)
    end else
      vd, (inline, nenv, cenv, subst)
  in
  let new_vd, (inline, nenv, cenv, subst) = freshen_vd funs (inline, nenv, cenv, subst) vd in
  Hept_mapfold.var_dec funs (inline, nenv, cenv, subst) new_vd

let var_ident _ (inline, nenv, cenv, subst) id =
  
  let id =
    if inline then
      try Format.eprintf "Looking for %a@." Idents.print_ident id; Idents.Env.find id subst
      with Not_found ->
         Format.eprintf "not found %a in %a@." Idents.print_ident id
         (Idents.Env.print_t Idents.print_ident) subst; 
        id
    else
      id
  in
  id, (inline, nenv, cenv, subst)

let apply_cenv_subst funs (inline, nenv, cenv, subst) sexp =
  let sexp, _ = Global_mapfold.static_exp funs (inline, nenv, cenv, subst) sexp in
  let sexp = match sexp.se_desc with
    | Svar s ->
        (try QualEnv.find s cenv with Not_found -> sexp)
    | _ -> sexp
  in
  sexp, (inline, nenv, cenv, subst)



let combine_subst subst old_l new_l =
  let add subst old niew =
    let niew = try Idents.Env.find niew subst with Not_found -> niew in
    Idents.Env.add old niew subst
  in
  List.fold_left2 add subst old_l new_l

let combine_cenv cenv old_l new_l =
  let add cenv old niew =
    let niew, _ =
      Global_mapfold.static_exp_it
        {Global_mapfold.defaults with Global_mapfold.static_exp = apply_cenv_subst}
        (true, (),cenv,()) niew
    in
    QualEnv.add old niew cenv
  in
  List.fold_left2 add cenv old_l new_l

(* TODO allow this function to load the necessary .epo and update the [nenv]. *)
let node_dec_from_qualname nn loc nenv = match nn.qual with
  | m when m = Modules.g_env.Modules.current_mod ->
      QualEnv.find nn nenv
  | Module _ -> (* TODO *)
      Format.eprintf "%aWarning inlining of non local function is not supported for now.@."
            Location.print_location loc;
      raise Not_found
  | LocalModule _ ->
      Format.eprintf "%aWarning inlining of static parameter function is not supported for now.@."
        Location.print_location loc;
      raise Not_found
  | Pervasives -> raise Not_found (* Ignore inlining of pervasives since they are operators *)
  | _ -> Misc.internal_error "inlining received some unexpected qualname to inline."


let eq funs (inline, nenv, cenv, subst) eq =
  let eq, (inline, nenv, cenv, subst) = Hept_mapfold.eq funs (inline, nenv, cenv, subst) eq in
  match eq.eq_desc with
  | Eeq (_, {e_desc = Eiterator (it, { a_op = Enode nn; }, _, _, _, _)}) when to_be_inlined nn ->
      Format.eprintf
        "WARN: inlining iterators (\"%s %s\" here) is unsupported.@."
        (Hept_printer.iterator_to_string it) (fullname nn);
      eq, (inline, nenv,cenv,subst)
  | Eeq(pat, {e_desc = Eapp ({ a_op = (Enode nn | Efun nn);
             a_unsafe = false; (* Unsafe can't be inlined *)
             a_inlined = inlined } as op, arg_l, rso)}) when inlined || to_be_inlined nn ->
      (*get the code to inline *)
      let code = node_dec_from_qualname nn eq.eq_loc nenv in
      (* Compute new_cenv *)
      let current_node = Idents.current_node () in (* store current node *)
      Idents.enter_node nn; (* Enter inlined node to have correct local_qn *)
      let code_params = List.map (fun p -> (local_qn p.p_name)) code.n_params in
      let new_cenv = combine_cenv cenv code_params op.a_params in
      Idents.enter_node current_node; (* get back to the current node *)
      (*Compute new_subst *)
      let code_inputs = List.map (fun vd -> vd.v_ident) code.n_input in
      let inputs = List.map
        (fun e -> match e.e_desc with
          | Evar i | Elast i -> i
          | _ -> Misc.internal_error "inlining needs arguments in normal form")
        arg_l in
      let new_subst = combine_subst subst code_inputs inputs in
      let code_outputs = List.map (fun vd -> vd.v_ident) code.n_output in
      let outputs = ident_list_of_pat pat in
      let new_subst = combine_subst new_subst code_outputs outputs in
      (* Apply the substitutions and inline the block *)
      let block, (_, nenv, _,_) =
        Hept_mapfold.block_it funs (true, nenv, new_cenv, new_subst) code.n_block
      in
      (* Add the reset *)
      let eqd = match rso with
        | None -> Eblock block
        | Some x -> (Ereset (block, x))
      in
      mk_equation eqd, (inline, nenv, cenv, subst)
  | _ -> (* nothing to do *) eq, (inline, nenv, cenv, subst)


let program p =
  let nenv = List.filter (function Pnode _ -> true | _ -> false) p.p_desc in
  let nenv = List.fold_left (fun env pd -> match pd with
                              | Pnode nd -> QualEnv.add nd.n_name nd env
                              | _ -> env)
                           QualEnv.empty nenv
  in
  let global_funs = { Global_mapfold.defaults with
    Global_mapfold.var_ident = var_ident;
    Global_mapfold.static_exp = apply_cenv_subst }
  in
  let funs = { Hept_mapfold.defaults with
    Hept_mapfold.eq = eq;
    Hept_mapfold.var_dec = var_dec;
    Hept_mapfold.global_funs = global_funs }
  in
  let p, _ = Hept_mapfold.program funs (false, nenv, QualEnv.empty, Idents.Env.empty) p in
  p
