(***********************************************************************)
(*                                                                     *)
(*                             Heptagon                                *)
(*                                                                     *)
(* Gwenael Delaval, LIG/INRIA, UJF                                     *)
(* Leonard Gerard, Parkas, ENS                                         *)
(* Adrien Guatto, Parkas, ENS                                          *)
(* Cedric Pasteur, Parkas, ENS                                         *)
(* Marc Pouzet, Parkas, ENS                                            *)
(*                                                                     *)
(* Copyright 2012 ENS, INRIA, UJF                                      *)
(*                                                                     *)
(* This file is part of the Heptagon compiler.                         *)
(*                                                                     *)
(* Heptagon is free software: you can redistribute it and/or modify it *)
(* under the terms of the GNU General Public License as published by   *)
(* the Free Software Foundation, either version 3 of the License, or   *)
(* (at your option) any later version.                                 *)
(*                                                                     *)
(* Heptagon is distributed in the hope that it will be useful,         *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of      *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the       *)
(* GNU General Public License for more details.                        *)
(*                                                                     *)
(* You should have received a copy of the GNU General Public License   *)
(* along with Heptagon.  If not, see <http://www.gnu.org/licenses/>    *)
(*                                                                     *)
(***********************************************************************)

open Misc
open Idents
open Signature
open Types
open Names
open Heptagon
open Hept_utils
open Hept_mapfold

exception Output_type_of_node_is_not_product


(* Detection if a given node must be inlined *)
let rec is_name_in_qualnamelist s l = match l with
  | [] -> false
  | h::t -> if (h.name = s.name) then true
    else is_name_in_qualnamelist s t

let is_prefix pref str =
  if ((String.length str) < (String.length pref)) then false else
  String.equal pref (String.sub str 0 (String.length pref))


let rec is_name_prefix s l = match l with
  | [] -> false
  | h::t -> if (is_prefix h s.name) then true
    else is_name_prefix s t

let to_be_inlined s =
  (!Compiler_options.flatten && not (s.qual = Pervasives))
    (* || (List.mem s !Compiler_options.inline) *)
    || (is_name_in_qualnamelist s !Compiler_options.inline)
    || (is_name_prefix s !Compiler_options.inline_prefix)

(* ======================== *)


let fresh = Idents.gen_var "inline"

let mk_unique_node nd =
  let mk_bind vd =
    let id = fresh (Idents.name vd.v_ident) in
    (vd.v_ident, { vd with v_ident = id; v_clock = Clocks.fresh_clock () }) in
  let subst =
    List.fold_left
      (fun subst vd ->
         let id, vd = mk_bind vd in
         Env.add id vd.v_ident subst)
      Env.empty
      (nd.n_input @ nd.n_output) in
  (* let subst_var_dec _ () vd = (List.assoc vd.v_ident subst, ()) in *)

  (* let subst_edesc funs () ed = *)
  (*   let ed, () = Hept_mapfold.edesc funs () ed in *)
  (*   let find vn = (List.assoc vn subst).v_ident in *)
  (*   (match ed with *)
  (*     | Evar vn -> Evar (find vn) *)
  (*     | Elast vn -> Elast (find vn) *)
  (*     | Ewhen (e, cn, vn) -> Ewhen (e, cn, find vn) *)
  (*     | Emerge (vn, e_l) -> Emerge (find vn, e_l) *)
  (*     | _ -> ed), () *)
  (* in *)

  (* let subst_eqdesc funs () eqd = *)
  (*   let (eqd, ()) = Hept_mapfold.eqdesc funs () eqd in *)
  (*   match eqd with *)
  (*   | Eeq (pat, e) -> *)
  (*       let rec subst_pat pat = match pat with *)
  (*         | Evarpat vn -> Evarpat (try (List.assoc vn subst).v_ident *)
  (*                                  with Not_found -> vn) *)
  (*         | Etuplepat patl -> Etuplepat (List.map subst_pat patl) in *)
  (*       (Eeq (subst_pat pat, e), ()) *)
  (*   | _ -> raise Errors.Fallback in *)

  let subst_var_ident _funs subst v =
    let v = Env.find v subst in
    v, subst in

  let subst_block funs subst b =
    let b_local, subst' =
      mapfold 
        (fun subst vd ->
           let id, vd = mk_bind vd in
           vd, (Env.add id vd.v_ident subst))
        subst b.b_local in
    let b, _ = Hept_mapfold.block funs subst' b in
    { b with b_local = b_local }, subst in

  (* let funs = { defaults with *)
  (*                var_dec = subst_var_dec; *)
  (*                eqdesc = subst_eqdesc; *)
  (*                edesc = subst_edesc; } in *)
  let funs = { Hept_mapfold.defaults with
                 block = subst_block;
                 global_funs = { Global_mapfold.defaults with
                                   Global_mapfold.var_ident = subst_var_ident } } in
  fst (Hept_mapfold.node_dec funs subst nd)

let exp funs (env, newvars, newequs) exp =
  let exp, (env, newvars, newequs) = Hept_mapfold.exp funs (env, newvars, newequs) exp in
  match exp.e_desc with
  | Eiterator (it, { a_op = Enode nn; }, _, _, _, _) when to_be_inlined nn ->
      Format.eprintf
        "WARN: inlining iterators (\"%s %s\" here) is unsupported.@."
        (Hept_printer.iterator_to_string it) (fullname nn);
      (exp, (env, newvars, newequs))

  | Eapp ({ a_op = (Enode nn | Efun nn);
            a_unsafe = false; (* Unsafe can't be inlined *)
            a_inlined = inlined } as op, argl, rso) when inlined || to_be_inlined nn ->
    begin try
      let add_reset eq = match rso with
        | None -> eq
        | Some x -> mk_equation (Ereset (mk_block [eq], x)) in
      
      let node_dec = QualEnv.find nn env in
      
      (* TODO: simpler alternative: use the tysubst which is stored at the "app" level? *)
      (* 			instead of recomputing it? *)
      
      (* Check if the node to be inlined contain some type parameter
      	=> value of the type: from output or input expression (typing was done)
      	Note: due to the nature of the type parameters, "t" is always alone when it appears *)
      let env_type_param = QualEnv.empty in
      
      let env_type_param = if (node_dec.n_typeparamdecs != []) then
        begin        (* We find the value of these parameters for this instance *)
        (* Outputs *)
        let list_ty_output = if (List.length node_dec.n_output ==1) then exp.e_ty::[]
          else match exp.e_ty with
            | Tprod lty -> lty
            | _ -> raise Output_type_of_node_is_not_product
        in
        let env_type_param = fst (List.fold_left
          (fun (env_acc,i) vd -> match vd.v_type with
            | Tclasstype (tname, tclass) ->
              (* i-th output of the node is a type parameter *)
              let value = List.nth list_ty_output i in
              let env_acc = QualEnv.add tname value env_acc in (* Solving the constraint about the type parameter *)
              (env_acc, i+1)
            | _ -> (env_acc, i+1)
          ) (env_type_param, 0) node_dec.n_output) in
        
        (* Inputs *)
        let env_type_param = fst (List.fold_left
          (fun (env_acc, i) vd -> match vd.v_type with
            | Tclasstype (tname, tclass) ->
              (* i-th output of the node is a type parameter *)
              let ith_input = List.nth argl i in
              let env_acc = QualEnv.add tname ith_input.e_ty env_acc in
              (env_acc, i+1)
            | _ -> (env_acc, i+1)
          ) (env_type_param, 0) node_dec.n_input) in
        env_type_param
        end
      else env_type_param in
      
      let ni = mk_unique_node node_dec in
      
      let static_subst =
        List.combine (List.map (fun p -> (local_qn p.p_name)) ni.n_params)
          op.a_params in

      (* Perform [static_exp] substitution *)
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
      
      (* Perform [env_type_param] substitution *)
      let ni =
        let apply_typaram_subst_ty funs () ty = match ty with
          | Tclasstype (tname, _) -> (QualEnv.find tname env_type_param, ())
          | _ -> Global_mapfold.ty funs () ty
        in
        let funs =
          { defaults with global_funs =
            { Global_mapfold.defaults with
                 Global_mapfold.ty = apply_typaram_subst_ty; };
          } in
          fst (Hept_mapfold.node_dec funs () ni)
      in
       
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
