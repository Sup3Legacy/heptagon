(***********************************************************************)
(*                                                                     *)
(*                             Heptagon                                *)
(*                                                                     *)
(* Gwenael Delaval, LIG/INRIA, UJF                                     *)
(* Leonard Gerard, Parkas, ENS                                         *)
(* Adrien Guatto, Parkas, ENS                                          *)
(* Cedric Pasteur, Parkas, ENS                                         *)
(* Marc Pouzet, Parkas, ENS                                            *)
(* Nicolas Berthier, SUMO, INRIA                                       *)
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

(* Preprocess pass before Lopht CG, in relation to OpenCL kernels *)

(* Author: Guillaume I *)
open Idents
open Names
open Minils
open Mls_utils


(* For debugging *)
let debug = true   (* TODO DEBUG *)
let ffout = Format.formatter_of_out_channel stdout


let print_lvarid ff lvarid =
  Format.fprintf ff "@[<2>%a@]" (Pp_tools.print_list_r Idents.print_ident "[""; ""]") lvarid


(* Detection step of troublesome communication *)
let detect_kernel_to_kernel_comm n =
  (* Step 1 : mark vid which are the output of equations using kernel call *)
  let svid_from_kernel = List.fold_left (fun sacc eq -> match eq.eq_rhs.e_desc with
    | Eapp (ap, _, _) -> begin match ap.a_op with
      | Efun fn | Enode fn -> (
        if (Modules.check_kernel fn) then
          let (lvid_lhs : var_ident list) = Mls_utils.ident_list_of_pat eq.eq_lhs in
          List.fold_left (fun (sacc: IdentSet.t) (vid:var_ident) ->
            IdentSet.add vid sacc
          ) sacc lvid_lhs
        else
          sacc
      )
      | _ -> sacc
    end
    | _ -> sacc
  ) IdentSet.empty n.n_equs in

  (* Step 2 : check if these vid are directly used as the input of another kernel call *)
  let lvid_direct_kernel_comm = List.fold_left (fun lvid_acc eq -> match eq.eq_rhs.e_desc with
    | Eapp (ap, leval, _) -> begin match ap.a_op with
      | Efun fn | Enode fn -> (
        if (Modules.check_kernel fn) then (
          (* Get list of vid used by the kernel call *)
          let lvid_used = List.fold_left (fun lvid_used_acc eval ->
            let ovid=  ident_of_extvalue eval in
            match ovid with
              | None -> lvid_used_acc
              | Some vid -> vid::lvid_used_acc
          ) [] leval in
          
          (* Check the presence of the element of lvid_used in the set svid_from_kernel *)
          List.fold_left (fun lvid_acc vid_used ->
            if (IdentSet.mem vid_used svid_from_kernel) then
              vid_used::lvid_acc
            else
              lvid_acc
          ) lvid_acc lvid_used
        ) else
          lvid_acc
      )
      | _ -> lvid_acc
    end
    | _ -> lvid_acc
  ) [] n.n_equs in

  lvid_direct_kernel_comm

(* Naming convention for copy variables*)
let get_copy_vid_name vid =
  let str_copy_name = "copy_" ^ (Idents.name vid) in
  Idents.gen_var "Preprocess_Lopht" str_copy_name

(* Substitute a variable id into a new variable id in a pattern *)
let rec subst_vid_pat old_vid new_vid pat = match pat with
  | Evarpat vid -> if (vid=old_vid) then (Evarpat new_vid) else pat
  | Etuplepat lpat -> Etuplepat (List.map (subst_vid_pat old_vid new_vid) lpat)

(* Naming convention for copy function name *)
let dummy_copy_funname = {qual = Pervasives; name = "_dummy_copy"}

(* Transformation step : we add a dummy copy equation *)
let add_dummy_copy_fun_equation n vid =
  (* Get the variable declaration of vid *)
  let vd = try 
      Mls_utils.vd_find vid n.n_local
    with Not_found -> failwith ("Variable " ^ (Idents.name vid) ^ " was not found in local variables.")
  in

  (* Create the new variable declaration *)
  let nvid = get_copy_vid_name vid in
  let nvd = Minils.mk_var_dec nvid vd.v_type vd.v_linearity vd.v_clock in

  (* Kernel equation now produce this new variable *)
  let (leq_updated, o_old_eq) = List.fold_left (fun (leq_acc, oeq) eq ->
    let lvid_lhs = Mls_utils.ident_list_of_pat eq.eq_lhs in
    if (List.mem vid lvid_lhs) then (
      assert(oeq=None);
      let nplhs = subst_vid_pat vid nvid eq.eq_lhs in
      let neq = { eq with eq_lhs = nplhs } in
      neq::leq_acc, (Some eq)
      (* Note : could interrupt recursion there - vid only defined once *)
    ) else
      eq::leq_acc, oeq
  ) ([], None) n.n_equs in
  
  (* Retrieve the old equation defining vid *)
  let old_eq = match o_old_eq with
    | None -> failwith ("Preprocess_lopht: Old equation for " ^ (Idents.name vid) ^ "was not found.")
    | Some eq -> eq
  in

  (* Create the new equation (dummy copy funcall) to define vid from nvid *)
  let op_dummy_copy = Efun dummy_copy_funname in
  let app_neq = Minils.mk_app op_dummy_copy in

  let eval_nvid = mk_extvalue ~ty:vd.v_type ~linearity:vd.v_linearity (Wvar nvid) in
  let larg = [eval_nvid] in

  let edesc_neq = Eapp (app_neq, larg, None) in

  let exp_neq = Minils.mk_exp old_eq.eq_base_ck vd.v_type ~linearity:vd.v_linearity edesc_neq in
  let pat_neq = Evarpat vid in
  let neq = Minils.mk_equation false pat_neq exp_neq in


  (* Return the final data struct *)
  let nlloc = nvd::n.n_local in
  let nleqs = neq :: leq_updated in
  { n with n_local = nlloc; n_equs = nleqs }


(* ============================================= *)


let main_node n = 
  (* We forbid direct communication between 2 kernels *)
  (*  => If we detect such case, we need to introduce a new temporary variable to
    insert a copy in the middle (with a specific function call "copy",
    so that Lopht takes it into account) + correct other equations *)

  (* NOTE: only FUNCTIONs are scheduled and appear in the return scheduling table !!! *)

  (* Step 1 : detection *)
  let lvarid = detect_kernel_to_kernel_comm n in

  (* DEBUG *)
  if (debug) then
    Format.fprintf ffout "detect_kernel_to_kernel_comm done.\n\tlvarid = %a\n@?"
      print_lvarid lvarid;

  (* Step 2 : transformation (add dummy copy funcall equation on vid) *)
  let n = List.fold_left (fun nacc vid ->
    add_dummy_copy_fun_equation nacc vid
  ) n lvarid in

  n

let program p =
  if ((List.length !Compiler_options.mainnode)!=1) then
    Format.fprintf ffout "Error: list of mainnodes (option -mainnode) must contain exactly one node\n@?";
  let main_node_name = Misc.assert_1 !Compiler_options.mainnode in

  (* We trigger the transformation only on the main node *)
  let nlpdesc = List.map (fun pd -> match pd with
    | Pnode nd ->
      if (nd.n_name.name = main_node_name.name) then
        Pnode (main_node nd)
      else
        Pnode nd
    | _ -> pd
  ) p.p_desc in
  { p with p_desc = nlpdesc }
