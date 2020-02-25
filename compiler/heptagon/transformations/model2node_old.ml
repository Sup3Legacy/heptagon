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
(* Conversion of model into node, in order to continue the compilation *)
(* Actions:
  => For all 1-synchronous clocks (ph, per), keep track of it, and create a new variable
      "varcl_NN = false fby ... fby true fby ... varcl_NN;" ( = (0^ph 1 0^{per-ph-1}) )

  => For each (phase, ratio) appearing in a 1-synchronous when/current, get a fresh variable
      (cannot be shared with others when/current expressions)

  => Transform the 1-synchronous when into a normal when
  => Transform the 1-synchronous current into a normal merge expression
  => Transform the delay/delayfby with combination of when/current
      => Right now, cannot do better without changing all the AST up to C code generation

  Assume normalization.
*)


(* Author: Guillaume I *)
open Format
open Clocks
open Types

open Heptagon
open Hept_utils
open Hept_mapfold


(* DEBUG *)
let debug_model2node = false
let ffout = formatter_of_out_channel stdout


(* Build an expression from a type *)
let rec build_dummy_stexp t = match t with
  | Tid qname ->
    let name = qname.name in
    let se_desc = match name with
      | "int" -> Sint 0
      | "real" -> Sfloat 0.0
      | "float" -> Sfloat 0.0
      | "string" -> Sstring ""
      | "bool" -> Sbool false
      | _ -> failwith ("model2node - unrecognized type " ^ name)
    in
    mk_static_exp t se_desc
  | Tarray (ty, sexpr) ->
    let st_exp_ty = build_dummy_stexp ty in
    let se_desc = Sarray_power (st_exp_ty, [sexpr]) in
    mk_static_exp t se_desc
  | Tprod lty ->
    let lst_exp = List.map build_dummy_stexp lty in
    let se_desc = Stuple lst_exp in
    mk_static_exp t se_desc
  | Tclasstype _ -> failwith "model2node : Classtype not managed."
  | Tinvalid -> failwith "model2node : Tinvalid type encountered."



  (* TODO *)

let rec gcd a b =
  assert(a>0);
  assert(b>=0);
  if (a<b) then gcd b a else
  if (b=0) then a else
  gcd b (a mod b)

(* Gather the list of 1-synchronous clocks *)
module IntIntSet = Set.Make(struct type t = int*int let compare = Pervasives.compare end)
module IntIntMap = Map.Make(struct type t = int*int let compare = Pervasives.compare end)

let var_dec_model_gather _ sacc vdm =
  let ock = vdm.vm_clock in
  let (ph,per) = Clocks.get_ph_per_from_ock ock in
  vdm, (IntIntSet.add (ph, per) sacc)

(* Main gathering function
  Returns [sacc] which is the set of all 1sync clock used in the program,
      and [saccInOut] which is the set of all 1sync clock used in the in/output.
 *)
let gather_osyncclocks md =
  let funs_gather = { Hept_mapfold.defaults with
      var_dec_model = var_dec_model_gather;
    } in
  let _, sacc = funs_gather.model_dec funs_gather IntIntSet.empty md in

  (* Assume that the clocks of inputs and outputs are always the base clock*)
  List.iter (fun vdm ->
    assert(is_base_ock vdm.vm_clock)
  ) md.m_input;
  List.iter (fun vdm ->
    assert(is_base_ock vdm.vm_clock)
  ) md.m_output;

  (* let saccInOut = List.fold_left (fun saccInOut vdm ->
    let _, saccInOut = var_dec_model_gather [] saccInOut vdm in
    saccInOut
  ) IntIntSet.empty md.m_input in
  let saccInOut = List.fold_left (fun saccInOut vdm ->
    let _, saccInOut = var_dec_model_gather [] saccInOut vdm in
    saccInOut
  ) saccInOut md.m_output in *)

  (* Removing the base clock *)
  let sacc = IntIntSet.remove (0,1) sacc in
  (* let saccInOut = IntIntSet.remove (0,1) saccInOut in *)

  sacc


(* Naming convention *)
let get_name_ock ph per = "ock_var_" ^ (string_of_int ph) ^ "_" ^ (string_of_int per)

let rec create_rhs_osync_eq res ph per = match (ph, per) with
  | (_, 0) -> res
  | (0, _) ->
    assert(per>0);
    let seTrue = mk_static_exp Initial.tbool (Sbool true) in
    let nedesc = Epre (Some seTrue, res) in
    let nres = mk_exp nedesc Initial.tbool ~linearity:Linearity.Ltop in
    create_rhs_osync_eq nres per (per-1)
  | _ ->
    assert(ph>0);
    assert(per>0);
    let seFalse = mk_static_exp Initial.tbool (Sbool false) in
    let nedesc = Epre (Some seFalse, res) in
    let nres = mk_exp nedesc Initial.tbool ~linearity:Linearity.Ltop in
    create_rhs_osync_eq nres per (per-1)

(* mock:  (ph,per) ==> (variable declaration, equation) *)
let get_osync_var_eq sock =
  let mock = IntIntSet.fold (fun (ph, per) mock ->
    (* Creating tne new local variable *)
    let name_var_ock = Idents.gen_var "model2node" (get_name_ock ph per) in
    let vd = mk_var_dec name_var_ock Initial.tbool ~linearity:Linearity.Ltop in

    (* Creating the new equation *)
    let ebase = mk_exp (Evar name_var_ock) Initial.tbool ~linearity:Linearity.Ltop in
    let erhs = create_rhs_osync_eq ebase ph per in
    let plhs = Evarpat name_var_ock in
    let eqdesc = Eeq (plhs, erhs) in
    let eq = mk_equation eqdesc in

    IntIntMap.add (ph, per) (vd, eq) mock
  ) sock IntIntMap.empty in
  mock

(* ======================================== *)

let counter_var_exp = ref 0

let get_name_var_exp ph ratio = 
  counter_var_exp := !counter_var_exp + 1;
  "var_" ^ (string_of_int !counter_var_exp) ^ "_" ^ (string_of_int ph) ^ "_" ^ (string_of_int ratio)

let get_name_var_current _ = 
  counter_var_exp := !counter_var_exp + 1;
  "var_current_" ^ (string_of_int !counter_var_exp)

let make_current_exp ph ratio seInit e1 =
  if (ratio==1) then (e1,[],[]) else

  (* We create a variable for the (ph, ratio). Cannot be the same than ock
      because the clock might not be a base one*)
  let var_id = Idents.gen_var "model2node" (get_name_var_exp ph ratio) in
  let nloc = mk_var_dec var_id Initial.tbool ~linearity:Ltop in

  let ebase = mk_exp (Evar var_id) Initial.tbool ~linearity:Linearity.Ltop in
  let rhs_eq = create_rhs_osync_eq ebase ph ratio in
  let neq = mk_simple_equation (Evarpat var_id) rhs_eq in 


  (* Current variable : varcurrent = merge var_id (True => e1) (False => seInit fby varcurrent) *)
  let var_current_id = Idents.gen_var "model2node" (get_name_var_current ()) in
  let nloc_current = mk_var_dec var_current_id e1.e_ty ~linearity:Ltop in

  let ebr_true = e1 in
  let evarbr_false = mk_exp (Evar var_current_id) e1.e_ty ~linearity:Linearity.Ltop in
  let ebr_false = mk_exp (Epre (Some seInit, evarbr_false)) e1.e_ty ~linearity:Linearity.Ltop in
  let lbranch = (Initial.ptrue, ebr_true)::(Initial.pfalse, ebr_false)::[] in

  let rhs_eq_current = mk_exp (Emerge (var_id, lbranch)) e1.e_ty ~linearity:Linearity.Ltop in
  let neq_current = mk_simple_equation (Evarpat var_current_id) rhs_eq_current in

  let nerhs = mk_exp (Evar var_current_id) e1.e_ty ~linearity:Linearity.Ltop in
  (nerhs, neq::neq_current::[], nloc::nloc_current::[])


(* We need to transform the clocks into boolean variables
 + manage the when/current associated to 1-synchronous clocks *)
let translate_equations leqs = 
  let (lneqs, nloceq) = List.fold_left (fun (acceq, accloc) eqm ->

    if debug_model2node then
      fprintf ffout "Entering equation eqm = %a\n@?" Hept_printer.print_eq_model eqm;

    (* Assume normalization *)
    let erhs = eqm.eqm_rhs in
    let eq_ock = eqm.eqm_clk in
    let (nerhs, nleq, nloc) = match erhs.e_desc with
      | Ewhenmodel (e1, (ph, ratio)) ->
        if (ratio==1) then (e1, [], []) else

        (* We create a variable for the (ph, ratio). Cannot be the same than ock
            because the clock might not be a base one*)
        let var_id = Idents.gen_var "model2node" (get_name_var_exp ph ratio) in
        let nloc = mk_var_dec var_id Initial.tbool ~linearity:Ltop in

        let nerhs = mk_exp (Ewhen (e1, Initial.ptrue, var_id)) erhs.e_ty ~linearity:Ltop in

        let ebase = mk_exp (Evar var_id) Initial.tbool ~linearity:Linearity.Ltop in
        let rhs_eq = create_rhs_osync_eq ebase ph ratio in
        let neq = mk_simple_equation (Evarpat var_id) rhs_eq in

        (nerhs, neq::[], nloc::[])
      | Ecurrentmodel ((ph, ratio), seInit, e1) ->
        make_current_exp ph ratio seInit e1
      | Edelay _ | Edelayfby _  ->
        let (p2, n) = Clocks.get_ph_per_from_ock eq_ock in

        let (d, e1, seInit) = match erhs.e_desc with
          | Edelay (d, e1) -> (d, e1, build_dummy_stexp e1.e_ty)
          | Edelayfby (d, seInit, e1) -> (d, e1, seInit)
          | _ -> failwith "Impossible matching"
        in

        (* We translate this delay into a combination of when and current *)
        (* Common clock: (q,m) s.t. m = gcd(d,n) and q = p_2 mod m, where clock(eq) = (p2, n) *)
        let p1 = p2 - d in

        (* TODO DEBUG *)
        if debug_model2node then
          fprintf ffout "p1 = %i | p2 = %i | n = %i | d = %i\n@?" p1 p2 n d;

        assert(p1>=0);
        let m = gcd d n in
        let q = p2 mod m in

        (* delay(d) e1 ===> (current( (a,r) , eDummy, eInit) ) when (b,r) *)
        (*    where a = (p1-q)/m and b = (p2-q) / m *)
        let r = n / m in
        let a = (p1-q) / m in
        let b = (p2-q) / m in

        (* Building the equations *)
        let (ecurrent, leqcurrent, lloccurrent) = make_current_exp a r seInit e1 in

        let var_id_when = Idents.gen_var "model2node" (get_name_var_exp b r) in
        let nloc_when = mk_var_dec var_id_when Initial.tbool ~linearity:Ltop in

        let nerhs = mk_exp (Ewhen (ecurrent, Initial.ptrue, var_id_when)) e1.e_ty ~linearity:Ltop in

        let ebase = mk_exp (Evar var_id_when) Initial.tbool ~linearity:Linearity.Ltop in
        let rhs_eq = create_rhs_osync_eq ebase b r in
        let eqwhen = mk_simple_equation (Evarpat var_id_when) rhs_eq in

        (nerhs, eqwhen::leqcurrent@[], nloc_when::lloccurrent@[])
      (* Default case: no need to do anything *)
      | _ -> (erhs, [], [])
    in

    let neq = mk_simple_equation eqm.eqm_lhs nerhs in
    let nacceq = neq :: (List.rev_append nleq acceq) in
    let naccloc = List.rev_append nloc accloc in
    
    (nacceq, naccloc)
  ) ([],[]) leqs in
  (lneqs, nloceq)



(* ======================================== *)

(* Conversion from model variable declaration to node variable declaration
    But only for input and output (for which the clock is always "Cbase") *)
let vdm_2_vd_inout vdm =
  mk_var_dec ~clock:Clocks.Cbase vdm.vm_ident
    vdm.vm_type ~linearity:Linearity.Ltop

let vdm_2_vd_local mock_loc_eq vdm =
  let ock = vdm.vm_clock in
  let (ph, per) = Clocks.get_ph_per_from_ock ock in
  let ck = if ((ph==1) && (per==1)) then
      Cbase
    else
      let (vd,_) = IntIntMap.find (ph, per) mock_loc_eq in
      Con (Cbase, Initial.ptrue, vd.v_ident)
  in
  mk_var_dec ~clock:ck vdm.vm_ident vdm.vm_type ~linearity:Linearity.Ltop

let model2node md =
  (* Step 1 - Management of 1-synchronous clocks *)
  let sock = gather_osyncclocks md in
  let mock_loc_eq = get_osync_var_eq sock in

  let nlocals = List.map (vdm_2_vd_local mock_loc_eq) md.m_block.bm_local in
  (* TODO: old locals: associate the old vardecl to the new one *)
  
  let (loc_ock, eq_ock) = IntIntMap.fold
    (fun _ (vd,eq) (accvd, acceq) -> (vd::accvd, eq::acceq))
    mock_loc_eq ([],[])
  in
  let nlocals = List.rev_append nlocals loc_ock in

  (* Step 2 - Management of the 1-synchronous temporal expressions *)
  let (lneqs, nloceq) = translate_equations md.m_block.bm_eqs in

  (* Final Step - Build and return the new node *)
  let nlocals = List.rev_append nlocals nloceq in
  let lneqs = List.rev_append lneqs eq_ock in

  let n_block = mk_block ~locals:nlocals lneqs in
  
  let ninputs = List.map vdm_2_vd_inout md.m_input in
  let noutputs = List.map vdm_2_vd_inout md.m_output in

  let n_nd = mk_node ~input:ninputs ~output:noutputs ~unsafe:true ~loc:md.m_loc
    md.m_name n_block in
  
  (* Normalization of the node *)
  let n_nd = Normalize.node_dec n_nd in
  n_nd


let program p =
  let program_desc pd = match pd with
    | Pmodel md -> Pnode (model2node md)
    | _ -> pd
  in
  { p with p_desc = List.map program_desc p.p_desc; }
