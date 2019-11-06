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
open Pp_tools
open Clocks
open Types
open Linearity

open Heptagon
open Hept_utils
open Hept_mapfold


(* DEBUG *)
let debug_model2node = false
let ffout = formatter_of_out_channel stdout

(* Pretty printer for the graph of periods*)
let print_gr_per ff gr =
  let print_couple_int ff (src,dst) =
    fprintf ff "(%i, %i)" src dst
  in
  fprintf ff "%a" (print_list print_couple_int "[[""; ""]]") gr


(* Build an expression from a type *)
let rec build_dummy_stexp t = match t with
  | Tid qname ->
    let name = qname.Names.name in
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



(* ======================================== *)
(* Old implementation of model2node *)

let rec gcd a b =
  assert(a>0);
  assert(b>=0);
  if (a<b) then gcd b a else
  if (b=0) then a else
  gcd b (a mod b)

(* Gather the list of 1-synchronous clocks *)
module IntIntSet = Set.Make(struct type t = int*int let compare = Pervasives.compare end)
module IntIntMap = Map.Make(struct type t = int*int let compare = Pervasives.compare end)


(* Main gathering function
  Returns [sacc] which is the set of all 1sync clock used in the program,
      and [saccInOut] which is the set of all 1sync clock used in the in/output.
 *)
let gather_osyncclocks md =
  let var_dec_model_gather _ sacc vdm =
    let ock = vdm.vm_clock in
    let (ph,per) = Clocks.get_ph_per_from_ock ock in
    vdm, (IntIntSet.add (ph, per) sacc)
  in
  let funs_gather = { Hept_mapfold.defaults with var_dec_model = var_dec_model_gather } in
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
    
    let res = create_rhs_osync_eq res per (per-1) in
    let nedesc = Epre (Some seTrue, res) in
    let nres = mk_exp nedesc Initial.tbool ~linearity:Linearity.Ltop in
    nres
    
  | _ ->
    assert(ph>0);
    assert(per>0);
    let seFalse = mk_static_exp Initial.tbool (Sbool false) in

    let res = create_rhs_osync_eq res (ph-1) (per-1) in
    let nedesc = Epre (Some seFalse, res) in
    let nres = mk_exp nedesc Initial.tbool ~linearity:Linearity.Ltop in
    nres
    

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

(* ======================================== *)




(* Re-implementation with locals *)

let rec get_father lgr elem = match lgr with
  | [] -> raise Not_found
  | (e1,e2)::r ->
    if (e2=elem) then e1 else get_father r elem


let rec add_to_graph lgr (p1, p2) = match lgr with
  | [] -> (p1,p2)::[]
  | (h1,h2)::r ->
    if (h2=p2) then lgr else (* If destination period already there, don't do anything *)
    (h1,h2)::(add_to_graph r (p1,p2))

(* Add the connexion from period 1 to periods with no father in the graph *)
let connect_to_one lgr =
  let lperiod : int list = List.fold_left (fun acc (e1,e2) ->
      e1::e2::acc
    ) [] lgr
  in
  let lperiod = List.sort_uniq Pervasives.compare lperiod in
  List.fold_left (fun accgr per ->
    if (per=1) then accgr else
    add_to_graph accgr (1, per)
  ) lgr lperiod
  (* let lconnected :int list = List.map (fun (_,src) -> src) lgr in
  let gr = List.fold_left (fun gracc per -> 
    (* If the period have an ancestor *)
    if (List.exists (fun pconn -> pconn=per) lconnected) then
      gracc
    else
      if (per=1) then gracc else
      (1, per)::gracc
  ) gr lperiod in
  gr *)

(* Some heuristics to make the graph of period better *)
let rectify_grper lgr =
  (* Heursitic: (a,b) and (a,c) where (c mod b = 0) ==> (a,b) and (b,c) *)
  let lsrc = List.map (fun (s,_) -> s) lgr in
  let lsrc = List.sort_uniq Pervasives.compare lsrc in

  let lngr = List.fold_left (fun lacc src ->
    let ledges = List.filter (fun (s,_) -> s=src) lgr in
    assert((List.length ledges)>0);

    (* Find the right configuration *)
    if ((List.tl ledges) = []) then ledges@lacc else

    let lconfig = List.fold_left (fun acc (_,d1) ->
      List.fold_left (fun acc (_,d2) ->
        if (d1=d2) then acc else
        if ((d1 mod d2) = 0) then  (* d2 divides d1 *)
          (d1, d2)::acc
        else acc
      ) acc ledges
    ) [] ledges in

    (* DEBUG
    fprintf ffout "lconfig = %a\n@?" print_gr_per lconfig; *)

    (* For each (d1,d2) in lconfig, replace the edge (s,d1) by (d2,d1) *)
    let lnedges:(int * int) list = List.map (fun (src,dst) ->
      try 
        let (d1,d2) = List.find (fun (d1,_) -> d1=dst) lconfig in
        (d2, d1)
      with Not_found -> (src,dst)
    ) ledges in
    lnedges@lacc
  ) [] lsrc in
  lngr


(* Build the graph of periods, which is a list of (src, dst) = (int * int) list *)
let build_period_graph md =
  (* For all when/current expression from p to p', build the corresponding edge in the graph *)
  let edesc_per_gr funs (gr, pereq) ed = match ed with
    | Ewhenmodel (_, (_, ratio)) ->
      assert(pereq mod ratio = 0);
      let per2 = pereq / ratio in
      let _, (gr,_) = Hept_mapfold.edesc funs (gr, per2) ed in

      (* Add (per2, pereq) in the graph *)
      let gr = add_to_graph gr (per2, pereq) in
      ed, (gr, pereq)

    | Ecurrentmodel ((_, ratio), _, _) ->
      let per1 = pereq * ratio in
      let _, (gr,_) = Hept_mapfold.edesc funs (gr, per1) ed in

      (* Add (pereq, per1) in the graph *)
      let gr = add_to_graph gr (pereq, per1) in
      ed, (gr, pereq)

    | _ -> Hept_mapfold.edesc funs (gr, pereq) ed 
  in
  let eqm_per_gr funs (gr,_) eqm =
    let per = Clocks.get_period_ock eqm.eqm_clk in
    Hept_mapfold.eq_model funs (gr, per) eqm
  in
  
  let funs_per_gr = { Hept_mapfold.defaults with edesc = edesc_per_gr; eq_model = eqm_per_gr } in
  let _, (gracc, _) = funs_per_gr.model_dec funs_per_gr ([],0) md in

  (* TODO DEBUG *)
  if debug_model2node then (
    fprintf ffout "gracc = %a\n@?" print_gr_per gracc;
  );

  (* Add link to 1 from roots of the graph *)
  let gracc = connect_to_one gracc in

  (* Finish by adding the periods of the variables decl to gr, if not already there *)
  let vdm_per _ gr vdm =
    let per = Clocks.get_period_ock vdm.vm_clock in
    if (per==1) then vdm, gr else
    vdm, add_to_graph gr (1, per)  (* Add to the graph only if there is no connection to it already *)
  in
  let funs_per_vdm = { Hept_mapfold.defaults with var_dec_model = vdm_per } in
  let _, gracc = funs_per_vdm.model_dec funs_per_vdm gracc md in

  let gracc = rectify_grper gracc in
  gracc


(* --- *)

(* Localisation of a ock into a succession of "on" which fits the graph of periods *)
let rec localising_ock lgr ock =
  let (ph, per) = Clocks.get_ph_per_from_ock ock in

  (* DEBUG
  fprintf ffout "localising_ock :: ph = %i | per = %i\n@?" ph per; *)

  (* Base case *)
  if (per=1) then (
    assert(ph=0);
    []
  ) else

  (* We get the father of per in lgr *)
  let per2 = get_father lgr per in
  let ratio = per / per2 in

  (* We need to find ph2 and k such that ph2 = ph - per2 * k *)
  (*  aka [ph2, per2] on [k,ratio] = [ph, per] <===> ph = per2*k + ph2 and per = ratio * per2 *)
  let ph2 = ph mod per2 in
  let k = (ph-ph2)/per2 in
  (* DEBUG
  fprintf ffout "\nlocalising_ock :: ph = %i | ratio = %i\n@?" ph ratio;
  fprintf ffout "localising_ock :: ph2 = %i | per2 = %i\n@?" ph2 per2; *)
  assert(0<=k);
  assert(k<ratio);

  (k, ratio) :: (localising_ock lgr (Cone (ph2, per2)))

(* Localisation of a ock1->ock2 (cf when/current) into a
    succession of "on" which fits the graph of periods *)
let localising_ock_connection lgr ock1 ock2 =
  (* We compare the start of the chain of "on" of ock1 and ock2 *)
  let lonock1 = localising_ock lgr ock1 in
  let lonock2 = localising_ock lgr ock2 in

  (* DEBUG
  fprintf ffout "localising_ock_connection::lonock1 = %a\n@?" print_gr_per lonock1;
  fprintf ffout "localising_ock_connection::lonock2 = %a\n@?" print_gr_per lonock2; *)

  let rec compare_on_chain common lonock1 lonock2 = match (lonock1, lonock2) with
  | ([],_) | (_,[]) -> (common, lonock1, lonock2)
  | ((k1,r1)::ronock1),((k2,r2)::ronock2) ->
    if ((k1=k2) && (r1=r2)) then
      compare_on_chain (common@[(k1,r1)]) ronock1 ronock2
    else
      (common, lonock1, lonock2)
  in
  let rev_lonock1 = List.rev lonock1 in
  let rev_lonock2 = List.rev lonock2 in

  let (common_ock, rev_lon_rest_ock1, rev_lon_rest_ock2) = compare_on_chain [] rev_lonock1 rev_lonock2 in
  let lon_rest_ock1 = List.rev rev_lon_rest_ock1 in
  let lon_rest_ock2 = List.rev rev_lon_rest_ock2 in
  (common_ock, lon_rest_ock1, lon_rest_ock2)

let rec build_chain_when eBase lchain = match lchain with
  | [] -> eBase
  | (k,ratio)::rest ->
    let edesc = Ewhenmodel (eBase, (k, ratio)) in
    let exp = Hept_utils.mk_exp edesc eBase.e_ty ~linearity:Linearity.Ltop in
    build_chain_when exp rest

let rec build_chain_current seInit eBase lchain = match lchain with
  | [] -> eBase
  | (k, ratio)::rest ->
    let eBase = build_chain_current seInit eBase rest in
    let edesc = Ecurrentmodel ((k, ratio), seInit, eBase) in
    let exp = Hept_utils.mk_exp edesc eBase.e_ty ~linearity:Linearity.Ltop in
    exp


(* Localise the when/current/delay/delayfby to make them fit the graph of periods *)
let localise_equations lgr md =
  let eqm_loc_eq _ _ eqm =
    if debug_model2node then
      fprintf ffout "Entering equation eqm : %a\n@?" Hept_printer.print_eq_model eqm;

    (* Assume normalization *)
    let erhs = eqm.eqm_rhs in
    let eq_ock = eqm.eqm_clk in

    let nerhs = match erhs.e_desc with
      | Ewhenmodel (e1, (_, ratio)) ->
        if (ratio==1) then e1 else

        let (ph_eq, per_eq) = Clocks.get_ph_per_from_ock eq_ock in
        assert(per_eq mod ratio = 0);
        
        (* ph_eq = ph_sexp + k * ratio *)
        let per_sexp = per_eq / ratio in
        let ph_sexp = ph_eq mod per_sexp in
        let sexpr_ock = Cone (ph_sexp, per_sexp) in

        let (_, lrev_r_sexpr, lrev_r_eq) = localising_ock_connection lgr sexpr_ock eq_ock in
        let lr_sexpr = List.rev lrev_r_sexpr in
        let lr_eq = List.rev lrev_r_eq in

        (* DEBUG
        fprintf ffout "sexpr_ock = %a\n@?" Global_printer.print_oneck sexpr_ock;
        fprintf ffout "eq_ock = %a\n@?" Global_printer.print_oneck eq_ock;
        fprintf ffout "common = %a\n@?" print_gr_per common;
        fprintf ffout "lr_sexpr = %a\n@?" print_gr_per lr_sexpr;
        fprintf ffout "lr_eq = %a\n@?" print_gr_per lr_eq; *)

        (* Build the chain of current/when which should replace the current when *)
        let seInit = build_dummy_stexp e1.e_ty in
        let ecurrent = build_chain_current seInit e1 lr_sexpr in
        let ewhen = build_chain_when ecurrent lr_eq in
        ewhen

      | Ecurrentmodel ((k, ratio), seInit, e1) ->
        if (ratio==1) then e1 else

        let (ph_eq, per_eq) = Clocks.get_ph_per_from_ock eq_ock in

        (* ph_sexp = ph_eq + k * ratio *)
        let per_sexp = per_eq * ratio in
        let ph_sexp = ph_eq + k * per_eq in
        let sexpr_ock = Cone (ph_sexp, per_sexp) in

        let (_, lrev_r_sexpr, lrev_r_eq) = localising_ock_connection lgr sexpr_ock eq_ock in
        let lr_sexpr = List.rev lrev_r_sexpr in
        let lr_eq = List.rev lrev_r_eq in

        let ecurrent = build_chain_current seInit e1 lr_sexpr in
        let ewhen = build_chain_when ecurrent lr_eq in
        ewhen

      | Edelay (d,e1)  ->
        let (ph_eq, per_eq) = Clocks.get_ph_per_from_ock eq_ock in
        let ph_sexp = ph_eq - d in
        assert(ph_sexp>=0);
        let sexpr_ock = Cone (ph_sexp, per_eq) in

        let (_, lrev_r_sexpr, lrev_r_eq) = localising_ock_connection lgr sexpr_ock eq_ock in
        let lr_sexpr = List.rev lrev_r_sexpr in
        let lr_eq = List.rev lrev_r_eq in
        
        (* Build the chain of current/when which should replace the current when *)
        let seInit = build_dummy_stexp e1.e_ty in
        let ecurrent = build_chain_current seInit e1 lr_sexpr in
        let ewhen = build_chain_when ecurrent lr_eq in
        ewhen

      | Edelayfby (d, seInit, e1) ->
        let (ph_eq, per_eq) = Clocks.get_ph_per_from_ock eq_ock in
        let ph_sexp = ph_eq - d + per_eq in
        assert(ph_sexp>=0);
        assert(ph_sexp<per_eq);
        let sexpr_ock = Cone (ph_sexp, per_eq) in

        let (_, lrev_r_sexpr, lrev_r_eq) = localising_ock_connection lgr sexpr_ock eq_ock in
        let lr_sexpr = List.rev lrev_r_sexpr in
        let lr_eq = List.rev lrev_r_eq in
        
        (* Build the chain of current/when which should replace the current when *)
        let ecurrent = build_chain_current seInit e1 lr_sexpr in
        let ewhen = build_chain_when ecurrent lr_eq in
        ewhen

      (* Default case: no need to do anything *)
      | _ -> erhs
    in
    { eqm with eqm_rhs = nerhs }, []
  in

  let funs_loc_eq = { Hept_mapfold.defaults with eq_model = eqm_loc_eq } in
  let n_mbl, _ = funs_loc_eq.block_model funs_loc_eq [] md.m_block in
  { md with m_block = n_mbl }


(* --- *)

(* (k, ratio, ph, per)  <===> (k, ratio) on (ph, per)  / associate with the actual id *)
module Int4Map = Map.Make(struct type t = int*int*int*int let compare = Pervasives.compare end)

let get_name_clock_id k ratio ph per = 
  "var_" ^ (string_of_int k) ^ "_" ^ (string_of_int ratio)
    ^ "_on_" ^ (string_of_int ph) ^ "_" ^ (string_of_int per)

let add_new_clock_id mvarOck k ratio ph per =
  assert(0<=ph);
  assert(ph<per);
  assert(0<=k);
  assert(k<ratio);
  try
    let varid = Int4Map.find (k, ratio, ph, per) mvarOck in
    (varid, mvarOck)
  with Not_found ->
    (* Create the new one and add it to mvarOck *)
    let namevar = get_name_clock_id k ratio ph per in
    let varid = Idents.gen_var "model2node" namevar in

    let mvarOck = Int4Map.add (k, ratio, ph, per) varid mvarOck in
    (varid, mvarOck)

let rec period_phase_from_chain lchain = match lchain with
  | [] -> (0,1)
  | (k, ratio)::rest ->
    let (ph,per) = period_phase_from_chain rest in
    (ph + k*per, per*ratio)

let rec get_clock_from_chain mvarOck lchainon = match lchainon with
  | [] -> (Cbase, mvarOck)
  | (k,ratio)::rest ->
    let (ckrest, mvarOck) = get_clock_from_chain mvarOck rest in

    let (phbase, perbase) = period_phase_from_chain rest in
    let (var_id, mvarOck) = add_new_clock_id mvarOck k ratio phbase perbase in
    Con (ckrest, Initial.ptrue, var_id), mvarOck

let transform_to_node_dec lgr md =
  let mvarOck = Int4Map.empty in

  (* Expression transformation and equation translation (to standard eq) *)
  let mbl = md.m_block in
  let (leqs, lvdcurrent, mvarOck) = List.fold_left (fun (acceq, accvd, mvarOck) eqm ->
    if debug_model2node then
      fprintf ffout "Entering equation eqm : %a\n@?" Hept_printer.print_eq_model eqm;

    let erhs = eqm.eqm_rhs in
    let (nerhs, lneq, lnvd, mvarOck) = match erhs.e_desc with
      | Ewhenmodel (e1, (k, ratio)) ->
        let (ph, per) = Clocks.get_ph_per_from_ock eqm.eqm_clk in
        let per_sexp = per / ratio in
        let ph_sexp = ph mod per_sexp in

        let (var_id, mvarOck) = add_new_clock_id mvarOck k ratio ph_sexp per_sexp in

        let nerhs = mk_exp (Ewhen (e1, Initial.ptrue, var_id)) erhs.e_ty ~linearity:Ltop in
        (nerhs, [], [], mvarOck)
      | Ecurrentmodel ((k, ratio), seInit, e1) ->
        let (ph, per) = Clocks.get_ph_per_from_ock eqm.eqm_clk in
        let per_sexp = per * ratio in
        let ph_sexp = ph + k * per in

        let (var_id, mvarOck) = add_new_clock_id mvarOck k ratio ph per in

        (* Fabrication du current *)
        (* Current variable : varcurrent = merge var_id (True => e1) (False => seInit fby varcurrent) *)
        let var_current_id = Idents.gen_var "model2node" (get_name_var_current ()) in
        let nloc_current = mk_var_dec var_current_id e1.e_ty ~linearity:Ltop in

        let ebr_true = e1 in
        let evarbr_false = mk_exp (Evar var_current_id) e1.e_ty ~linearity:Linearity.Ltop in
        let ebr_false = mk_exp (Epre (Some seInit, evarbr_false)) e1.e_ty ~linearity:Linearity.Ltop in

        let ebr_false_whenot = mk_exp (Ewhen (ebr_false, Initial.pfalse, var_id)) e1.e_ty ~linearity:Linearity.Ltop in
        let lbranch = (Initial.ptrue, ebr_true)::(Initial.pfalse, ebr_false_whenot)::[] in

        let rhs_eq_current = mk_exp (Emerge (var_id, lbranch)) e1.e_ty ~linearity:Linearity.Ltop in
        let neq_current = mk_simple_equation (Evarpat var_current_id) rhs_eq_current in

        let nerhs = mk_exp (Evar var_current_id) e1.e_ty ~linearity:Linearity.Ltop in
        (nerhs, neq_current::[], nloc_current::[], mvarOck)

        (* TODO - remark: we can avoid building the neq_current/nloc_current by reusing the lhs of the equation *)

      | Edelay _ | Edelayfby _ ->
        failwith "delay/delayfby should have been translated to when/current"
      | _ -> (erhs, [], [], mvarOck)
    in
    let neq = mk_simple_equation eqm.eqm_lhs nerhs in
    (neq::(List.rev_append lneq acceq),
      List.rev_append lnvd accvd,
      mvarOck)
  ) ([], [], mvarOck) mbl.bm_eqs in

  (* Variable declaration translation *)
  let (lvdloc_orig, mvarOck) = List.fold_left (fun (accvd, mvarOck) vdm -> 
    let ock = vdm.vm_clock in
    let lchainon = localising_ock lgr ock in
    let (ck, mvarOck) = get_clock_from_chain mvarOck lchainon in

    let vd = mk_var_dec ~clock:ck vdm.vm_ident vdm.vm_type ~linearity:Linearity.Ltop in
    (vd::accvd, mvarOck)
  ) ([], mvarOck) mbl.bm_local in


  (* Getting the equation and variable declaration of the boolean var expressing the clocks *)
  let (lvarock, leqock) = Int4Map.fold (fun (k, ratio, _, _) var_id (accvd, acceq) ->
    let nvd = mk_var_dec var_id Initial.tbool ~linearity:Ltop in

    let ebase = mk_exp (Evar var_id) Initial.tbool ~linearity:Linearity.Ltop in
    let rhs_eq = create_rhs_osync_eq ebase k ratio in
    let neq = mk_simple_equation (Evarpat var_id) rhs_eq in

    (* DEBUG
    if debug_model2node then
      fprintf ffout "neq (k = %i, ratio = %i) = %a\n@?"
        k ratio  Hept_printer.print_eq neq; *)

    (nvd::accvd, neq::acceq)
  ) mvarOck ([], []) in


  (* Wrapping things up *)
  let llocals = (List.rev_append lvdcurrent (List.rev_append lvarock lvdloc_orig)) in
  let leqs = List.rev_append leqock leqs in

  let bl = Hept_utils.mk_block ~locals:llocals leqs in 

  let linputs = List.map vdm_2_vd_inout md.m_input in
  let loutputs = List.map vdm_2_vd_inout md.m_output in
  let nd = Hept_utils.mk_node ~input:linputs ~output:loutputs md.m_name bl in
  nd



(* ======================================== *)

let model2node md =
  (* Step 1 - build the graph of harmonic periods *)
  let lgr_harm_per : (int * int) list = build_period_graph md in

  if debug_model2node then (
    fprintf ffout "model2node : Period graph built.\n@?";
    fprintf ffout "lgr_harm_per = %a\n@?" print_gr_per lgr_harm_per;
  );

  (* Step 2 - go over all when/current/delay in eq_model
    and convert them into smalled when/current/delay *)
  let localised_md = localise_equations lgr_harm_per md in
  
  if debug_model2node then (
    fprintf ffout "model2node : Equations localised.\n@?";
    fprintf ffout "localised_md = %a\n@?" Hept_printer.print_model localised_md;
  );

  let localised_md = Normalize.model_dec localised_md in


  if debug_model2node then (
    fprintf ffout "model2node : Equations normalized.\n@?";
    fprintf ffout "localised_md = %a\n@?" Hept_printer.print_model localised_md;
  );

  (* There should not be any buffer this time => simpler clocking analysis *)
  let localised_md = Model_clocking.typing_model true localised_md in

  (* At that point, there is no delay/delayfby, and the only when remaining
    are along the edges of the graph of harmonic periods *)

  if debug_model2node then (
    fprintf ffout "model2node : Equations normalized and clocked.\n@?";
    fprintf ffout "localised_md = %a\n@?" Hept_printer.print_model localised_md;
  );

  (* Step 3 - gather the list of local variables (IntIntIntIntMap)
    and replace the whenmodel/currentmodel by classical when/current *)
  let n_nd = transform_to_node_dec lgr_harm_per localised_md in

  (* Normalization of the node *)
  let n_nd = Normalize.node_dec n_nd in
  n_nd


let program p =
  let program_desc pd = match pd with
    | Pmodel md -> Pnode (model2node md)
    | _ -> pd
  in
  { p with p_desc = List.map program_desc p.p_desc; }
