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
(* Full 1-synchronous clocking analysis for model *)

(* Assumption: program is normalized (previous compilation pass) *)
(* We need to keep track of the clocks (needed if we want to get the constraints on the phases) *)
(* 	=> We use exp.e_ct_annot to keep track of these (which is a mutable field) *)

(* Author: Guillaume I *)

open Names
open Idents
open Containers

open Heptagon
open Hept_utils
open Hept_mapfold
open Global_printer
open Signature
open Clocks
open Location
open Format

open Affine_constraint_clocking


let debug_clocking = false (* DEBUG *)
let ffout = formatter_of_out_channel stdout

let print_henv ff h =
  Env.iter (fun k v ->
    fprintf ff "\t%a => %a\n@?"  print_ident k  print_oneck v
  ) h

let print_lsubst ff (lsubst : (int * int option * int * (int*int) list) list) =
  let print_subst ff (id1, oid2, sh, laffterm) =
  let laffterm = List.map (fun (c,v) -> (c, varname_from_phase_index v)) laffterm in
  match oid2 with
    | None -> fprintf ff "(%i => None, %a, %i)"
                id1 (Affine_constraint_clocking.print_affterm ~bfirst:true) laffterm sh
    | Some id2 -> fprintf ff "(%i => %i, %a, %i)"
                    id1 id2 (Affine_constraint_clocking.print_affterm ~bfirst:true) laffterm sh
  in
  fprintf ff "%a\n@?" (Pp_tools.print_list print_subst "[" "; " "]") lsubst

(* Print out the substitution mapping between phase variables *)
let print_msubst ff msubst =
  StringMap.iter (fun id1 (oid2, sh, laffterm) -> match oid2 with
    | None -> fprintf ff "\t(%s => None, %a, %i)\n"
                id1 (Affine_constraint_clocking.print_affterm ~bfirst:true) laffterm sh
    | Some id2 -> fprintf ff "\t(%s => %s, %a, %i)\n"
              id1 id2 (Affine_constraint_clocking.print_affterm ~bfirst:true) laffterm sh
  ) msubst

(* Print out the decision variables *)
let print_mdecvar ff mdecvar =
  fprintf ff "mdecvar=\n@?";
  Env.iter (fun varid1 varph_name -> 
    fprintf ff "\t(%s => %s)\n@?" (Idents.name varid1) varph_name
  ) mdecvar


type error_kind =
  | Etypeclash of onect * onect

let error_message loc = function
  | Etypeclash (actual_ct, expected_ct) ->
      Format.eprintf "%aClock Clash: this expression has clock %a, but is expected to have clock %a.@."
        print_location loc
        print_onect actual_ct
        print_onect expected_ct;
      raise Errors.Error

let assert_Evar e = match e.e_desc with
  | Evar varid -> varid
  | _ ->
    Format.eprintf "Error: expression (%a) is expected to be a variable.\n@?"
      Hept_printer.print_exp e;
    failwith "Internal error - expression should be a variable"


(* ==================================== *)
(* Core clocking modification *)

let apply_shift_period sh per ock =
  let rec apply_period nper ock = match ock with
    | Cone (s, _) -> Cone (s, nper)
    | Cshift (a, ock) -> Cshift(a, apply_period nper ock)
    | Covar { contents = ol } -> begin match ol with
      | Colink ock -> apply_period nper ock
      | Coindex _ -> failwith "Ock with no period associated is forbidden at that point"
      | Coper (op, _) -> Covar { contents = Coper(op, nper)}
      end
  in
  let n_ock = apply_period per ock in
  let n_ock = Cshift (sh, n_ock) in
  let n_ock = ock_repr n_ock in
  n_ock

(* Phase manipulation, corresponding to the time operators *)
let rec typing_when_osynch oct phWhen ratio = match oct with
  | Ocprod loct ->
    Ocprod ((List.map (fun oct -> typing_when_osynch oct phWhen ratio) ) loct)
  | Ock ock -> begin
    let ock = ock_repr ock in
    match ock with
    | Covar { contents = Coindex _ } ->
      failwith "Typing 1-synch when - variable clock manipulation should not happen?"
      (* Does this only happen when we have a when of a constant, or something like that? *)
    | _ ->
      let per = Clocks.get_period_ock ock in
      let nper = per * ratio in
      let shift = (phWhen * per) in
      let n_ock = apply_shift_period shift nper ock in
      Ock n_ock
  end 

let rec typing_current_osynch oct phCurr ratio = match oct with
  | Ocprod loct->
    Ocprod ((List.map (fun oct -> typing_current_osynch oct phCurr ratio) ) loct)
  | Ock ock -> begin
    let ock = ock_repr ock in
    match ock with
    | Covar { contents = Coindex _ } ->
      failwith "Typing 1-synch current - variable clock manipulation should not happen?"
      (* Does this only happen when we have a current of a constant, or something like that? *)
    | _ ->
      let per = Clocks.get_period_ock ock in
      assert(per mod ratio = 0); (* Harmonicity hypothesis *)
      let nper = per / ratio in
      let shift =  - (phCurr * nper) in
      let n_ock = apply_shift_period shift nper ock in

      (* Case where the current access the previous instance of the period
      let n_ock = match n_ock with
        | Cone (ph, _) -> if (ph<0) then Cone(0,nper) else n_ock
        | _ -> n_ock
      in *)
      
      (* DEBUG
      fprintf ffout "ock = %a ===(shift = %i | nper = %i)===> nock = %a\n@?"
        Global_printer.print_oneck ock  shift nper  Global_printer.print_oneck n_ock; *)
      Ock n_ock
  end 

let rec typing_delay_osynch oct d = match oct with
  | Ocprod loct->
    Ocprod ((List.map (fun oct -> typing_delay_osynch oct d) ) loct)
  | Ock ock -> begin
    let ock = ock_repr ock in
    match ock with
    | Covar { contents = Coindex _ } ->
      failwith "Typing 1-synch delay - variable clock manipulation should not happen?"
      (* Does this only happen when we have a delay of a constant, or something like that? *)
    | _ ->
      let per = Clocks.get_period_ock ock in
      let shift = d in
      assert(0<=d);
      let n_ock = apply_shift_period shift per ock in
      Ock n_ock
  end 

let rec typing_delayfby_osynch oct d = match oct with
 | Ocprod loct->
    Ocprod ((List.map (fun oct -> typing_delayfby_osynch oct d) ) loct)
  | Ock ock -> begin
    let ock = ock_repr ock in
    match ock with
    | Covar { contents = Coindex _ } ->
      failwith "Typing 1-synch delayfby - variable clock manipulation should not happen?"
      (* Does this only happen when we have a delay of a constant, or something like that? *)
    | _ ->
      let per = Clocks.get_period_ock ock in
      let shift = d - per in
      assert(0<=d);
      let n_ock = apply_shift_period shift per ock in
      Ock n_ock
  end 

(* ==================================== *)

(* Constraint generation for buffer operators *)

let rec typing_buffer_osynch oct = match oct with
  | Ocprod loct->
    let loct, lac = Misc.mapfold (fun lac_acc oct ->
      let noct, nlac = typing_buffer_osynch oct in
      noct, nlac@lac_acc
    ) [] loct in
    (Ocprod loct), lac
  | Ock ock -> begin
    let ock = ock_repr ock in
    match ock with
    | Covar { contents = Coindex _ } ->
      failwith "Typing 1-synch delay - variable clock manipulation should not happen?"
      (* Does this only happen when we have a delay of a constant, or something like that? *)
    | _ ->
      let per = Clocks.get_period_ock ock in
      let n_ock = fresh_osynch_period per in
      let (varopt_nock, laffterm, sh) = Clocks.get_phase_ock n_ock in
      let idvar_nock = match varopt_nock with
        | None -> failwith "Internal error"
        | Some idvar -> idvar
      in
      assert(laffterm=[]); assert(sh=0);
      let varname_n_ock = varname_from_phase_index idvar_nock in

      (* Affine constraint generation / ph_{n_ock} >= expr_{ock} *)
      let (varopt, laffterm, ph) = Clocks.get_phase_ock ock in

      let lcoeffVar = (1, varname_n_ock) :: [] in
      let lcoeffVar = match varopt with
        | None -> lcoeffVar
        | Some idvar ->
          (-1, varname_from_phase_index idvar)::lcoeffVar
      in
      let lcoeffVar = List.fold_left (fun acc (c,v) -> (-c, varname_from_phase_index v)::acc) lcoeffVar laffterm in
      let affconstr = mk_affconstr false lcoeffVar ph in

      (Ock n_ock, affconstr::[])
  end 

let rec typing_bufferfby_osynch oct = match oct with
  | Ocprod loct->
    let loct, lac = Misc.mapfold (fun lac_acc oct ->
      let noct, nlac = typing_bufferfby_osynch oct in
      noct, nlac@lac_acc
    ) [] loct in
    (Ocprod loct), lac
  | Ock ock -> begin
    let ock = ock_repr ock in
    match ock with
    | Covar { contents = Coindex _ } ->
      failwith "Typing 1-synch delay - variable clock manipulation should not happen?"
    | _ ->
      let per = Clocks.get_period_ock ock in
      let n_ock = fresh_osynch_period per in

      let constraint_bufferfby = not (!Compiler_options.no_constraint_bufferfby) in
      let laffconstr = if (constraint_bufferfby) then begin
        let (varopt_nock, laffterm, sh) = Clocks.get_phase_ock n_ock in
        let idvar_nock = match varopt_nock with
          | None -> failwith "Internal error"
          | Some idvar -> idvar
        in
        assert(laffterm=[]); assert(sh=0);
        let varname_n_ock = varname_from_phase_index idvar_nock in

        (* Affine constraint generation / expr_{ock} >= ph_{n_ock} +1 *)
        let (varopt, laffterm, ph) = Clocks.get_phase_ock ock in

        let lcoeffVar = (-1, varname_n_ock) :: [] in
        let lcoeffVar = match varopt with
          | None -> lcoeffVar
          | Some idvar ->
            (1, varname_from_phase_index idvar)::lcoeffVar
        in
        let lcoeffVar = List.fold_left (fun acc (c,v) -> (c, varname_from_phase_index v)::acc) lcoeffVar laffterm in
        let affconstr = mk_affconstr false lcoeffVar (1-ph) in
        affconstr::[]
      end else [] in
      (Ock n_ock, laffconstr)
  end 

let rec typing_bufferlat_osynch oct lat = match oct with
  | Ocprod loct ->
    let loct, lac = Misc.mapfold (fun lac_acc oct ->
      let noct, nlac = typing_bufferlat_osynch oct lat in
      noct, nlac@lac_acc
    ) [] loct in
    (Ocprod loct), lac
  | Ock ock -> begin
    let ock = ock_repr ock in
    match ock with
    | Covar { contents = Coindex _ } ->
      failwith "Typing 1-synch delay - variable clock manipulation should not happen?"
      (* Does this only happen when we have a delay of a constant, or something like that? *)
    | _ ->
      let per = Clocks.get_period_ock ock in
      let n_ock = fresh_osynch_period per in
      
      let (varopt_nock, laffterm, sh) = Clocks.get_phase_ock n_ock in
      let idvar_nock = match varopt_nock with
        | None -> failwith "Internal error"
        | Some idvar -> idvar
      in
      assert(laffterm=[]); assert(sh=0);
      let varname_n_ock = varname_from_phase_index idvar_nock in

      let (varopt, laffterm, ph) = Clocks.get_phase_ock ock in

      (* Affine constraint generation / lat >= ph_{n_ock} - ph_{ock} >= 0 *)

      (* ph_{ock} - ph_{n_ock} >= -lat *)
      let lcoeffVar_lat = (-1, varname_n_ock) :: [] in
      let lcoeffVar_lat = match varopt with
        | None -> lcoeffVar_lat
        | Some idvar ->
          (1, varname_from_phase_index idvar)::lcoeffVar_lat
      in
      let lcoeffVar_lat = List.fold_left (fun acc (c,v) ->
          (c, varname_from_phase_index v)::acc
        ) lcoeffVar_lat laffterm
      in
      let affconstr_lat = mk_affconstr false lcoeffVar_lat (-lat-ph) in

      (* ph_{n_ock} - ph_{ock} >= 0  *)
      let lcoeffVar_0 = (1, varname_n_ock) :: [] in
      let lcoeffVar_0 = match varopt with
        | None -> lcoeffVar_0
        | Some idvar ->
          (-1, varname_from_phase_index idvar)::lcoeffVar_0
      in
      let lcoeffVar_0 = List.fold_left (fun acc (c,v) ->
          (-c, varname_from_phase_index v)::acc
        ) lcoeffVar_0 laffterm
      in
      let affconstr_0 = mk_affconstr false lcoeffVar_0 ph in

      let laffconstr = affconstr_0::affconstr_lat::[] in
      (Ock n_ock, laffconstr)
  end


(* ==================================== *)

(* Constraint generation for underspecified operators (the "?" operators) *)

let rec typing_whenq_osynch octe min max ratio dvarid = match octe with
  | Ocprod loct ->
    let loct, lac = Misc.mapfold (fun lac_acc oct ->
      let (noct, nlac) = typing_whenq_osynch oct min max ratio dvarid in
      noct, nlac@lac_acc
    ) [] loct in
    (Ocprod loct), lac
  | Ock ock -> begin
    let ock = ock_repr ock in
    match ock with
    | Covar { contents = Coindex _ } ->
      failwith "Typing 1-synch when? - variable clock manipulation should not happen?"
      (* Does this only happen when we have a when of a constant, or something like that? *)
    | _ ->
      (* Coherence of min/max related to the ratio *)
      assert(0<=min);
      assert(min<=max);
      assert(max<ratio);    (* min <= d <= max *)
      
      (* The shift is parametrised by a new integer variable "d" (decision variable) *)
      let dvarname = varname_from_phase_index dvarid in
      
      (* We build the clock [sh + ( (per,dvar)::laffterm) + idvar_ock , per * ratio ] *)
      let (varopt_ock, laffterm, sh, _, per) = Clocks.extract_ock_info ock in
      let nper = per * ratio in
      let nlaffterm = (per, dvarid)::laffterm in
      let n_ock =  build_clock varopt_ock nlaffterm sh nper in

      (* Constraint on the phase of n_ock *)
      (* idvar_ock + ( (per,dvar)::laffterm) + sh >= 0 *)
      let nlaffterm_str = List.map (fun (c,v) -> (c, varname_from_phase_index v)) nlaffterm in
      let lcoeffVar3 = match varopt_ock with
        | None -> nlaffterm_str
        | Some varid -> (1, varname_from_phase_index varid)::nlaffterm_str
      in
      let affconstr3 = mk_affconstr false lcoeffVar3 (-sh) in

      (* idvar_ock + ( (per,dvar)::laffterm) + sh <= nper *)
      let nlaffterm_op = List.map (fun (c,v) -> (-c,v)) nlaffterm_str in
      let lcoeffVar4 = match varopt_ock with
        | None -> nlaffterm_op
        | Some varid -> (-1, varname_from_phase_index varid)::nlaffterm_op
      in
      let affconstr4 = mk_affconstr false lcoeffVar4 (sh-nper) in

      ((Ock n_ock), affconstr3::affconstr4::[])
  end 

let rec typing_currentq_osynch octe min max ratio dvarid = match octe with
  | Ocprod loct ->
    let loct, lac = Misc.mapfold (fun lac_acc oct ->
      let noct, nlac = typing_currentq_osynch oct min max ratio dvarid in
      noct, nlac@lac_acc
    ) [] loct in
    (Ocprod loct), lac
  | Ock ock -> begin
    let ock = ock_repr ock in
    match ock with
    | Covar { contents = Coindex _ } ->
      failwith "Typing 1-synch current? - variable clock manipulation should not happen?"
      (* Does this only happen when we have a when of a constant, or something like that? *)
    | _ ->
      (* Coherence of min/max related to the ratio *)
      assert(0<=min);
      assert(min<=max);
      assert(max<ratio);    (* min <= d <= max *)
      
      (* The shift is parametrised by a new integer variable "d" (decision variable) *)
      let dvarname = varname_from_phase_index dvarid in
      
      (* We build the clock [sh + ( (-nper,dvar)::laffterm) + idvar_ock , per * ratio ] *)
      let (varopt_ock, laffterm, sh, _, per) = Clocks.extract_ock_info ock in
      let nper = per / ratio in
      let nlaffterm = (-nper, dvarid)::laffterm in
      let n_ock =  build_clock varopt_ock nlaffterm sh nper in

      (* Constraint on the phase of n_ock *)

      (* idvar_ock + ((-nper,dvar)::laffterm) + sh >= 0 *)
      let nlaffterm_str = List.map (fun (c,v) -> (c, varname_from_phase_index v)) nlaffterm in
      let lcoeffVar3 = match varopt_ock with
        | None -> nlaffterm_str
        | Some varid -> (1, varname_from_phase_index varid)::nlaffterm_str
      in
      let affconstr3 = mk_affconstr false lcoeffVar3 (-sh) in

      (* idvar_ock + ((-nper,dvar)::laffterm) + sh < nper *)
      let nlaffterm_op = List.map (fun (c,v) -> (-c,v)) nlaffterm_str in
      let lcoeffVar4 = match varopt_ock with
        | None -> nlaffterm_op
        | Some varid -> (-1, varname_from_phase_index varid)::nlaffterm_op
      in
      let affconstr4 = mk_affconstr false lcoeffVar4 (sh-nper+1) in

      (* DEBUG
      fprintf ffout "PING\n@?";
      fprintf ffout "affconstr3 = %a\n@?" print_aff_constr affconstr3;
      fprintf ffout "affconstr4 = %a\n@?" print_aff_constr affconstr4; *)

      ((Ock n_ock), affconstr3::affconstr4::[])
  end 

let rec typing_bufferfbyq_osynch octe dvarid = match octe with
  | Ocprod loct ->
    let loct, lac = Misc.mapfold (fun lac_acc oct ->
      let noct, nlac = typing_bufferfbyq_osynch oct dvarid in
      noct, nlac@lac_acc
    ) [] loct in
    (Ocprod loct), lac
  | Ock ock -> begin
    let ock = ock_repr ock in
    match ock with
    | Covar { contents = Coindex _ } ->
      failwith "Typing 1-synch bufferfby? - variable clock manipulation should not happen?"
      (* Does this only happen when we have a when of a constant, or something like that? *)
    | _ ->
      (* The shift is parametrised by a new integer variable "d" (decision variable) *)
      let dvarname = varname_from_phase_index dvarid in
      
      (* Output clock of the bufferfby? + getting its informations *)
      let (varopt, laffterm, ph) = Clocks.get_phase_ock ock in
      let per = Clocks.get_period_ock ock in
      let n_ock = fresh_osynch_period per in

      let (varopt_nock, laffterm, sh) = Clocks.get_phase_ock n_ock in
      let idvar_nock = match varopt_nock with
        | None -> failwith "Internal error"
        | Some idvar -> idvar
      in
      assert(laffterm=[]); assert(sh=0);
      let varname_n_ock = varname_from_phase_index idvar_nock in

      (* Constraint on the phase
        => constraint buffer to be activated only when d=0
        => constraint bufferfby to be activated if option + d=1 :/ *)

      (* Constraint to be activated when d=1:
          expr_{ock} + per*(1-d) >= ph_{n_ock} + 1
          <=> expr_{ock} - per*d >= ph_{n_ock} - per + 1 *)
      let constraint_bufferfby = not (!Compiler_options.no_constraint_bufferfby) in
      let laffconstr_ph = if (constraint_bufferfby) then begin

        let lcoeffVar = (-1, varname_n_ock) :: [] in
        let lcoeffVar = match varopt with
          | None -> lcoeffVar
          | Some idvar ->
            (1, varname_from_phase_index idvar)::lcoeffVar
        in
        let lcoeffVar = List.fold_left (fun acc (c,v) -> (c, varname_from_phase_index v)::acc) lcoeffVar laffterm in
        let lcoeffVar = ((-per), dvarname)::lcoeffVar in

        let affconstr_ph1 = mk_affconstr false lcoeffVar (1-ph-per) in
        affconstr_ph1::[]
      end else [] in

      (* DEBUG
      fprintf ffout "bufferfbyq - constraint_bufferfby = %b\n@?" constraint_bufferfby;
      fprintf ffout "bufferfbyq - laffconstr_ph (temp) = %a\n@?"
        print_list_aff_constr laffconstr_ph; *)


      (* Constraint to be activated when d=0:
        ph_{n_ock} + d*per >= expr_{ock} *)
      let lcoeffVar = (1, varname_n_ock) :: [] in
      let lcoeffVar = match varopt with
        | None -> lcoeffVar
        | Some idvar ->
          (-1, varname_from_phase_index idvar)::lcoeffVar
      in
      let lcoeffVar = List.fold_left (fun acc (c,v) -> (-c, varname_from_phase_index v)::acc) lcoeffVar laffterm in
      let lcoeffVar = (per, dvarname)::lcoeffVar in
      let affconstr_ph2 = mk_affconstr false lcoeffVar ph in
      let laffconstr_ph = affconstr_ph2 :: laffconstr_ph in

      ((Ock n_ock), laffconstr_ph)
  end


(* ==================================== *)
let ock_of_name h x =
  try Env.find x h
  with Not_found ->
    Format.printf "Not found while hept_clocking : %a@\n" Idents.print_ident x;
    raise Not_found

let rec typing_model_pat h = function
  | Evarpat x -> Ock (ock_of_name h x)
  | Etuplepat pat_list -> Ocprod (List.map (typing_model_pat h) pat_list)

let rec typing_osych h lcst pat e = match e.e_desc with
  | Econst _ -> 
    let ock = fresh_osynch_clock () in
    (Ock ock, lcst, [], None)
  | Evar x ->
    let ock = ock_of_name h x in
    (Ock ock, lcst, [], None)
  | Efby (e1, e2) ->
    let (ct1, lcst, lsubst_e1, odecvar) = typing_osych h lcst pat e1 in
    assert(odecvar=None);
    let (lcst, lsubst_fby, odecvar) = expect_osynch h lcst pat ct1 e2 in
    let lsubst = List.rev_append lsubst_fby lsubst_e1 in
    (ct1, lcst, lsubst, odecvar)
  | Epre (_,e2) ->
    typing_osych h lcst pat e2
  | Estruct l ->
    let ock = fresh_osynch_clock () in
    let (lcst, lsubst) = List.fold_left (fun (lcst, lsubst_acc) (_, e) ->
      let (lcst, lsubst_e, odecvar) = expect_osynch h lcst pat (Ock ock) e in
      assert(odecvar=None);
      let lsubst_acc = List.rev_append lsubst_e lsubst_acc in
      (lcst, lsubst_acc)
    ) (lcst,[]) l in
    (Ock ock, lcst, lsubst, None)

  (* Expressions specific to model *)
  | Ewhenmodel (e, (ph,ratio)) ->
    let (octe, lcst, lsubst, odecvar) = typing_osych h lcst pat e in
    let noct = typing_when_osynch octe ph ratio in
    (noct, lcst, lsubst, odecvar)

  | Ecurrentmodel ((ph, ratio), _, e) ->
    let (octe, lcst, lsubst, odecvar) = typing_osych h lcst pat e in
    let noct = typing_current_osynch octe ph ratio in
    (noct, lcst, lsubst, odecvar)

  | Edelay (d, e) ->
    let (octe, lcst, lsubst, odecvar) = typing_osych h lcst pat e in
    let noct = typing_delay_osynch octe d in
    (noct, lcst, lsubst, odecvar)

  | Edelayfby (d, _, e) ->
    let (octe, lcst, lsubst, odecvar) = typing_osych h lcst pat e in
    let noct = typing_delayfby_osynch octe d in
    (noct, lcst, lsubst, odecvar)

  | Ebuffer e ->
    let (octe, lcst, lsubst, odecvar) = typing_osych h lcst pat e in
    let (noct, laffconstr) = typing_buffer_osynch octe in
    let (al,bl) = lcst in
    (noct, (laffconstr@al,bl), lsubst, odecvar)

  | Ebufferfby (_, e) ->
    let (octe, lcst, lsubst, odecvar) = typing_osych h lcst pat e in
    let (noct, laffconstr) = typing_bufferfby_osynch octe in
    let (al,bl) = lcst in
    (noct, (laffconstr@al,bl), lsubst, odecvar)

  | Ebufferlat (lat, e) ->
    let (octe, lcst, lsubst, odecvar) = typing_osych h lcst pat e in
    let (noct, laffconstr) = typing_bufferlat_osynch octe lat in
    let (al,bl) = lcst in
    (noct, (laffconstr@al,bl), lsubst, odecvar)

  | Efbyq (seInit, e) ->  (* fby? does not have any impact on the clock itself *)
    let (octe, lac, lsubst, odecvar) = typing_osych h lcst pat e in
    assert(odecvar=None);  (* No nested underspecified operators *)

    (* Building the decision variable *)
    let dvarid = Clocks.gen_index () in
    let dvarname = varname_from_phase_index dvarid in
    
    (* Boundary constraint : 0<= dvarname <=1 *)
    let bc_dec = mk_bound_constr dvarname 0 2 in
    let (al,bl) = lcst in
    (octe, (al,bc_dec::bl), lsubst, Some dvarname)

  | Ewhenq (e, (min,max), ratio) ->
    let (octe, lcst, lsubst, odecvar) = typing_osych h lcst pat e in
    assert(odecvar=None);  (* No nested underspecified operators *)

    (* Building the decision variable *)
    let dvarid = Clocks.gen_index () in
    let dvarname = varname_from_phase_index dvarid in

    (* Constraints on the decision variable d : min<=d<=max *)
    let bc_dec = mk_bound_constr dvarname min (max+1) in

    let (noct, laffconstr) = typing_whenq_osynch octe min max ratio dvarid in
    let (al,bl) = lcst in
    (noct, (laffconstr@al, bc_dec::bl), lsubst, Some dvarname)

  | Ecurrentq (ratio, (min,max), seInit, e) ->
    let (octe, lcst, lsubst, odecvar) = typing_osych h lcst pat e in
    assert(odecvar=None);  (* No nested underspecified operators *)

    (* Building the decision variable *)
    let dvarid = Clocks.gen_index () in
    let dvarname = varname_from_phase_index dvarid in

    (* Constraints on the decision variable d : min<=d<=max *)
    let bc_dec = mk_bound_constr dvarname min (max+1) in

    let (noct, laffconstr) = typing_currentq_osynch octe min max ratio dvarid in
    let (al,bl) = lcst in
    (noct, (laffconstr@al, bc_dec::bl), lsubst, Some dvarname)

  | Ebufferfbyq (seInit,e) ->
    let (octe, lcst, lsubst, odecvar) = typing_osych h lcst pat e in
    assert(odecvar=None);  (* No nested underspecified operators *)

    (* Building the decision variable *)
    let dvarid = Clocks.gen_index () in
    let dvarname = varname_from_phase_index dvarid in

    (* Constraints on the decision variable: 0<=d<=1 *)
    let bc_dec = mk_bound_constr dvarname 0 2 in

    let (noct, laffconstr) = typing_bufferfbyq_osynch octe dvarid in
    let (al,bl) = lcst in
    (noct, (laffconstr@al, bc_dec::bl), lsubst, Some dvarname)

  | Eapp({a_op = op}, args, _) ->
      let base_ock = fresh_osynch_clock () in
      let (oct, lcst, lsubst) = typing_osynch_app h lcst base_ock pat op args in
      (oct, lcst, lsubst, None)

  (* TODO: iterators needed ??? :/ *)
  | Eiterator (it, {a_op = op}, nl, pargs, args, _) ->
    let base_ock = fresh_osynch_clock () in
    let (oct, lcst, lsubst) = match it with
      | Imap -> (* exactly as if clocking the node *)
          typing_osynch_app h lcst base_ock pat op (pargs@args)
      | Imapi -> (* clocking the node with the extra i input on [ck_r] *)
          let il (* stubs i as 0 *) =
            List.map (fun _ -> mk_exp
                (Econst (Initial.mk_static_int 0))
                Initial.tint ~linearity:Linearity.Ltop
            ) nl
          in
          typing_osynch_app h lcst base_ock pat op (pargs@args@il)
      | Ifold | Imapfold ->
          (* clocking node with equality constaint on last input and last output *)
          let (oct, lcst, lsubst) = typing_osynch_app h lcst base_ock pat op (pargs@args) in
          (oct, lcst, lsubst)
      | Ifoldi -> (* clocking the node with the extra i and last in/out constraints *)
          let il (* stubs i as 0 *) =
            List.map (fun _ -> mk_exp
                (Econst (Initial.mk_static_int 0))
                Initial.tint ~linearity:Linearity.Ltop
            ) nl
          in
          let rec insert_i args = match args with
            | [] -> il
            | [l] -> il @ [l]
            | h::l -> h::(insert_i l)
          in
          let (oct, lcst, lsubst) = typing_osynch_app h lcst base_ock pat op (pargs@(insert_i args)) in
          (oct, lcst, lsubst)
    in
    (oct, lcst, lsubst, None)
  | Esplit _ | Elast _ | Ecurrent _ -> assert false
  | Emerge _ | Ewhen _ -> failwith "Construction should not appear in a model node"

and typing_osynch_app h lcst base pat op e_list = match op with
  | Etuple (* to relax ? *)
  | Earrow
  | Earray_fill | Eselect | Eselect_dyn | Eselect_trunc | Eupdate
  | Eselect_slice | Econcat | Earray | Efield | Efield_update | Eifthenelse | Ereinit ->
    let (lcst, lsubst) = List.fold_left (fun (lcst, lsubst_acc) e ->
      let (lcst, lsubst_e, odecvar) = expect_osynch h lcst pat (Ock base) e in
      assert(odecvar=None); (* No nested underspecified operator *)
      let lsubst_acc = List.rev_append lsubst_e lsubst_acc in
      (lcst, lsubst_acc)
    ) (lcst, []) e_list in
    (Ock base, lcst, lsubst)
  | Efun { qual = Module "Iostream"; name = "printf" } | Efun { qual = Module "Iostream"; name = "fprintf" } ->
    let (lcst, lsubst) = List.fold_left (fun (lcst, lsubst_acc) e ->
      let (lcst, lsubst_e, odecvar) = expect_osynch h lcst pat (Ock base) e in
      assert(odecvar=None); (* No nested underspecified operator *)
      let lsubst_acc = List.rev_append lsubst_e lsubst_acc in
      (lcst, lsubst_acc)
    ) (lcst, []) e_list in
    (Ocprod [], lcst, lsubst)
  | (Efun f | Enode f) ->
    (* Big one - function call *)
    (* REMARK - We forbid clock change inside a function called by a model node
        (ie, no "on" on the output of clocks => no clock on sign of function) *)
    let node = Modules.find_value f in
    (*let rec build_env a_l v_l env = match a_l, v_l with
      | [],[] -> env
      | a::a_l, v::v_l -> (match a.a_name with
          | None -> build_env a_l v_l env
          | Some n -> build_env a_l v_l ((n,v)::env)
        )
      | _ ->
          Misc.internal_error ("Clocking, non matching signature in call of "^
                                  Names.fullname f);
    in
    let pat_id_list = Hept_clocking.ident_list_of_pat pat in
    let env_pat = build_env node.node_outputs pat_id_list [] in
    let env_args = build_env node.node_inputs e_list [] in 
    List.iter2 (fun _ e -> expect_osynch h lcst pat (Ock base) e) node.node_inputs e_list; *)
    let (lcst, lsubst) = List.fold_left (fun (lcst, lsubst_acc) e ->
      let (lcst, lsubst_arg, odecvar) = expect_osynch h lcst pat (Ock base) e in
      assert(odecvar=None); (* No nested underspecified operator *)
      let lsubst_acc = List.rev_append lsubst_arg lsubst_acc in
      (lcst, lsubst_acc)
    ) (lcst, []) e_list in
    (Ocprod (List.map (fun _ -> (Ock base)) node.node_outputs), lcst, lsubst)

and expect_osynch h lcst pat expected_oct e =
  let (actual_oct, lcst, lsubst_e, odecvar) = typing_osych h lcst pat e in

  (* Unification might implies a substitution and a constraint on a decision variable *)
  let (lsubst_unif, lconstr_decvar_unif) :
      ((bool * int * int option * int * (int*int) list) list)
        * ( (int*int) list * int) list = (try
    unify_onect_constr actual_oct expected_oct
  with Unify ->
    error_message e.e_loc (Etypeclash (actual_oct, expected_oct))
  ) in

  (* We build the constraint on the decision variable *)
  let lac_decvar = List.map (fun (laffterm_int, cst_term) ->
    let lcoeffVar = List.map (fun (c,v) -> (c, varname_from_phase_index v)) laffterm_int in
    mk_affconstr true lcoeffVar cst_term
  ) lconstr_decvar_unif in

  (* Return all of that *)
  let (lac, lbc) = lcst in
  let lncst = (lac_decvar @ lac, lbc) in
  let lsubst = List.rev_append lsubst_e lsubst_unif in
  (lncst, lsubst, odecvar)


(* ----- *)
(* ----- *)

(* Causality constraint *)

(* Note: only used on lhs of normalised equations with a underspecified operator on the rhs *)
let rec get_first_var pat = match pat with
  | Etuplepat pl ->
    if (pl=[]) then failwith "typing_model_eq - internal error: equation with an underspecified operator has no lhs."
    else get_first_var (List.hd pl)
  | Evarpat vid -> vid

(* Get the list of variable from the lhs *)
let rec get_vars_lhs plhs = match plhs with
  | Etuplepat pl ->
    List.fold_left (fun lacc p ->
      (get_vars_lhs p) @ lacc
    ) [] pl
  | Evarpat vid -> vid::[]

(* Get the list of *present* variable used in the rhs of a model equation *)
let get_lvar_used eqm =
  let exp_lvar_used funs lacc exp = match exp.e_desc with
    | Evar vid | Elast vid -> exp, vid::lacc        (* Variable use detected ! *)
    | Epre _ | Efby _ | Edelayfby _ | Ebufferfby _ ->  exp, lacc  (* Stop recursion if we go into the past *)
    | _ -> Hept_mapfold.exp funs lacc exp           (* Other cases: just do a recursion *)
  in
  let funs_lvar_used = { Hept_mapfold.defaults with exp = exp_lvar_used } in
  let _, lvar = funs_lvar_used.eq_model funs_lvar_used [] eqm in
  lvar

(* Remove duplicated elements from a list *)
let rec list_make_unique lres l = match l with
  | [] -> lres
  | h::t -> if (List.mem h lres) then
      list_make_unique lres t
    else
      list_make_unique (h::lres) t

(* Pretty-printer of list of strongly connected component, for debugging and error management *)
let print_lscc ff lscc =
  let print_scc ff scc =
    fprintf ff "[";
    List.iter (fun varid ->
      fprintf ff "%a, " print_ident varid
    ) scc;
    fprintf ff "]"
  in
  fprintf ff "[[[\n@?";
  List.iter (fun scc ->
    fprintf ff "\t%a\n@?" print_scc scc
  ) lscc;
  fprintf ff "]]]\n@?"

let print_loop ff loop =
  fprintf ff "[";
  List.iter (fun eqm ->
    fprintf ff "%a, " Hept_printer.print_pat_init (eqm.eqm_lhs, Lno_init)
  ) loop;
  fprintf ff "]"

let print_l_loops ff l_loops = 
  fprintf ff "[[[\n@?";
  List.iter (fun loop ->
    fprintf ff "\t%a\n@?" print_loop loop
  ) l_loops;
  fprintf ff "]]]\n@?"

(* Pretty-printer of the main internal data structure of the scc algo, for debugging *)
let print_mIndex ff mIndex =
  Idents.Env.iter (fun k (ind, lowlink) ->
    fprintf ff "\t %a  --> (%i, %i)\n@?" print_ident k  ind lowlink
  ) mIndex

(* Strongly connected component extraction - Tarjan algorithm *)
let strongly_connected_components mVar2Eq leqm leqmStart =

  (* Last part of the Tarjan algorithm - building the strongly connected component *)
  let rec pop_connected_component mIndex stvar index_root lstr_conn_comp mIsOnStack =
    (* We pop the first element of the stack *)
    let (w_id, stvar) = match stvar with
      | [] -> failwith "Internal strongly_connected_components error: Empty stack"
      | a::b -> (a,b)
    in
    let mIsOnStack = Env.update w_id (fun _ -> Some false) mIsOnStack in
    let (index_w, _) = Idents.Env.find w_id mIndex in

    let lstr_conn_comp = w_id::lstr_conn_comp in

    (* Should we continue? *)
    if (index_w!=index_root) then
      pop_connected_component mIndex stvar index_root lstr_conn_comp mIsOnStack
    else
     (lstr_conn_comp, stvar, mIsOnStack)
  in


  (* We use Tarjan algorithm to get strongly connected components (fby = no edge) *)
  (* Broad idea: graph coloring with the lowest label a backlink goes to... *)
  (* I used the English wikipedia page of Tarjan algorithm to implement it *)
  (* https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm *)
  let rec strong_connect mVar2Eq lconncomp mIndex index stvar mIsOnStack varid =

    (* mIndex : varid ---> (index, lowlink) *)
    let mIndex = Idents.Env.add varid (index, index) mIndex in
    let index = index + 1 in

    (* Stack = path used by the depth first search algo used to traverse the graph *)
    let stvar = varid::stvar in  (* Push *)
    let mIsOnStack = Env.update varid (fun _ -> Some true) mIsOnStack in

    (* DEBUG
    fprintf ffout "strong_connect - varid = %a\n@?" print_ident varid;
    fprintf ffout "lconncomp = %a\n@?" print_lscc lconncomp; *)

    (* For each successor of varid *)
    let lvar_successor = try
      let eqm_varid = Env.find varid mVar2Eq in
      let lvar_successor = get_lvar_used eqm_varid in
      lvar_successor
    with Not_found -> [] (* We have an input => no successor *)
    in

    let (stvar, lconncomp, mIndex, index, mIsOnStack) = List.fold_left
      (fun (stvar, lconncomp, mIndex, index, mIsOnStack) var_succ ->
      (* If "var_succ" was not visited yet, then recursion!  (edge is on the traversal tree)  *)
      if (not (Env.mem var_succ mIndex)) then
        let (stvar, lconncomp, mIndex, index, mIsOnStack) =
          strong_connect mVar2Eq lconncomp mIndex index stvar mIsOnStack var_succ in

        let (_, lowlink_varid) = Idents.Env.find varid mIndex in
        let (_, lowlink_var_succ) = Idents.Env.find var_succ mIndex in 
        let lowlink = Pervasives.min lowlink_varid lowlink_var_succ in

        let mIndex = Env.update varid (fun ocurmap -> match ocurmap with
          | None -> failwith ("Mapping of " ^ (Idents.name varid) ^ "not found in mIndex")
          | Some (ind_curmap, _) -> Some (ind_curmap, lowlink)
        ) mIndex in
        (stvar, lconncomp, mIndex, index, mIsOnStack)
      else

      (* If the successor "var_succ" is on the stack, we have a backedge (because depth-first search) *)
      if (Env.find var_succ mIsOnStack) then
        let (_, lowlink_varid) = Idents.Env.find varid mIndex in
        let (index_var_succ, _) = Idents.Env.find var_succ mIndex in
        let lowlink = Pervasives.min lowlink_varid index_var_succ in

        let mIndex = Env.update varid (fun ocurmap -> match ocurmap with
          | None -> failwith ("Mapping of " ^ (Idents.name varid) ^ "not found in mIndex")
          | Some (ind_curmap, _) -> Some (ind_curmap, lowlink)
        ) mIndex in
        (stvar, lconncomp, mIndex, index, mIsOnStack)
      else
        (* "var_succ" is a cross-edge in the DFS tree, and can be ignored *)
        (stvar, lconncomp, mIndex, index, mIsOnStack)
    ) (stvar, lconncomp, mIndex, index, mIsOnStack) lvar_successor in

    (* DEBUG
    fprintf ffout "strong_connect - after-propagation - varid = %a\n@?" print_ident varid; *)
    (* DEBUG
    fprintf ffout "strong_connect - after-propagation - mIndex = %a\n@?" print_mIndex mIndex;
    fprintf ffout "strong_connect - after-propagation - stvar = %a\n@?"
      (Pp_tools.print_list print_ident "[" ", " " ]") stvar; *)

    (* Root node: "index = lowlink". We have as many SCC than root nodes *)

    (* If v is a root node (ie, lowlink = index), pop the stack and generate a SCC *)
    let (index_varid, lowlink_varid) = Idents.Env.find varid mIndex in
    
    let (lconncomp, stvar, mIsOnStack) =
      if (index_varid = lowlink_varid) then
        (* We have finished to explore a SCC => build it *)
        let (nstr_conn_comp, stvar, mIsOnStack) = pop_connected_component mIndex stvar index_varid [] mIsOnStack in
        (nstr_conn_comp::lconncomp, stvar, mIsOnStack)
      else
        (lconncomp, stvar, mIsOnStack)
    in
    (stvar, lconncomp, mIndex, index, mIsOnStack)
  in

  (* Stack and mapping to know if a variable is on the stack *)
  let stvar = [] in
  let mIsOnStack = Idents.Env.fold (fun varid _ macc ->
    Env.add varid true macc
  ) mVar2Eq Idents.Env.empty in
  
  (* Main loop *)
  (* mIndex: varId -> (index, lowlink) *)
  let (_, lconncomp, _, _, _) = Idents.Env.fold (fun varid _ (stvar, lconncomp, macc, index, mIsOnStack) ->
    if (Idents.Env.mem varid macc) then (stvar, lconncomp, macc, index, mIsOnStack) else
    strong_connect mVar2Eq lconncomp macc index stvar mIsOnStack varid
  ) mVar2Eq ([], [], Idents.Env.empty, 0, mIsOnStack) in

  (* Return the list of strongly connected components *)
  lconncomp

(* Constraint extraction from a strongly connected component *)
let extract_constraint_from_scc mdecvar mVar2Eq (scc:var_ident list) =
  assert((List.length scc)>0);

  let rec back_loop_detection checkedpath succ lpath_tocheck = match lpath_tocheck with
    | [] -> None
    | (v, eqm)::rest ->
      if (v=succ) then Some (eqm::checkedpath) else
      back_loop_detection (eqm::checkedpath) succ rest
  in

  (* Algorithm:
    - Consider a random node and start a deep first search graph exploration in the scc from it
        (ignoring the fby edges, as usual for the causality analysis)
    - If we go back to a node on the stack of explored node, then we have detected a cycle.
      => All cycle can be obtained like that (even the one not including root_node) because it is a scc *)
  (* Note. lcurrent_path is in the opposite order ( :: in the list  <=>  <- in the graph ) *)
  let rec loop_obtention mVar2Eq (scc:var_ident list) (l_loops_res: eq_model list list)
    (lcurrent_path: (var_ident * eq_model) list) (current_node:var_ident) =

    (* DEBUG
    fprintf ffout "DEBUG loop_obtention - current_node = %a\n@?" print_ident current_node; *)

    (* We check the next edge in the graph *)
    let (next_edge: eq_model) = Idents.Env.find current_node mVar2Eq in
    let lsuccessors = get_lvar_used next_edge in
    
    (* Remove the nodes not in the scc *)
    let lsuccessors = List.filter (fun v -> List.mem v scc) lsuccessors in

    let l_loops = List.fold_left (fun l_loop_acc succ -> 
      (* Loop detection - is "succ" in lcurrent_path + current_node? *)
      if (succ=current_node) then
        [ next_edge ] :: l_loop_acc
      else
      let (oloop : (eq_model list) option) = back_loop_detection [] succ lcurrent_path in

      match oloop with
      | Some nloop ->
        (nloop @ [next_edge]) :: l_loop_acc
      | None ->
        (* Recursion - deep first search *)
        let nlcurrent_path = (current_node, next_edge) :: lcurrent_path in
        loop_obtention mVar2Eq scc l_loop_acc nlcurrent_path succ
    ) l_loops_res lsuccessors in
    l_loops
  in

  let (l_loops: eq_model list list) = loop_obtention mVar2Eq scc [] [] (List.hd scc) in

  (* DEBUG
  fprintf ffout "l_loops = %a\n@?" print_l_loops l_loops; *)

  (* Constraint generation: because we consider 1-synchronous clock,
      if we have a dependence loop without having a fby somewhere in the middle,
      the data used must be the same that we are trying to obtain, thus fail.
    => It is enough to just check the fby? and bufferfby? and generate a constraint
      that at least one of their decision variable is 1 (\sum dec_var >= 1) *)
  let (lldecvar:string list list) = List.map (fun loop ->
    let ldecvar = List.fold_left (fun ldecvar_acc eqm ->
      match eqm.eqm_rhs.e_desc with
      | Efbyq _ | Ebufferfbyq _ ->
        let ndecvar = Idents.Env.find (get_first_var eqm.eqm_lhs) mdecvar in
        ndecvar::ldecvar_acc
      | _ -> ldecvar_acc
    ) [] loop in
    if (ldecvar=[]) then (
      (* True causality-violating cycle detected !!! *)
      fprintf ffout "Causality violating cycle = %a\n@?" print_loop loop;
      failwith "Program is not causal, causality violating cycle outputed."
    ) else
      ldecvar

  ) l_loops in

  (* Constraint redundancy: using the decision variables, we remove the redundancies *)
  (* Done by sorting elements, then checking for equality *)
  let lldecvar = List.map (fun ldecvar -> List.sort Pervasives.compare ldecvar) lldecvar in
  let lldecvar = list_make_unique [] lldecvar in

  (* Building the constraints *)
  let lac_caus = List.map (fun ldecvar ->
    let lcoeffVar = List.map (fun v -> (1,v)) ldecvar in
    mk_affconstr false lcoeffVar 1
  ) lldecvar in
  lac_caus

(* Constraints for the causality management, if we have underspecified ops *)
let add_causality_constraint lcst mdecvar leqm =
  (* a) List all cycles in the dependence graph which contains a fbyq or a bufferfbyq equation *)
  (* To do that, we start looking for cycle (with no fby) from variables above fbyq/bufferfbyq,
    which are not yet reached by a broad-first search algorithm (broad to minimize the length of the cycle) *)

  (* List of the starting point of the graph exploration - Nots: equations are normalized *)
  let leqmStart = List.fold_left (fun lacc eqm -> match eqm.eqm_rhs.e_desc with
    | Efbyq _ | Ebufferfbyq _ -> eqm::lacc
    | _ -> lacc
  ) [] leqm in

  if (leqmStart=[]) then lcst else  (* No fbyq or bufferfbyq => No extra constraint *)

  (* Build the set of the unexplored variables + associate them to their equation *)
  let mVar2Eq = List.fold_left (fun macc eqm ->
    let lvarlhs = get_vars_lhs eqm.eqm_lhs in
    List.fold_left (fun macc varid -> Idents.Env.add varid eqm macc) macc lvarlhs
  ) Idents.Env.empty leqm in

  (* Start of the graph exploration algorithm *)
  let (lscc : var_ident list list) = strongly_connected_components mVar2Eq leqm leqmStart in

  (* DEBUG *)
  if (debug_clocking) then
    fprintf ffout "... causality constraintes: ssc found.\n@?";
  (* DEBUG
  fprintf ffout "lscc = %a\n@?" print_lscc lscc; *)

  (* Verification that lscc is a partition - TODO later?
  check_lscc leqm lscc; *)

  (* We filter the inputs, which forms scc of size 1 with no corresponding equation in mVar2Eq *)
  let lscc = List.fold_left (fun lacc scc -> 
    if ((List.length scc) =1) then (
      let varid = List.hd scc in
      if (Idents.Env.mem varid mVar2Eq) then
        scc::lacc
      else
        lacc
    ) else scc::lacc
  ) [] lscc in

  (* For all cycles in a strongly connected component, extract a constraints *)
  let lac_causality = List.fold_left (fun lac_acc scc ->
    let nlac = extract_constraint_from_scc mdecvar mVar2Eq scc in
    List.rev_append nlac lac_acc
  ) [] lscc in

  if (debug_clocking) then (
    fprintf ffout "... causality constraintes: built.\n@?";
    fprintf ffout "lac_causality = %a\n@?" print_list_aff_constr lac_causality
  );

  (* Merge the new constraints with the old ones *)
  let (lac, lbc) = lcst in
  (List.rev_append lac_causality lac, lbc)

(* ----- *)
(* ----- *)

(* Constraint for latency chains *)
let add_latency_chain_constraint mdecvar mVar2Eq mvar_ock lat lvid_chain lcst_acc =
  (* let rec remove_last_elem l = match l with
    | [] -> failwith "internal error: remove_last_elem applied to an empty list"
    | h::[] -> []
    | h::t -> h::(remove_last_elem t)
  in *)
  let lvid_chain_nofirst = List.tl lvid_chain in

  (* We sum the latency over the chain - assume a normalized program *)
  let diff_ocks ock ock_e1 =
    let (ophid, laffterm, sh, _, per) = extract_ock_info ock in
    let (ophid1, laffterm1, sh1, _, per1) = extract_ock_info ock_e1 in

    assert(per=per1);
    let shdiff = sh - sh1 in
    
    let laffterm1_minus = List.map (fun (c,v) -> (-c,v)) laffterm1 in
    let lafftermdiff = List.fold_left (fun lacc term ->
      add_term term lacc
    ) laffterm laffterm1_minus in
    let lafftermdiff = match ophid with
      | None -> lafftermdiff
      | Some phid -> add_term (1,  phid) lafftermdiff
    in
    let lafftermdiff = match ophid1 with
      | None -> lafftermdiff
      | Some phid -> add_term (-1, phid) lafftermdiff
    in
    let lafftermdiff = List.map (fun (c,v) ->
      (c, varname_from_phase_index v)
    ) lafftermdiff in
    (lafftermdiff, shdiff)
  in

  let (lcoeff_lat, cst_lat) = List.fold_left (fun (lcoeff_acc, cst_acc) vid ->
    let eqm = Env.find vid mVar2Eq in
    let ock = eqm.eqm_clk in

    (* Terms potentially introduced *)
    let onterm = match eqm.eqm_rhs.e_desc with
      | Econst _ ->
        failwith "Internal error - constant equation should not happen in latency chain"
      | Elast _ ->
        failwith "Model_clocking::add_latency_chain_constraint : unsure on how to manage last"
      | Ewhen _ | Emerge _ | Ecurrent _ ->
        failwith "Ewhen/Ecurrent/Emerge shoud not appear in a block_model"
      
      | Evar _ | Estruct _ | Esplit _ | Eapp _ | Eiterator _ -> None
      
      (* Period-changing operators are instantaneous *)
      | Ewhenmodel _ | Ecurrentmodel _ | Ewhenq _ | Ecurrentq _ -> None

      | Epre _ | Efby _ -> (* We add the period *)
        let per = get_period_ock ock in
        Some ([], per)
      
      | Edelay (d,_) | Edelayfby (d, _, _) ->
        Some ([], d)
      
      | Ebuffer e1 | Ebufferfby (_, e1) | Ebufferlat (_, e1) ->
        (* Normalization => e1 must be a var or a constant / no sense of having a constant *)
        let vid_e1 = assert_Evar e1 in
        let ock_e1 = try Env.find vid_e1 mvar_ock
          with Not_found -> failwith ("Variable " ^ (Idents.name vid_e1) ^ " not found in mvar_ock.")
        in

        (* DEBUG
        fprintf ffout "\neqm = %a | vid_e1 = %a\n@?" Hept_printer.print_eq_model eqm  print_ident vid_e1;
        fprintf ffout "ock = %a | ock_e1 = %a\n@?" print_oneck ock  print_oneck ock_e1; *)

        (* Lattency introduced : "ock - ock_e1" *)
        let (lafftermdiff, shdiff) = diff_ocks ock ock_e1 in
        Some (lafftermdiff, shdiff)

      | Efbyq _ ->
       (* Remark: mdecvar : [name of first lhs var
          -> decision variable name associated to the underspecified op on the right] *)
        let vidlhs = get_first_var eqm.eqm_lhs in
        let decvar = Env.find vidlhs mdecvar in
        let per = get_period_ock ock in

        let laffterm = (per, decvar)::[] in
        Some (laffterm, 0)
      | Ebufferfbyq (_, e1) ->
        let vid_e1 = assert_Evar e1 in
        let ock_e1 = try Env.find vid_e1 mvar_ock
          with Not_found -> failwith ("Variable " ^ (Idents.name vid_e1) ^ " not found in mvar_ock.")
        in
        (* Lattency introduced : "ock - ock_e1" *)
        let (lafftermdiff, shdiff) = diff_ocks ock ock_e1 in

        (* Adding the potential "+per" the decision variable might have introduced *)
        let vidlhs = get_first_var eqm.eqm_lhs in
        let decvar = Env.find vidlhs mdecvar in
        let per = get_period_ock ock in
        let lafftermdiff = add_term (per, decvar) lafftermdiff in

        Some (lafftermdiff, shdiff)
    in


    (* DEBUG
    (match onterm with
      | None -> fprintf ffout "vid = %a ==> onterm = None\n@?" print_ident vid
      | Some (term, cst) -> fprintf ffout "vid = %a ==> onterm = Some (%a, %i)\n@?"
        print_ident vid  (print_affterm ~bfirst:true) term  cst
    );*)

    (* Add the new contributions to the old ones *)
    let (lcoeff_acc, cst_acc) = match onterm with
      | None -> (lcoeff_acc, cst_acc)
      | Some (laffterm, cst) ->
        let cst_acc = cst + cst_acc in
        let lcoeff_acc = List.fold_left (fun lacc term ->
          add_term term lacc
        ) lcoeff_acc laffterm in
        (lcoeff_acc, cst_acc)
    in
    (lcoeff_acc, cst_acc)
  ) ([],0) lvid_chain_nofirst in


  (*  lcoeff_lat + cst_lat <= lat  ===> -lcoeff_lat >= cst_lat-lat *)
  let lcoeff_lat_minus = List.map (fun (c,v) -> (-c, v)) lcoeff_lat in
  let ac_latency = mk_affconstr false lcoeff_lat_minus (cst_lat-lat) in

  (* DEBUG
  fprintf ffout "ac_latency = %a\n@?" print_aff_constr ac_latency; *)

  (* Note: substitutions are performed after that part *)

  (* Wrapping things up *)
  let (lac_acc, lbc_acc) = lcst_acc in
  let nlcst_acc = (ac_latency::lac_acc, lbc_acc) in
  nlcst_acc


(* Constraints from annotation management *)
let add_constraint_from_annot mdecvar mvar_ock lcst eqm_list lbann =
  (* Constraints from equations *)
  (* mlabel : label -> ock / associate a label with the ock info *)
  let (lcst, mlabel) = List.fold_left (fun (lcst_acc, mlabel) eqm ->
    let (ophid, laffterm, sh, _, per) = extract_ock_info eqm.eqm_clk in

    List.fold_left (fun (lcst_acc, mlabel) eqmann ->
      let (lac, lbc) = lcst_acc in
      match eqmann.anneqm_desc with
      | Anneqm_minphase mphase ->
        (assert(mphase<per); assert(mphase>=0);
        match ophid with
          | None ->
            if (mphase > sh) then (
              eprintf "%aIn equation (%a), minphase annotation cannot be respected (clock is %a)\n@?"
                print_location eqm.eqm_loc Hept_printer.print_eq_model eqm  print_oneck eqm.eqm_clk;
              failwith "Minimal phase constraint is not respected by constant clock."
            );
            (lcst_acc, mlabel)
          | Some phid ->
            (* Create constraint phid+laffterm >= mphase-sh *)
            let lcoeffVar = (1, (varname_from_phase_index phid))::[] in
            let lcoeffVar = List.fold_left (fun acc (c,v) ->
              (c, varname_from_phase_index v)::acc
            ) lcoeffVar laffterm in
            let ac = mk_affconstr false lcoeffVar (mphase-sh) in
            ((ac::lac, lbc), mlabel)
        )
      | Anneqm_maxphase mphase ->
        (assert(mphase<per); assert(mphase>=0);
        match ophid with
          | None ->
            if (mphase < sh) then (
              eprintf "%aIn equation (%a), maxphase annotation cannot be respected (clock is %a)\n@?"
                print_location eqm.eqm_loc Hept_printer.print_eq_model eqm  print_oneck eqm.eqm_clk;
              failwith "Maximal phase constraint is not respected by constant clock."
            );
            (lcst_acc, mlabel)
          | Some phid ->
            (* Create constraint phid+laffterm+sh <= maxphase , aka -phid-laffterm >= sh-maxphase *)
            let lcoeffVar = ((-1), (varname_from_phase_index phid))::[] in
            let lcoeffVar = List.fold_left (fun acc (c,v) ->
              (-c, varname_from_phase_index v)::acc
            ) lcoeffVar laffterm in
            let ac = mk_affconstr false lcoeffVar (sh-mphase) in
            ((ac::lac, lbc), mlabel)
        )
      | Anneqm_label ln ->
        (lcst, StringMap.add ln eqm.eqm_clk mlabel)
    ) (lcst_acc, mlabel) eqm.eqm_annot
  ) (lcst, StringMap.empty) eqm_list in

  let mVar2Eq = List.fold_left (fun macc eqm ->
    let lvarlhs = get_vars_lhs eqm.eqm_lhs in
    List.fold_left (fun macc varid -> Idents.Env.add varid eqm macc) macc lvarlhs
  ) Idents.Env.empty eqm_list in

  (* Constraint from block *)
  let lcst = List.fold_left (fun lcst_acc bmann -> match bmann.annm_desc with
    (* Low/Upper bound the phase between 2 equations on same period *)
    | Ann_range (l, u, lab1, lab2) -> begin
      let ock1 = try StringMap.find lab1 mlabel
        with Not_found ->
        failwith ("Equation of label " ^ lab1 ^ " was not found.")
      in
      let ock2 = try StringMap.find lab2 mlabel
        with Not_found ->
        failwith ("Equation of label " ^ lab2 ^ " was not found.")
      in
      let (ophid1, laffterm1, sh1, _, per1) = extract_ock_info ock1 in
      let (ophid2, laffterm2, sh2, _, per2) = extract_ock_info ock2 in
      assert(per1=per2);   (* Same period... should we keep that condition ? *)
      let diff = sh2 - sh1 in
      let laffterm2m1 = substract_laffterm laffterm2 laffterm1 in

      let (lac,lbc) = lcst_acc in
      (match (ophid1, ophid2) with
        | (None, None) ->
          if (laffterm2m1=[]) then
            (if (diff<l) then (
              eprintf "%aIn constraint (%a), min is not respected (lab1.ock = %a | lab2.ock = %a)\n@?"
                print_location bmann.annm_loc  Hept_printer.print_annot_model bmann
                print_oneck ock1  print_oneck ock2;
              failwith "Minimal phase difference constraint is not respected by constant clocks."
            );
            if (diff>u) then (
              eprintf "%aIn constraint (%a), max is not respected (lab1.ock = %a | lab2.ock = %a)\n@?"
                print_location bmann.annm_loc  Hept_printer.print_annot_model bmann
                print_oneck ock1  print_oneck ock2;
              failwith "Maximal phase difference constraint is not respected by constant clocks."
            );
            lcst_acc)
          else (
            (* Constraint: laffterm2m1 >= l-diff *)
            let lcoeffVar1 = List.map (fun (c,v) -> (c, varname_from_phase_index v)) laffterm2m1 in
            let ac1 = mk_affconstr false lcoeffVar1 (l-diff) in

            (* Constraint: u >= laffterm2m1+diff => -laffterm2m1 >= diff-u *)
            let lcoeffVar2 = List.map (fun (c,v) -> (-c, varname_from_phase_index v)) laffterm2m1 in
            let ac2 = mk_affconstr false lcoeffVar2 (diff-u) in

            (ac1::ac2::lac, lbc)
          )
        | (None, Some phid2) ->
          let varph2 = varname_from_phase_index phid2 in

          (* Constraint: varph2 + laffterm2m1 >= l- diff *)
          let lcoeffVar1 = (1,varph2)::[] in
          let lcoeffVar1 = List.fold_left (fun acc (c,v) ->
            (c, varname_from_phase_index v)::acc
          ) lcoeffVar1 laffterm2m1 in
          let ac1 = mk_affconstr false lcoeffVar1 (l-diff) in

          (* Constraint: u >= varph2 + laffterm2m1 + diff  ==>  -varph2 - laffterm2m1 >= diff-u *)
          let lcoeffVar2 = ((-1),varph2)::[] in
          let lcoeffVar2 = List.fold_left (fun acc (c,v) ->
            (-c, varname_from_phase_index v)::acc
          ) lcoeffVar2 laffterm2m1 in
          let ac2 = mk_affconstr false lcoeffVar2 (diff-u) in

          (ac1::ac2::lac, lbc)
        | (Some phid1, None) ->
          let varph1 = varname_from_phase_index phid1 in

          (* Constraint: diff - varph1 + laffterm2m1 >=l  *)
          let lcoeffVar1 = ((-1),varph1)::[] in
          let lcoeffVar1 = List.fold_left (fun acc (c,v) ->
            (c, varname_from_phase_index v)::acc
          ) lcoeffVar1 laffterm2m1 in
          let ac1 = mk_affconstr false lcoeffVar1 (l-diff) in

          (* Constraint: u >= diff - varph1 + laffterm2m1 *)
          let lcoeffVar2 = (1,varph1)::[] in
          let lcoeffVar2 = List.fold_left (fun acc (c,v) ->
            (-c, varname_from_phase_index v)::acc
          ) lcoeffVar2 laffterm2m1 in
          let ac2 = mk_affconstr false lcoeffVar2 (diff-u) in

          (ac1::ac2::lac, lbc)
        | (Some phid1, Some phid2) ->
          let varph1 = varname_from_phase_index phid1 in
          let varph2 = varname_from_phase_index phid2 in

          (* Constraint: varph2 - varph1 + laffterm2m1 + diff >=l  *)
          let lcoeffVar1 = (1,varph2)::((-1),varph1)::[] in
          let lcoeffVar1 = List.fold_left (fun acc (c,v) ->
            (c, varname_from_phase_index v)::acc
          ) lcoeffVar1 laffterm2m1 in
          let ac1 = mk_affconstr false lcoeffVar1 (l-diff) in

          (* Constraint: u >= varph2 - varph1 + laffterm2m1 + diff *)
          let lcoeffVar2 = ((-1),varph2)::(1,varph1)::[] in
          let lcoeffVar2 = List.fold_left (fun acc (c,v) ->
            (-c, varname_from_phase_index v)::acc
          ) lcoeffVar2 laffterm2m1 in
          let ac2 = mk_affconstr false lcoeffVar2 (diff-u) in

          (ac1::ac2::lac, lbc)
      )
    end
    
    (* Precedence constraint on the phase *)
    | Ann_before (lab1, lab2) -> begin
      let ock1 = try StringMap.find lab1 mlabel
        with Not_found ->
        failwith ("Equation of label " ^ lab1 ^ " was not found.")
      in
      let ock2 = try StringMap.find lab2 mlabel
        with Not_found ->
        failwith ("Equation of label " ^ lab2 ^ " was not found.")
      in
      let (ophid1, laffterm1, sh1, _, per1) = extract_ock_info ock1 in
      let (ophid2, laffterm2, sh2, _, per2) = extract_ock_info ock2 in
      assert(per1=per2);   (* Same period... should we keep that condition ? *)
      let diff = sh2 - sh1 in
      let laffterm2m1 = substract_laffterm laffterm2 laffterm1 in

      (* TODO - add laffterm2m1 contrib here !!! *)

      let (lac,lbc) = lcst_acc in
      (match (ophid1, ophid2) with
        | (None, None) ->
          if (laffterm2m1=[]) then (
            if (diff<0) then (
              eprintf "%aIn constraint (%a), precedence is not respected (lab1.ock = %a | lab2.ock = %a)\n@?"
                print_location bmann.annm_loc  Hept_printer.print_annot_model bmann
                print_oneck ock1  print_oneck ock2;
              failwith "Precedence constraint is not respected by constant clocks."
            );
            lcst_acc
          ) else (
            (* Constraint: laffterm2m1 + diff >= 0 *)
            let lcoeffVar1 = List.map (fun (c,v) -> (c, varname_from_phase_index v)) laffterm2m1 in
            let ac = mk_affconstr false lcoeffVar1 (-diff) in
            (ac::lac, lbc)
          )
        | (None, Some phid2) ->
          let varph2 = varname_from_phase_index phid2 in

          (* Constraint: varph2+laffterm2m1 >= - diff *)
          let lcoeffVar = (1,varph2)::[] in
          let lcoeffVar = List.fold_left (fun acc (c,v) ->
            (c, varname_from_phase_index v)::acc
          ) lcoeffVar laffterm2m1 in
          let ac = mk_affconstr false lcoeffVar (-diff) in
          (ac::lac, lbc)

        | (Some phid1, None) ->
          let varph1 = varname_from_phase_index phid1 in

          (* Constraint: diff - varph1 + laffterm2m1 >= 0  *)
          let lcoeffVar = ((-1),varph1)::[] in
          let lcoeffVar = List.fold_left (fun acc (c,v) ->
            (c, varname_from_phase_index v)::acc
          ) lcoeffVar laffterm2m1 in
          let ac = mk_affconstr false lcoeffVar (-diff) in
          (ac::lac, lbc)

        | (Some phid1, Some phid2) ->
          let varph1 = varname_from_phase_index phid1 in
          let varph2 = varname_from_phase_index phid2 in
          
          (* Constraint: varph2 - varph1 + laffterm2m1 + diff >= 0 *)
          let lcoeffVar = (1,varph2)::((-1),varph1)::[] in
          let lcoeffVar = List.fold_left (fun acc (c,v) ->
            (c, varname_from_phase_index v)::acc
          ) lcoeffVar laffterm2m1 in
          let ac = mk_affconstr false lcoeffVar (-diff) in
          (ac::lac, lbc)
      )
    end

    | Ann_latchain (lat, lvid_chain) ->
      add_latency_chain_constraint mdecvar mVar2Eq mvar_ock lat lvid_chain lcst_acc
  ) lcst lbann in

  lcst


(* ----- *)
(* ----- *)
(* Substitution management *)

let rec reorient_lsubst lsubst = match lsubst with
  | [] -> []
  | (blsubstr, n1, None, sh, laffterm)::r ->
    (n1, None, sh, laffterm)::(reorient_lsubst r)
  | (blsubstr, n1, Some n2, sh, laffterm)::r ->
    if blsubstr then
      (n1, (Some n2), sh, laffterm)::(reorient_lsubst r)
    else
      (n2, (Some n1),(-sh), negate_laffterm laffterm)::(reorient_lsubst r)

let rec unroll_substitution msubst sh laffterm phid =
  try
    let (ophid2, sh2, laffterm2) = StringMap.find phid msubst in
    let laffterm12 = List.fold_left (fun lacc (a,v) ->
      add_term (a,v) lacc
    ) laffterm laffterm2 in
    match ophid2 with
    | None -> (None, sh+sh2, laffterm12)
    | Some phid2 -> unroll_substitution msubst (sh+sh2) laffterm12 phid2
  with
  | Not_found -> (Some phid, sh, laffterm)

let closure_subst msubst =
  let msubst = StringMap.fold (fun phid1 (optphid2, sh, laffterm) macc ->
    match optphid2 with
    | None -> StringMap.add phid1 (optphid2, sh, laffterm) macc
    | Some phid2 ->
      let (optphid_unr, sh_unr, laffterm_unr) = unroll_substitution msubst sh laffterm phid2 in
      StringMap.add phid1 (optphid_unr, sh_unr, laffterm_unr) macc
  ) msubst StringMap.empty in
  msubst


(* Update the constraints from lcst, depending on the substitution
  obtained from the unification process at the equation level *)
let update_lcst msubst (lcst,lbcst) =
  let lcst = List.map (fun cst ->
    let cst = List.fold_left (fun constr (coeff,var) -> 
      try
        let (optphid2, sh, laffterm) = StringMap.find var msubst in
        let constr = subst_constraint (var, optphid2, laffterm, sh) constr in
        constr
      with
      | Not_found -> constr
    ) cst cst.lcoeffVar in
    cst
  ) lcst in

  (* DEBUG
  fprintf ffout "lbcst = %a\n@?" print_list_bound_constr lbcst;
  fprintf ffout "msubst = %a\n@?" print_msubst msubst; *)

  let rec pop_boundary_constraint var lbcst = match lbcst with
    | [] -> raise Not_found (* Because some variable comes from subexpressions *)
    | h::t ->
      if (h.varName=var) then (h,t) else
      let (bcst, nt) = pop_boundary_constraint var t in
      (bcst,h::nt)
  in

  let rec update_bound_constraint var2 sh bconst1 lbcst = match lbcst with
    | [] -> failwith "Boundary constraint not found (update)"
    | h::t ->
      if (h.varName=var2) then
        let nh = { h with lbound = max h.lbound (bconst1.lbound - sh);
                          ubound = min h.ubound (bconst1.ubound - sh);
        } in
        nh::t
      else
        h::(update_bound_constraint var2 sh bconst1 t)
  in

  let (lcst, lbcst) = StringMap.fold (fun k (optvarph2, sh, laffterm2) (acc_lac, acc_lbc) ->
    (* Propagate the substitution from msubst to the boundary constraints *)
    (* k is replaced by the infos in (optvarph2, sh)
        => propagate the bound constraint from k in the bound contraint of (optvarph2, sh)
        => then remove the bound contraint of k *)
    try
      let (bconst, acc_lbc) = pop_boundary_constraint k acc_lbc in

      if (laffterm2=[]) then (
        let acc_lbc = match optvarph2 with
          | None ->
            assert(bconst.lbound <= sh);
            assert(bconst.ubound > sh);
            acc_lbc
          | Some var2 -> update_bound_constraint var2 sh bconst acc_lbc
        in
        (acc_lac, acc_lbc)
      ) else (
        (* We build 2 affine constraints here, instead of a boundary constraint *)
        (* l<= optvarph2 + sh + laffterm2 <=u *)

        (* First constraint: optvarph2 + laffterm2 >= l-sh *)
        let lcoeffVar1 = match optvarph2 with
          | None -> []
          | Some varph2 -> (1,varph2)::[]
        in
        let lcoeffVar1 = List.fold_left (fun acc (c,v) -> (c, v)::acc) lcoeffVar1 laffterm2 in
        let ac1 = mk_affconstr false lcoeffVar1 (bconst.lbound-sh) in

        (* Second constraint: - optvarph2 - laffterm2 >= sh-u+1 *)
        let lcoeffVar2 = match optvarph2 with
          | None -> []
          | Some varph2 -> ((-1),varph2)::[]
        in
        let lcoeffVar2 = List.fold_left (fun acc (c,v) -> (-c, v)::acc) lcoeffVar2 laffterm2 in
        let ac2 = mk_affconstr false lcoeffVar2 (sh-bconst.ubound+1) in

        (ac1::ac2::acc_lac, acc_lbc)
      )
    with Not_found -> (acc_lac, acc_lbc)  (* TODO: check that *)
  ) msubst (lcst, lbcst) in
  (lcst,lbcst)


(* ----- *)
(* ----- *)

(* Get the wcet and ressources of a function *)
let get_wcet_ressource funname =
  try
    let sign = Modules.find_value funname in
    (sign.node_wcet, sign.node_ressource)
  with Not_found -> (None, [])

(* Build the wcet mapping - useful for the load balancing cost function *)
(* Assume normalisation of the program *)
let build_wcet_info leqms =
  let lwcet = List.fold_left (fun lwacc eqm ->
    match eqm.eqm_rhs.e_desc with
      | Eapp (a, _, _) -> begin match a.a_op with
        | Efun fn | Enode fn -> (
          let (ow, lress) = get_wcet_ressource fn in

          (* Default case - nothing to see there *)
          if ((ow=None) && (lress=[])) then lwacc else

          (* Else, register information *)
          let (ophid, laffterm, sh, _, per) = Clocks.extract_ock_info eqm.eqm_clk in
          let ovarph = match ophid with
            | None -> None
            | Some phid -> Some (varname_from_phase_index phid)
          in
          let laffterm = List.map (fun (c,v) ->
            (c,varname_from_phase_index v)
          ) laffterm in
          (ovarph, laffterm, sh, per, ow, lress)::lwacc
        )
        | _ -> lwacc
      end
      | _ -> lwacc
  ) [] leqms in
  lwcet

(* Update the wcet using the msubst done in the block *)
let update_wcet msubst lwcet =
  List.map (fun (ovarname, laffterm, sh, per, owcet, lress) -> match ovarname with
    | None -> (None, laffterm, sh, per, owcet, lress)
    | Some varname ->
    try
      let (ovarname2, sh2, laffterm2) = StringMap.find varname msubst in
      let laffterm12 = List.fold_left (fun lacc (a,v) ->
        add_term (a,v) lacc
      ) laffterm laffterm2 in
      (ovarname2, laffterm12, sh+sh2, per, owcet, lress)
    with
      | Not_found -> (ovarname, laffterm, sh, per, owcet, lress)
  ) lwcet

(* Pretty-printer for debugging *)
let print_elem_lwcet ff (ovarph, laffterm, sh, per, owcet, lress) =
  let print_opt_string ff ovarph = match ovarph with
    | None -> fprintf ff "None"
    | Some varph -> fprintf ff "%s" varph
  in
  let print_opt_int ff owcet = match owcet with
    | None -> fprintf ff "None"
    | Some w -> fprintf ff "%i" w
  in
  let print_ress ff (n,v) = fprintf ff "(%s, %i)" n v in
  fprintf ff "\t(%a + %a + %i, per = %i => wcet = %a | ress = %a);"
    print_opt_string ovarph
    (Affine_constraint_clocking.print_affterm ~bfirst:true) laffterm
    sh per
    print_opt_int owcet
    (Pp_tools.print_list print_ress "(" "" ")") lress

let print_lwcet ff (lwcet: (string option * ((int * string) list) * int * int * (int option) * (string * int) list) list) =
  fprintf ff "lwcet = %a\n@?"
    (Pp_tools.print_list print_elem_lwcet "[" "" "]") lwcet


(* ----- *)
(* ----- *)


(* Typing model equations  *)
let rec typing_model_eq h lcst eqm =
  if (debug_clocking) then
    fprintf ffout "Entering model equation %a@\n" Hept_printer.print_eq_model eqm;

  let (oct, lcst, lsubst_rhs, odecvar) = typing_osych h lcst eqm.eqm_lhs eqm.eqm_rhs in
  let pat_oct = typing_model_pat h eqm.eqm_lhs in

  let (lcst, lsubst_eq) = (try
    (* For debugging *)
    if (debug_clocking) then 
      fprintf ffout "unification between pat => %a and rhs => %a\n"
        print_onect pat_oct  print_onect oct;

    let (lsubst_eq, lconstr_decvar_unif) :
          ((bool * int * int option * int * (int*int) list) list)
            * ( (int*int) list * int) list = unify_onect_constr oct pat_oct in
    
    let lac_decvar = List.map (fun (laffterm_int, cst_term) ->
      let lcoeffVar = List.map (fun (c,v) -> (c, varname_from_phase_index v)) laffterm_int in
      mk_affconstr true lcoeffVar cst_term
    ) lconstr_decvar_unif in

    let (lac,lbc) = lcst in
    ((List.rev_append lac_decvar lac,lbc), lsubst_eq)
  with Unify ->
    eprintf "Incoherent clock between right and left side of the equation:@\n\t%a\nlhs :: %a  | rhs :: %a.@\n"
     Hept_printer.print_eq_model eqm print_onect pat_oct  print_onect oct;
    error_message eqm.eqm_loc (Etypeclash (oct, pat_oct))
  ) in


  let lsubst = List.rev_append lsubst_rhs lsubst_eq in
  let lsubst : (int * int option * int * (int*int) list) list = reorient_lsubst lsubst in

  (* For debugging *)
  if (debug_clocking) then 
    fprintf ffout "\tlsubst = %a\n@?" print_lsubst lsubst;


  (* Using a ? operator on a equation which returns nothing is useless
    => we assume this does not happen and use the first variable of the lhs
       to associate the decision variable to the equation *)
  let omatch_decvar = match odecvar with
   | None -> None
   | Some decvar ->
      let firstvarlhs = get_first_var eqm.eqm_lhs in
      Some (firstvarlhs, decvar)
  in
  (lcst, lsubst, omatch_decvar)

and typing_model_eqs h lcst eq_list =
  List.fold_left (fun (lcst_acc, lsubst_acc, mdecvar) eqm ->
    let (lcst, lsubst, omatch_decvar) = typing_model_eq h lcst_acc eqm in
    let mdecvar = match omatch_decvar with
      | None -> mdecvar
      | Some (k,v) -> Env.add k v mdecvar
    in
    (lcst, lsubst @ lsubst_acc, mdecvar)
  ) (lcst,[], Env.empty) eq_list

(* Block management *)
and append_model_env h lcst vdms =
  let (h, lcst) = List.fold_left (fun (h,lcst) { vm_ident = n; vm_clock = ock } ->
    (* Create a new boundary condition from ock, if phase variable *)
    let (varopt, laffterm,  ph) = Clocks.get_phase_ock ock in
    
    let nlaffcst = if (laffterm=[]) then (
      (* First pass should always go there *)

      (* We add the boundary constraint on the variable *)
      match varopt with
        | None -> lcst   (* The check that the phase is valid was done during parsing *)
        | Some varid ->
          let varname = varname_from_phase_index varid in
          let per = get_period_ock ock in

          let bcond = mk_bound_constr varname (-ph) (per-ph) in
          let (laffcst, lbndcst) = lcst in
          (laffcst, bcond::lbndcst)
    ) else (
      (* 0 <= phase_var *)
      let laffterm_ac1 = match varopt with
        | None -> []
        | Some varid -> (1, varname_from_phase_index varid)::[]
      in
      let laffterm_ac1 = List.fold_left (fun lacc (c,v) ->
        (c, varname_from_phase_index v)::lacc
      ) laffterm_ac1 laffterm in
      let ac_1 = mk_affconstr false laffterm_ac1 0 in

      (* phase_var < per *)
      let per = get_period_ock ock in
      let laffterm_ac2 = match varopt with
        | None -> []
        | Some varid -> (-1, varname_from_phase_index varid)::[]
      in
      let laffterm_ac2 = List.fold_left (fun lacc (c,v) ->
        (-c, varname_from_phase_index v)::lacc
      ) laffterm_ac2 laffterm in
      let ac_2 = mk_affconstr false laffterm_ac2 (1-per) in


      let (laffcst, lbndcst) = lcst in
      (ac_1::ac_2::laffcst, lbndcst)
    ) in

    (* Update h *)
    let nh = Env.add n ock h in
    (nh, nlaffcst)
  ) (h,lcst) vdms in
  (h, lcst)


and typing_block_model h lcst {bm_local = l; bm_eqs = eq_list; bm_annot = lbann} =
  let (h1, lcst) = append_model_env h lcst l in

  if (debug_clocking) then
    fprintf ffout "Entering block_model - Environment is:\n%a@\n" print_henv h1;

  (* mdecvar : [name of first lhs var -> decision variable name associated to the underspecified op on the right] *)
  let (lcst, lsubst, mdecvar) = typing_model_eqs h1 lcst eq_list in

  if (debug_clocking) then (
    fprintf ffout "DEBUG-typing_model_eq - constraints =\n %a\n@?"
      print_constraint_environment lcst (*;
    fprintf ffout "lsubst = %a@?" print_lsubst lsubst *)
  );

  (* Adding the constraints from the annotations *)
  let (lcst: (affconstr list) * (boundconstr list)) = add_constraint_from_annot mdecvar h1 lcst eq_list lbann in


  (* DEBUG *)
  if (debug_clocking) then (
    fprintf ffout "DEBUG-typing_model_eq - annotation constraints added\n@?"
  );

  (* If there is decision variable, add constraints for causality *)
  let lcst = if (Env.is_empty mdecvar) then lcst else
    add_causality_constraint lcst mdecvar eq_list
  in

  (* DEBUG *)
  if (debug_clocking) then (
    fprintf ffout "DEBUG-typing_model_eq - causality constraints added\n@?"
  );


  (* Manages subtitutions *)
  let msubst = List.fold_left (fun macc (phid1, optphid2, sh, laffterm) ->
    let varph1 = varname_from_phase_index phid1 in
    let optvarph2 = match optphid2 with
      | None -> None
      | Some phid2 -> Some (varname_from_phase_index phid2)
    in
    let laffterm = List.map (fun (c,vid) ->
      (c,varname_from_phase_index vid)
    ) laffterm in
    StringMap.add varph1 (optvarph2, sh, laffterm) macc
  ) StringMap.empty lsubst in
  
  (* Closure on the substitutions of msubst *)
  let msubst = closure_subst msubst in

  (* Update constraints with substitutions *)
  let lcst = update_lcst msubst lcst in

  if (debug_clocking) then (
    fprintf ffout "DEBUG-typing_model_eq - constraints =\n %a\n@?"
      print_constraint_environment lcst;

    fprintf ffout "DEBUG-typing_model_eq - msubst =\n %a\n@?"
      print_msubst msubst;
  );

  (* Build the wcet mapping - useful for the load balancing cost function *)
  (* lwcet : (potential phase_variable_name, list of affine terms, shift of ock, period of ock,
                    potential assigned WCET, list of ressources used *)
  let (lwcet : (string option * ((int * string) list) * int * int
                  * (int option) * (string * int) list) list) = build_wcet_info eq_list in

  (* Substitute infos in lwcet using msubst *)
  let lwcet = update_wcet msubst lwcet in

  (* TODO DEBUG *)
  if (debug_clocking) then print_lwcet ffout lwcet;

  (h1, lcst, msubst, lwcet, mdecvar)


(* ----- *)
(* ----- *)

(* Substitution of the phase solution in the program *)
let enrich_sol_with_msubst msubst msol =
  let msol = StringMap.fold (fun k (ov, sh, laffterm) msol_acc ->
    (* msubst was already closure-ed => no need for recursion *)
    let val_k = sh in
    let val_k = match ov with
      | None -> val_k
      | Some v2 ->
        let val_v2 = StringMap.find v2 msol in
        val_v2 + val_k
    in
    let val_k = List.fold_left (fun accval (c,vafft) ->
      let val_vafft = StringMap.find vafft msol in
      accval + c * val_vafft
    ) val_k laffterm in

    (* Enriching msol with the new value for the var which was substituted *)
    StringMap.add k val_k msol_acc
  ) msubst msol in
  msol

let rec subst_solution msol ock =
  let rec aux_phase_subst_solution msol oph = match oph with
    | Cophase ph -> ph
    | Cophshift (sh, phid) ->
      let ph_val = try IntMap.find phid msol
        with Not_found -> failwith ("Subst_solution: phase " ^ (string_of_int phid) ^ " was not found.")
      in
      ph_val+sh
    | Cophindex phid -> (* 'a *)
      let ph_val = try IntMap.find phid msol
        with Not_found -> failwith ("Subst_solution: phase " ^ (string_of_int phid) ^ " was not found.")
      in
      ph_val
    | Cophlinexp ((c,v), noph) ->
      let ph_val_noph = aux_phase_subst_solution msol noph in
      let val_v = try IntMap.find v msol
        with Not_found -> failwith ("Subst_solution: phase " ^ (string_of_int v) ^ " was not found.")
      in
      (c * val_v + ph_val_noph)
  in
  let ock_subst = match ock with
  | Cone _ -> ock
  | Cshift (sh, ock1) ->
    let ock1 = subst_solution msol ock1 in
    ock_repr (Cshift (sh, ock1))
  | Covar { contents = ol } -> (match ol with
    | Coindex _ ->
      failwith "Internal error: Period and phase unknown during solution substitution"
    | Colink ock -> subst_solution msol ock
    | Coper ({ contents = op }, per) ->
      let val_op = aux_phase_subst_solution msol op in
      Cone (val_op, per)
    )
  in
  (* Double check that the clock is correct *)
  let (ph,per) = get_ph_per_from_ock ock_subst in
  (* DEBUG
    fprintf ffout "ock = %a\n@?" print_oneck ock; *)
  assert(0<=ph);
  assert(ph<per);

  ock_subst

let eq_model_replace _ (hfull,msol,mdecvar) eqm =
  let ock_eq = subst_solution msol eqm.eqm_clk in
  let (ph_eq, per_eq) = get_ph_per_from_ock ock_eq in

  let rhs = eqm.eqm_rhs in

  (* Determinisation pass *)
  (* We recover the decision variable and use it to determinize the operators*)
  let get_dec_var_sol mdecvar msol plhs =
    let firstvarname = get_first_var eqm.eqm_lhs in
    let (decvar:string) = try
      Env.find firstvarname mdecvar
      with Not_found -> failwith ("Internal error: equation defining " ^ (Idents.name firstvarname)
            ^ " is not associated with a decision variable.")
    in
    let (soldecvar:int) = try
        IntMap.find (get_phase_index_from_varname decvar) msol
      with Not_found -> failwith ("Internal error: declaration variable " ^ decvar
            ^ " is not included in the solution.")
    in
    soldecvar
  in

  let rhs = match rhs.e_desc with
    | Efbyq (seInit, e) ->
        let soldecvar = get_dec_var_sol mdecvar msol eqm.eqm_lhs in
        (* soldecvar = 0 => no fby / soldecvar = 1 => fby *)
        if (soldecvar=0) then e else (
          assert(soldecvar=1);
          { rhs with e_desc = Epre (Some seInit, e) }
        )

    | Ebufferfbyq (seInit, e) ->
        let soldecvar = get_dec_var_sol mdecvar msol eqm.eqm_lhs in
        (* soldecvar = 0 => buffer no fby / soldecvar = 1 => bufferfby *)
        if (soldecvar=0) then
          { rhs with e_desc = Ebuffer e }
        else (
          assert(soldecvar=1);
          { rhs with e_desc = Ebufferfby (seInit, e) }
        )

    | Ewhenq (e, (min,max), ratio) -> (
        let soldecvar = get_dec_var_sol mdecvar msol eqm.eqm_lhs in
        assert(min<=soldecvar); assert(soldecvar<=max);  (* Double-checking*)
        { rhs with e_desc = Ewhenmodel (e, (soldecvar, ratio)) }
      )
    | Ecurrentq (ratio, (min,max), seInit, e) -> (
        let soldecvar = get_dec_var_sol mdecvar msol eqm.eqm_lhs in
        assert(min<=soldecvar); assert(soldecvar<=max);  (* Double-checking*)
        { rhs with e_desc = Ecurrentmodel ((soldecvar, ratio), seInit, e) }
      )
    | _ -> rhs
  in

  (* We assume normalization here *)
  let rhs = match rhs.e_desc with
    | Ebuffer e ->
      let varid = assert_Evar e in
      let ock_sexp = Env.find varid hfull in
      let ock_sexp = subst_solution msol ock_sexp in

      let (ph_sexp, per_sexp) = get_ph_per_from_ock ock_sexp in

      (* DEBUG
      fprintf ffout "eqm ::: %a\n@?" Hept_printer.print_eq_model eqm;
      fprintf ffout "ph_eq = %i | ph_sexp = %i\n@?" ph_eq ph_sexp; *)

      assert(per_eq = per_sexp);
      assert(ph_eq >= ph_sexp);
      let d = ph_eq - ph_sexp in

      if (d>0) then
        { rhs with e_desc = Edelay(d, e) }
      else
        e
    | Ebufferfby (seInit, e) ->
      let varid = assert_Evar e in
      let ock_sexp = Env.find varid hfull in
      let ock_sexp = subst_solution msol ock_sexp in
      
      let (ph_sexp, per_sexp) = get_ph_per_from_ock ock_sexp in
      assert(per_eq = per_sexp);
      assert(ph_eq < ph_sexp);
      let d = ph_eq - ph_sexp + per_eq in

      { rhs with e_desc = Edelayfby(d, seInit, e) }
    | Ebufferlat (l, e) ->
      let varid = assert_Evar e in
      let ock_sexp = Env.find varid hfull in
      let ock_sexp = subst_solution msol ock_sexp in

      let (ph_sexp, per_sexp) = get_ph_per_from_ock ock_sexp in
      assert(per_eq = per_sexp);
      assert(ph_eq >= ph_sexp);
      let d = ph_eq - ph_sexp in
      assert(l>=d);

      if (d>0) then
        { rhs with e_desc = Edelay(d, e) }
      else
        e
    | _ -> rhs
  in
  { eqm with eqm_clk = ock_eq; eqm_rhs = rhs }, (hfull, msol, mdecvar)

let var_dec_model_replace _ (hfull,msol,mdecvar) vdm =
 { vdm with vm_clock = subst_solution msol vdm.vm_clock }, (hfull, msol, mdecvar)


(* Main functions
  bquickres = try simplest solution resolution or fail. Used for model2node *)
let typing_model bquickres md =
  let lcst : ((affconstr list) * (boundconstr list)) = ([],[]) in

  let (h0, lcst) = append_model_env Env.empty lcst md.m_input in
  let (h, lcst) = append_model_env h0 lcst md.m_output in
  let (h, lcst, msubst, lwcet, mdecvar) = typing_block_model h lcst md.m_block in

  (* mdecvar: [First var of a "?" equation ==> corresponding decision variable] *)

  (* Update clock info in variable descriptions *)
  let set_clock vdm = { vdm with vm_clock = Env.find vdm.vm_ident h } in
  let md = { md with m_input = List.map set_clock md.m_input;
                     m_output = List.map set_clock md.m_output }
  in

  if debug_clocking then (
    print_constraint_environment ffout lcst;
    if (not (Env.is_empty mdecvar)) then
      print_mdecvar ffout mdecvar
  );

  
  (* Solve the constraints *)
  (* Note: no boundary constraint missing for the created phase variable, because
      the system is normalised *)
  let b_no_underspec_ops = Idents.Env.is_empty mdecvar in
  let msol = Affine_constraint_clocking.solve_constraints_main bquickres lwcet lcst b_no_underspec_ops in

  (* DEBUG
  print_msol ffout msol; *)

  (* Enrich the solution with the substitutions previously performed *)
  let msol = enrich_sol_with_msubst msubst msol in

  (* DEBUG
  print_msol ffout msol; *)

  (* Convert the solution back to a mapping from phase id to its value *)
  let misol = Affine_constraint_clocking.solution_to_phase_number msol in
  

  if debug_clocking then
    fprintf ffout "Starting substitution of solution in model clocking\n@?";

  (* Use solution to replace all phindex of the system *)
  let (hfull, _) = append_model_env h ([],[]) md.m_block.bm_local in
  let funs_replacement = { Hept_mapfold.defaults with
      eq_model = eq_model_replace;
      var_dec_model = var_dec_model_replace;
  } in
  let md, _ = funs_replacement.model_dec funs_replacement (hfull, misol, mdecvar) md in


  (* No update of signature: model should be the top-level node *)
  (* update_signature_model h md; *)
  md

let program p =
  let program_desc pd = match pd with
    | Pmodel md -> Pmodel (typing_model false md)
    | _ -> pd
  in
  { p with p_desc = List.map program_desc p.p_desc; }


