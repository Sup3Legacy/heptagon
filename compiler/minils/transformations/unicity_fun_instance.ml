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

(* Makes the function name unique - needed with interfacing with lopht
    so that equations using the same function can be differentiated
    in the obtained parallel schedule *)
(* Author: Giooss *)
open Names
open Containers
open Minils
open Mls_utils


(* Mapping between the funname and the corresponding Minils equation *)
(* These mapping will be used later in parshed_preproc.ml to translate back the parallel schedule from Lopht *)
let mFunname2Eq = ref StringMap.empty
let mEq2Funname = ref EqMap.empty

(* ------------------------- *)

let b_rewriting_activated = ref false

let counter = ref 0
let get_counter _ =
  let res = !counter in
  counter := !counter + 1;
  res

let make_funname_unique qn =
  let id = get_counter () in
  let n_name = qn.name ^ "_" ^ (string_of_int id) in
  { qn with name = n_name }

(* Revert the last function - be sure to do it only if the rewriting was activated *)
let revert_funname qn =
  if (!b_rewriting_activated) then
    let name = qn.name in
    let end_ind = String.rindex name '_' in
    let n_name = String.sub name 0 end_ind in
    { qn with name = n_name }
  else
    qn

(* ------------------------- *)


(* Makes sure that the functions called all have different names *)
let preprocess_funname bmodify nd =
  b_rewriting_activated := true;

  let nleq = List.map (fun eq ->
    match eq.eq_rhs.e_desc with
      | Eapp (ap, lev, ovid) -> (
        match ap.a_op with
        | Efun fn ->
          let nfn = make_funname_unique fn in

          let neq = if (bmodify) then
            let n_ap = { ap with a_op = Efun nfn } in
            let nrhs = { eq.eq_rhs with e_desc = Eapp(n_ap, lev, ovid) } in
            { eq with eq_rhs = nrhs }
          else
            eq
          in
          mFunname2Eq := StringMap.add nfn.name neq !mFunname2Eq;
          mEq2Funname := EqMap.add neq nfn.name !mEq2Funname;
          neq

        | Enode fn ->
          let nfn = make_funname_unique fn in
          let neq = if (bmodify) then
            let n_ap = { ap with a_op = Enode nfn } in
            let nrhs = { eq.eq_rhs with e_desc = Eapp(n_ap, lev, ovid) } in
            { eq with eq_rhs = nrhs }
          else
            eq
          in
          mFunname2Eq := StringMap.add nfn.name neq !mFunname2Eq;
          mEq2Funname := EqMap.add neq nfn.name !mEq2Funname;
          neq
        | _ -> eq
      )
      | _ -> eq
  ) nd.n_equs in
  { nd with n_equs = nleq }

(* ------------------------- *)

let program p =
  (* If currently preprocessing for Lopht, we need to modify the equations *)
  (* Else, if just preparing to parse the corresponding parallel schedule,
      we just build "mFunname2Eq" here *)
  let modify_mainnode = !Compiler_options.lopht_preprocess in

  (* Get the name of the mainnode *)
  let lqname = !Compiler_options.mainnode in
  if (lqname=[]) then (
    Format.eprintf "A main node with no input arguments must be given.@.";
    raise Errors.Error
  );
  if ((List.length lqname)>1) then (
    Format.eprintf "Warning: multiple main node declared. Last one selected.@.";
  );
  (* Main node is the last target node used *)
  let qname = List.hd lqname in

  (* Apply the transformation only on the mainnode *)
  let npdesc = List.map (fun pdesc -> match pdesc with
    | Pnode nd ->
      if (nd.n_name.name = qname.name) then
        Pnode (preprocess_funname modify_mainnode nd)
      else
        Pnode nd
    | _ -> pdesc
  ) p.p_desc in
  { p with p_desc = npdesc }

