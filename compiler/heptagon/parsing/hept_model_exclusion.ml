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

(* Author: Guillaume I *)

(* This transformation checks that:
   - No "when", "merge" and "current" expression using general clocks are inside a model node
   - No "whenmodel", "currentmodel", "delay" and "delayfby" are inside a node/fun node
 *)
open Format
open Location
open Hept_parsetree
open Hept_parsetree_mapfold
open Hept_parsetree_printAST


(* acc: (expression_specific_to_a_node, expression_specific_to_a_model) *)

let exp funs acc e =
  let e, (accnode, accmodel) = Hept_parsetree_mapfold.exp funs acc e in
  match e.e_desc with
  | Ewhen _ | Emerge _ | Ecurrent _ ->
    if (accmodel) then
      (eprintf "%aThe expression %a is forbidden in a model.@."
            print_location e.e_loc
            print_exp e;
      raise Errors.Error)
    else
      e, (accnode, accmodel)
  | Ewhenmodel _ | Ecurrentmodel _ | Edelay _ | Edelayfby _ ->
    if (accnode) then
      (eprintf "%aThe expression %a is forbidden in a node.@."
            print_location e.e_loc
            print_exp e;
      raise Errors.Error)
    else
      e, (accnode, accmodel)
  | _ -> e, (accnode, accmodel)



let node_dec funs _ nd =
  Hept_parsetree_mapfold.node_dec funs (true, false) nd

let model_dec funs _ md =
  Hept_parsetree_mapfold.model_dec funs (false, true) md


let program p =
  let funs = { Hept_parsetree_mapfold.defaults with node_dec = node_dec; model_dec = model_dec; exp = exp } in
  let p, _ = funs.program funs (false, false) p in
	p