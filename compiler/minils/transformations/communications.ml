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
(* Copyright 2016 ENS, INRIA, UJF                                      *)
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
open Names
open Idents
open Minils
open Mls_mapfold
open Mls_utils

(** 
Translate communications [[d <- s](e)] into special node call
Desynch.comm(s,d,e) 
*)

let qn_comm = { qual = Module "Desynch"; name = "comm" }
       
let edesc funs env desc =
  match desc with
  | Eapp ({ a_op = Ecomm c } as a, [e], r) ->
     let s = NamesEnv.find c.c_src env in
     let d = NamesEnv.find c.c_dst env in
     Eapp ({ a with a_op = Efun qn_comm }, [s;d;e], r)
  | _ -> raise Errors.Fallback

let node funs _ nd =
  let site_inputs, env =
    Misc.mapfold
      (fun env n ->
       let n_id = ident_of_name n in
       let env = NamesEnv.add n n_id env in
       let vd = mk_var_dec n_id Initial.tbool Linearity.Ltop Clocks.Cbase Sites.Scentralized in
       vd, env)
      NamesEnv.empty nd.n_sites in
  let nd, _ = Mls_mapfold.node_dec funs env nd in
  (* return updated node *)
  { nd with n_input = site_inputs @ nd.n_input }, env

let program p =
  let funs = { Mls_mapfold.defaults with exp = exp; node_dec = node } in
  let p, _ = Mls_mapfold.program_it funs NamesEnv.empty p in
  p
