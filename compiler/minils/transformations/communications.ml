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

(* TODO HERE *)
(**
 Environment :
 - mapping site names/identifiers added as inputs
 - mapping variable names/mapping sites/variable
 - additional equations
 *)
type comm_env =
    { site_var : ident NamesEnv.t;
      comm_var : ident NamesEnv.t Idents.Env.t;
      add_eq   : Minils.eq list;
    }

let empty_env =
  { site_var = NamesEnv.empty;
    comm_var = Idents.Env.empty;
    add_eq = [] }
		
let edesc funs env desc =
  match desc with
  | Eapp ({ a_op = Ecomm c } as a, [e], r) ->
     let e, env = extvalue_it funs env e in
     let s = NamesEnv.find c.c_src env in
     let d = NamesEnv.find c.c_dst env in
     let e_s = mk_extvalue ~ty:Initial.tbool ~linearity:Linearity.Ltop
			   ~site:Sites.Scentralized
			   ~clock:Clocks.Cbase (Wvar s) in
     let e_d = mk_extvalue ~ty:Initial.tbool ~linearity:Linearity.Ltop
			   ~site:Sites.Scentralized
			   ~clock:Clocks.Cbase (Wvar d) in
     Eapp ({ a with a_op = Efun qn_comm }, [e_s;e_d;e], r), env
  | Eapp ({ a_op = (Efun _ | Enode _); a_sites = sl } as a, args, r) ->
     let args, env = Misc.mapfold (extvalue_it funs) env args in
     let site_args =
       List.map (fun s ->
		 let s_id = NamesEnv.find s env in
		 mk_extvalue ~ty:Initial.tbool
			     ~linearity:Linearity.Ltop
			     ~site:Sites.Scentralized
			     ~clock:Clocks.Cbase (Wvar s_id))
		sl in
     Eapp({ a with a_sites = [] }, site_args @ args, r), env
  | _ -> raise Errors.Fallback

let translate_clock env ct s = ct
	       
let exp funs env e =
  let e,_ = Mls_mapfold.exp funs env e in
  { e with
    e_ct = translate_clock env e.e_ct e.e_site;
  }
    
	       
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
  let funs = { Mls_mapfold.defaults with edesc = edesc; node_dec = node } in
  let p, _ = Mls_mapfold.program_it funs NamesEnv.empty p in
  p
