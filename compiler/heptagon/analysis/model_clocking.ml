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
open Heptagon
open Hept_utils
open Global_printer
open Signature
open Clocks
open Location
open Format


type error_kind =
  | Etypeclash of onect * onect

let error_message loc = function
  | Etypeclash (actual_ct, expected_ct) ->
      Format.eprintf "%aClock Clash: this expression has clock %a,@\n\
                        but is expected to have clock %a.@."
        print_location loc
        print_onect actual_ct
        print_onect expected_ct;
      raise Errors.Error





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
    | Cone (ph, per) ->
      let nper = per * ratio in
      let nph = ph + (phWhen * per) in
      Ock (Cone (nph, nper))
    | _ -> failwith "Typing 1-synch when - Ck clock unrecognized"
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
    | Cone (ph, per) ->
      assert(per mod ratio = 0); (* Harmonicity hypothesis *)
      let nper = per / ratio in
      let nph = ph - (phCurr * nper) in
      Ock (Cone (nph, nper))
    | _ -> failwith "Typing 1-synch current - Ck clock unrecognized"
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
    | Cone (ph, per) ->
      let nph = ph + d in
      assert(0<=d);
      assert(0<=nph);
      assert(nph<per);
      Ock (Cone (nph, per))
    | _ -> failwith "Typing 1-synch delay - Ck clock unrecognized"
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
    | Cone (ph, per) ->
      let nph = ph + d - per in  (* fby -> going into the next period *)
      assert(0<=d);
      assert(0<=nph);
      assert(nph<per);
      Ock (Cone (nph, per))
    | _ -> failwith "Typing 1-synch delayfby - Ck clock unrecognized"
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

let rec typing_osych h pat e = match e.e_desc with
  | Econst _ -> 
    let ock = fresh_osynch_clock () in
      Ock ock
  | Evar x ->
    let ock = ock_of_name h x in
    Ock ock
  | Efby (e1, e2) ->
    let ct1 = typing_osych h pat e1 in
    expect_osynch h pat ct1 e2;
    ct1
  | Estruct l ->
    let ock = fresh_osynch_clock () in
    List.iter (fun (_, e) -> expect_osynch h pat (Ock ock) e) l;
    Ock ock

  (* Expressions speficic to model *)
  | Ewhenmodel (e, (ph,ratio)) ->
    let octe = typing_osych h pat e in
    let noct = typing_when_osynch octe ph ratio in
    noct

  | Ecurrentmodel ((ph, ratio), eInit, e) ->
    let octe = typing_osych h pat e in
    expect_osynch h pat octe eInit;
    let noct = typing_current_osynch octe ph ratio in
    noct

  | Edelay (d, e) ->
    let octe = typing_osych h pat e in
    let noct = typing_delay_osynch octe d in
    noct

  | Edelayfby (d, eInit, e) ->
    let octe = typing_osych h pat e in
    expect_osynch h pat octe eInit;
    let noct = typing_delayfby_osynch octe d in
    noct

  | Eapp({a_op = op}, args, _) ->
      let base_ock = fresh_osynch_clock () in
      let oct = typing_osynch_app h base_ock pat op args in
      oct

  (* TODO: iterators needed ??? :/ *)
  | Eiterator (it, {a_op = op}, nl, pargs, args, _) ->
    let base_ock = fresh_osynch_clock () in
    let oct = match it with
      | Imap -> (* exactly as if clocking the node *)
          typing_osynch_app h base_ock pat op (pargs@args)
      | Imapi -> (* clocking the node with the extra i input on [ck_r] *)
          let il (* stubs i as 0 *) =
            List.map (fun _ -> mk_exp
                (Econst (Initial.mk_static_int 0))
                Initial.tint ~linearity:Linearity.Ltop
            ) nl
          in
          typing_osynch_app h base_ock pat op (pargs@args@il)
      | Ifold | Imapfold ->
          (* clocking node with equality constaint on last input and last output *)
          let oct = typing_osynch_app h base_ock pat op (pargs@args) in
          oct
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
          let oct = typing_osynch_app h base_ock pat op (pargs@(insert_i args)) in
          oct
    in
    oct
  | Esplit _ | Elast _ | Ecurrent _ -> assert false
  | Emerge _ | Epre _ | Ewhen _ -> failwith "Construction should not appear in a model node"

and typing_osynch_app h base pat op e_list = match op with
  | Etuple (* to relax ? *)
  | Earrow
  | Earray_fill | Eselect | Eselect_dyn | Eselect_trunc | Eupdate
  | Eselect_slice | Econcat | Earray | Efield | Efield_update | Eifthenelse | Ereinit ->
    List.iter (expect_osynch h pat (Ock base)) e_list;
    Ock base
  | Efun { qual = Module "Iostream"; name = "printf" } | Efun { qual = Module "Iostream"; name = "fprintf" } ->
    List.iter (expect_osynch h pat (Ock base)) e_list;
    Ocprod []
  | (Efun f | Enode f) ->
    (* Big one - function call *)
    (* REMARK - We forbid clock change inside a function called by a model node
        (ie, no "on" on the output of clocks => no clock on sign of function) *)
    let node = Modules.find_value f in
    let pat_id_list = Hept_clocking.ident_list_of_pat pat in
    let rec build_env a_l v_l env = match a_l, v_l with
      | [],[] -> env
      | a::a_l, v::v_l -> (match a.a_name with
          | None -> build_env a_l v_l env
          | Some n -> build_env a_l v_l ((n,v)::env)
        )
      | _ ->
          Misc.internal_error ("Clocking, non matching signature in call of "^
                                  Names.fullname f);
    in
    let env_pat = build_env node.node_outputs pat_id_list [] in
    let env_args = build_env node.node_inputs e_list [] in
    
    List.iter2 (fun _ e -> expect_osynch h pat (Ock base) e) node.node_inputs e_list;
    Ocprod (List.map (fun _ -> (Ock base)) node.node_outputs)

and expect_osynch h pat expected_oct e =
  let actual_oct = typing_osych h pat e in
  (try unify_onect actual_oct expected_oct
   with Unify ->
    error_message e.e_loc (Etypeclash (actual_oct, expected_oct))
  )


(* ----- *)
(* ----- *)
let rec typing_model_eq h eqm =
  let oct = typing_osych h eqm.eqm_lhs eqm.eqm_rhs in
  let pat_oct = typing_model_pat h eqm.eqm_lhs in
  (try unify_onect oct pat_oct
   with Unify ->
     eprintf "Incoherent clock between right and left side of the equation.@\n";
     error_message eqm.eqm_loc (Etypeclash (oct, pat_oct)))

and typing_model_eqs h eq_list = List.iter (typing_model_eq h) eq_list

(* Block management *)
and append_model_env h vdms =
  List.fold_left (fun h { vm_ident = n; vm_clock = ock } -> Env.add n ock h) h vdms 

and typing_block_model h {bm_local = l; bm_eqs = eq_list} =
  let h1 = append_model_env h l in
  typing_model_eqs h1 eq_list;
  h1

let typing_model md = 
  let h0 = append_model_env Env.empty md.m_input in
  let h = append_model_env h0 md.m_output in
  let h = typing_block_model h md.m_block in

  (* Update clock info in variable descriptions *)
  let set_clock vdm = { vdm with vm_clock = Env.find vdm.vm_ident h } in
  let md = { md with m_input = List.map set_clock md.m_input;
                     m_output = List.map set_clock md.m_output }
  in
  (* No update of signature: model should be the top-level node *)
  (* update_signature_model h md; *)
  md

let program p =
  let program_desc pd = match pd with
    | Pmodel md -> Pmodel (typing_model md)
    | _ -> pd
  in
  { p with p_desc = List.map program_desc p.p_desc; }
