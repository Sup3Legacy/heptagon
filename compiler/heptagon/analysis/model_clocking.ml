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


let debug_clocking = false (* TODO DEBUG *)
let ffout = formatter_of_out_channel stdout

let constraint_bufferfby = true  (* TODO: mettre ca en option du compilo ? *)


let print_henv ff h =
  Env.iter (fun k v ->
    fprintf ff "\t%a => %a\n@?"  print_ident k  print_oneck v
  ) h

type error_kind =
  | Etypeclash of onect * onect

let error_message loc = function
  | Etypeclash (actual_ct, expected_ct) ->
      Format.eprintf "%aClock Clash: this expression has clock %a, but is expected to have clock %a.@."
        print_location loc
        print_onect actual_ct
        print_onect expected_ct;
      raise Errors.Error



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
      let (varopt_nock,_) = get_phase_ock n_ock in
      let idvar_nock = match varopt_nock with
        | None -> failwith "Internal error"
        | Some idvar -> idvar
      in
      let varname_n_ock = varname_from_phase_index idvar_nock in

      (* Affine constraint generation / ph_{n_ock} >= expr_{ock} *)
      let (varopt, ph) = get_phase_ock ock in

      let lcoeffVar = (1, varname_n_ock) :: [] in
      let lcoeffVar = match varopt with
        | None -> lcoeffVar
        | Some idvar ->
          (-1, varname_from_phase_index idvar)::lcoeffVar
      in
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
      (* Does this only happen when we have a delay of a constant, or something like that? *)
    | _ ->
      let per = Clocks.get_period_ock ock in
      let n_ock = fresh_osynch_period per in

      let laffconstr = if (constraint_bufferfby) then begin
        let (varopt_nock,_) = get_phase_ock n_ock in
        let idvar_nock = match varopt_nock with
          | None -> failwith "Internal error"
          | Some idvar -> idvar
        in
        let varname_n_ock = varname_from_phase_index idvar_nock in

        (* Affine constraint generation / expr_{ock} >= ph_{n_ock} +1 *)
        let (varopt, ph) = get_phase_ock ock in

        let lcoeffVar = (-1, varname_n_ock) :: [] in
        let lcoeffVar = match varopt with
          | None -> lcoeffVar
          | Some idvar ->
            (1, varname_from_phase_index idvar)::lcoeffVar
        in
        let affconstr = mk_affconstr false lcoeffVar (1-ph) in
        affconstr::[]
      end else [] in
      (Ock n_ock, laffconstr)
  end 

let rec typing_bufferlat_osynch oct lat =match oct with
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
      
      let (varopt_nock,_) = get_phase_ock n_ock in
      let idvar_nock = match varopt_nock with
        | None -> failwith "Internal error"
        | Some idvar -> idvar
      in
      let varname_n_ock = varname_from_phase_index idvar_nock in

      let (varopt, ph) = get_phase_ock ock in

      (* Affine constraint generation / lat >= ph_{n_ock} - ph_{ock} >= 0 *)

      (* ph_{ock} - ph_{n_ock} >= -lat *)
      let lcoeffVar_lat = (-1, varname_n_ock) :: [] in
      let lcoeffVar_lat = match varopt with
        | None -> lcoeffVar_lat
        | Some idvar ->
          (1, varname_from_phase_index idvar)::lcoeffVar_lat
      in
      let affconstr_lat = mk_affconstr false lcoeffVar_lat (-lat-ph) in

      (* ph_{n_ock} - ph_{ock} >= 0  *)
      let lcoeffVar_0 = (1, varname_n_ock) :: [] in
      let lcoeffVar_0 = match varopt with
        | None -> lcoeffVar_0
        | Some idvar ->
          (-1, varname_from_phase_index idvar)::lcoeffVar_0
      in
      let affconstr_0 = mk_affconstr false lcoeffVar_0 ph in

      let laffconstr = affconstr_0::affconstr_lat::[] in
      (Ock n_ock, laffconstr)
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
    (Ock ock, lcst)
  | Evar x ->
    let ock = ock_of_name h x in
    (Ock ock, lcst)
  | Efby (e1, e2) ->
    let ct1, lcst = typing_osych h lcst pat e1 in
    let lcst = expect_osynch h lcst pat ct1 e2 in
    (ct1, lcst)
  | Epre (_,e2) ->
    typing_osych h lcst pat e2
  | Estruct l ->
    let ock = fresh_osynch_clock () in
    let lcst = List.fold_left (fun lcst (_, e) ->
      expect_osynch h lcst pat (Ock ock) e
    ) lcst l in
    (Ock ock, lcst)

  (* Expressions specific to model *)
  | Ewhenmodel (e, (ph,ratio)) ->
    let (octe, lcst) = typing_osych h lcst pat e in
    let noct = typing_when_osynch octe ph ratio in
    (noct, lcst)

  | Ecurrentmodel ((ph, ratio), _, e) ->
    let (octe, lcst) = typing_osych h lcst pat e in
    let noct = typing_current_osynch octe ph ratio in
    (noct, lcst)

  | Edelay (d, e) ->
    let (octe, lcst) = typing_osych h lcst pat e in
    let noct = typing_delay_osynch octe d in
    (noct, lcst)

  | Edelayfby (d, _, e) ->
    let (octe, lcst) = typing_osych h lcst pat e in
    let noct = typing_delayfby_osynch octe d in
    (noct, lcst)

  | Ebuffer e ->
    let (octe, lcst) = typing_osych h lcst pat e in
    let (noct, laffconstr) = typing_buffer_osynch octe in
    let (al,bl) = lcst in
    (noct, (laffconstr@al,bl))

  | Ebufferfby (_, e) ->
    let (octe, lcst) = typing_osych h lcst pat e in
    let (noct, laffconstr) = typing_bufferfby_osynch octe in
    let (al,bl) = lcst in
    (noct, (laffconstr@al,bl))

  | Ebufferlat (lat, e) ->
    let (octe, lcst) = typing_osych h lcst pat e in
    let (noct, laffconstr) = typing_bufferlat_osynch octe lat in
    let (al,bl) = lcst in
    (noct, (laffconstr@al,bl))

  | Eapp({a_op = op}, args, _) ->
      let base_ock = fresh_osynch_clock () in
      let (oct, lcst) = typing_osynch_app h lcst base_ock pat op args in
      (oct, lcst)

  (* TODO: iterators needed ??? :/ *)
  | Eiterator (it, {a_op = op}, nl, pargs, args, _) ->
    let base_ock = fresh_osynch_clock () in
    let (oct, lcst) = match it with
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
          let (oct, lcst) = typing_osynch_app h lcst base_ock pat op (pargs@args) in
          (oct, lcst)
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
          let (oct, lcst) = typing_osynch_app h lcst base_ock pat op (pargs@(insert_i args)) in
          (oct, lcst)
    in
    (oct, lcst)
  | Esplit _ | Elast _ | Ecurrent _ -> assert false
  | Emerge _ | Ewhen _ -> failwith "Construction should not appear in a model node"

and typing_osynch_app h lcst base pat op e_list = match op with
  | Etuple (* to relax ? *)
  | Earrow
  | Earray_fill | Eselect | Eselect_dyn | Eselect_trunc | Eupdate
  | Eselect_slice | Econcat | Earray | Efield | Efield_update | Eifthenelse | Ereinit ->
    let lcst = List.fold_left (fun lcst e ->
      expect_osynch h lcst pat (Ock base) e
    ) lcst e_list in
    (Ock base, lcst)
  | Efun { qual = Module "Iostream"; name = "printf" } | Efun { qual = Module "Iostream"; name = "fprintf" } ->
    let lcst = List.fold_left (fun lcst e ->
      expect_osynch h lcst pat (Ock base) e
    ) lcst e_list in
    (Ocprod [], lcst)
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
    let lcst = List.fold_left (fun lcst e -> expect_osynch h lcst pat (Ock base) e) lcst e_list in
    Ocprod (List.map (fun _ -> (Ock base)) node.node_outputs), lcst

and expect_osynch h lcst pat expected_oct e =
  let (actual_oct, lcst) = typing_osych h lcst pat e in
  (try unify_onect actual_oct expected_oct
   with Unify ->
    error_message e.e_loc (Etypeclash (actual_oct, expected_oct))
  );
  lcst


(* ----- *)
(* ----- *)
let rec typing_model_eq h lcst eqm =
  if (debug_clocking) then
    fprintf ffout "Entering model equation %a@\n" Hept_printer.print_eq_model eqm;

  let (oct, lcst) = typing_osych h lcst eqm.eqm_lhs eqm.eqm_rhs in
  let pat_oct = typing_model_pat h eqm.eqm_lhs in
  (try unify_onect oct pat_oct
   with Unify ->
     eprintf "Incoherent clock between right and left side of the equation:@\n\t%a\nlhs :: %a  | rhs :: %a.@\n"
      Hept_printer.print_eq_model eqm print_onect pat_oct  print_onect oct;
     error_message eqm.eqm_loc (Etypeclash (oct, pat_oct)))

and typing_model_eqs h lcst eq_list = List.iter (typing_model_eq h lcst) eq_list

(* Block management *)
and append_model_env h lcst vdms =
  let (h, lcst) = List.fold_left (fun (h,lcst) { vm_ident = n; vm_clock = ock } ->
    (* Create a new boundary condition from ock, if phase variable *)
    let (varopt, ph) = get_phase_ock ock in
    let nlaffcst = match varopt with
      | None -> lcst   (* The check that the phase is valid was done during parsing*)
      | Some varid ->
        assert(ph==0);    (* No shift in variable declaration *)
        let varname = varname_from_phase_index varid in
        let per = get_period_ock ock in

        let bcond = mk_bound_constr varname 0 per in
        let (laffcst, lbndcst) = lcst in
        (laffcst, bcond::lbndcst)
    in

    (* Update h *)
    let nh = Env.add n ock h in
    (nh, nlaffcst)
  ) (h,lcst) vdms in
  (h, lcst)

and typing_block_model h lcst {bm_local = l; bm_eqs = eq_list} =
  let (h1, lcst) = append_model_env h lcst l in

  if (debug_clocking) then
    fprintf ffout "Entering block_model - Environment is:\n%a@\n" print_henv h1;

  typing_model_eqs h1 lcst eq_list;
  (h1, lcst)


(* Substitution of the phase solution in the program *)
let rec subst_solution msol ock = match ock with
  | Cone _ -> ock
  | Cshift (sh, ock1) ->
    let ock1 = subst_solution msol ock1 in
    ock_repr (Cshift (sh, ock1))
  | Covar { contents = ol } -> (match ol with
    | Coindex _ ->
      failwith "Internal error: Period and phase unknown during solution substitution"
    | Colink ock -> subst_solution msol ock
    | Coper ({ contents = op }, per) -> (match op with
      | Cophase ph -> Cone (ph, per)
      | Cophshift (sh, phid) ->  (* Shift + 'a *)
        let ph_val = IntMap.find phid msol in
        Cone (ph_val+sh, per)
      | Cophindex phid -> (* 'a *)
        let ph_val = IntMap.find phid msol in
        Cone (ph_val, per)
    )
  )

let eq_model_replace _ msol eqm =
  { eqm with eqm_clk = subst_solution msol eqm.eqm_clk }, msol

let var_dec_model_replace _ msol vdm =
 { vdm with vm_clock = subst_solution msol vdm.vm_clock }, msol


(* Main functions *)
let typing_model md =
  let lcst : ((affconstr list) * (boundconstr list)) = ([],[]) in

  let (h0, lcst) = append_model_env Env.empty lcst md.m_input in
  let (h, lcst) = append_model_env h0 lcst md.m_output in
  let (h, lcst) = typing_block_model h lcst md.m_block in
  (* Update clock info in variable descriptions *)
  let set_clock vdm = { vdm with vm_clock = Env.find vdm.vm_ident h } in
  let md = { md with m_input = List.map set_clock md.m_input;
                     m_output = List.map set_clock md.m_output }
  in

  if debug_clocking then
    print_constraint_environment ffout lcst;

  (* Solve the constraints *)
  (* Note: no boundary constraint missing for the created phase variable, because
      the system is normalised *)
  let msol = Affine_constraint_clocking.solve_constraints_main lcst in

  (* Convert the solution back to a mapping from phase id to its value *)
  let misol = Affine_constraint_clocking.solution_to_phase_number msol in
  
  (* Use solution to replace all phindex of the system *)
  let funs_replacement = { Hept_mapfold.defaults with
      eq_model = eq_model_replace;
      var_dec_model = var_dec_model_replace;
  } in
  let md, _ = funs_replacement.model_dec funs_replacement misol md in


  (* No update of signature: model should be the top-level node *)
  (* update_signature_model h md; *)
  md

let program p =
  let program_desc pd = match pd with
    | Pmodel md -> Pmodel (typing_model md)
    | _ -> pd
  in
  { p with p_desc = List.map program_desc p.p_desc; }
