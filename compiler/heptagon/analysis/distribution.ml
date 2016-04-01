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
(* distribution analysis *)

open Names
open Idents
open Signature
open Heptagon
open Hept_utils
open Global_printer
open Sites
open Location
open Format
open Pp_tools

(** Error Kind *)
type error_kind =
  | Etypeclash of tsite * tsite
  | Esiteclash of site * site
  | Esiteundefined of name
  | Einstanciation of name list
		       
let error_message loc = function
  | Etypeclash (actual_tsite, expected_tsite) ->
      Format.eprintf "%aDistribution: this expression has location %a,@\n\
                        but is expected to have location %a.@."
        print_location loc
        print_tsite actual_tsite
        print_tsite expected_tsite;
      raise Errors.Error
  | Esiteclash (actual_site, expected_site) ->
      Format.eprintf "%aDistribution: this value has location %a,@\n\
                        but is expected to have location %a.@."
        print_location loc
        print_site actual_site
        print_site expected_site;
      raise Errors.Error
  | Esiteundefined n ->
     Format.eprintf "%aDistribution: undefined site %a.@."
		    print_location loc
		    print_name n;
     raise Errors.Error
  | Einstanciation name_list ->
     Format.eprintf "%aDistribution: invalid instanciation of site list %a@."
		    print_location loc
		    (print_list_r print_name "[" "," "]") name_list;
     raise Errors.Error

let site_of_name h x =
  try
    Env.find x h
  with Not_found ->
    Format.printf "Not found while distribution : %a@\n"
		  Idents.print_ident x;
    raise Not_found

let build_site_env s_l = s_l
			
let mem_env senv x = List.mem x senv
	  
let rec typing_pat h = function
  | Evarpat x -> Ssite (site_of_name h x)
  | Etuplepat pat_list -> Sprod (List.map (typing_pat h) pat_list)

(* typing the expression, returns ct, ck_base *)
let rec typing h senv e =
  let tsite = match e.e_desc with
    | Econst _ ->
        let s = fresh_site() in
        Ssite s
    | Evar x ->
        let s = site_of_name h x in
        Ssite s
    | Efby (e1, e2) ->
        let tsite = typing h senv e1 in
        expect h senv tsite e2;
        tsite
    | Epre(_,e) ->
        typing h senv e
    | Ewhen (e,c,n) ->
       (* TODO : distrib implicite *)
       let site_n = site_of_name h n in
       let tsite = skeleton site_n e.e_ty in
       expect h senv tsite e;
       tsite
    | Emerge (x, c_e_list) ->
       (* TODO : distrib implicite *)
       let site_n = site_of_name h x in
       let tsite = Ssite site_n in
       List.iter (fun (_c,e) -> expect h senv tsite e) c_e_list;
       tsite
    | Estruct l ->
       let s = fresh_site () in
       let tsite = Ssite s in
       List.iter (fun (_, e) -> expect h senv tsite e) l;
       tsite
    | Eapp(app, args, _) ->
        typing_app h senv e.e_loc app args
    | Eiterator (it, app, nl, pargs, args, _) ->
        let tsite = match it with
          | Imap -> (* exactly as if clocking the node *)
              typing_app h senv e.e_loc app (pargs@args)
          | Imapi | Ifoldi
          | Ifold | Imapfold ->
	     failwith("Imapi not implemented")
        in
	tsite
    | Esplit _ | Elast _ -> assert false
  in
  e.e_tsite <- tsite;
  tsite

and expect h senv expected_tsite e =
  let actual_tsite = typing h senv e in
  (try unify actual_tsite expected_tsite
   with Unify -> error_message e.e_loc (Etypeclash (actual_tsite, expected_tsite)))

and typing_app h senv loc app e_list = match app.a_op with
  | Ecomm c_list ->
     let tsite_l = List.map2
		     (fun c e ->
		      let tsite_from = Ssite (Slocalized c.c_src) in
		      let tsite_to = Ssite (Slocalized c.c_dst) in
		      expect h senv tsite_from e;
		      tsite_to)
		     c_list e_list in
     Sites.prod tsite_l
  | Etuple
  | Earrow
  | Earray_fill | Eselect | Eselect_dyn | Eselect_trunc | Eupdate
  | Eselect_slice | Econcat | Earray | Efield | Efield_update
  | Eifthenelse
  | Ereinit ->
     let s = fresh_site () in
     let tsite = Ssite s in
     List.iter (expect h senv tsite) e_list;
     tsite
  | Efun { qual = Module "Iostream"; name = "printf" }
  | Efun { qual = Module "Iostream"; name = "fprintf" } ->
     let s = fresh_site () in
     List.iter (expect h senv (Ssite s)) e_list;
     Sprod []
  | (Efun f | Enode f) ->
     let node = Modules.find_value f in
     let site_map =
       try List.combine node.node_sites app.a_sites
       with Invalid_argument _ ->
	 Format.eprintf "ici : %a@\n" (print_list_r print_name "[" "," "]") app.a_sites;
	 error_message loc (Einstanciation node.node_sites)
     in
     (* Site variable for centralized nodes *)
     let s = fresh_site () in
     (* Translation of signature sites to sites *)
     let rec sigsite_to_site ssite = match ssite with
        | Signature.Scentralized -> Ssite s
        | Signature.Slocalized n ->
	   let n_inst =
	     try List.assoc n site_map
	     with Not_found ->
	       Misc.internal_error "Distribution: unconsistent signature"
	   in
	   Ssite (Slocalized n_inst)
      in
      List.iter2
        (fun a e -> expect h senv (sigsite_to_site a.a_site) e)
        node.node_inputs e_list;
      Sites.prod (List.map (fun a -> sigsite_to_site a.a_site) node.node_outputs)

let append_env h senv vds =
  List.fold_left
    (fun h { v_ident = n; v_site = s; v_loc = loc; } ->
     begin match s with
     | Scentralized | Svar _ -> ()
     | Slocalized n ->
	if not (mem_env senv n) then
	  error_message loc (Esiteundefined n)
     end;
     Env.add n s h)
    h vds

let rec typing_eq h senv ({ eq_desc = desc; eq_loc = loc } as _eq) =
  match desc with
  | Eeq(pat,e) ->
      let tsite = typing h senv e in
      let pat_tsite = typing_pat h pat in
      (try unify tsite pat_tsite
       with Unify ->
         eprintf "Incoherent site between right and left side of the equation.@\n";
         error_message loc (Etypeclash (tsite, pat_tsite)))
  | Eblock b ->
      ignore(typing_block h senv b)
  | _ -> assert false

and typing_eqs h senv eq_list = List.iter (typing_eq h senv) eq_list

and typing_block h senv
    ({ b_local = l; b_equs = eq_list } as _b) =
  let h' = append_env h senv l in
  typing_eqs h' senv eq_list;
  h'

    (* TODO
let typing_contract h contract =
  match contract with
    | None -> h
    | Some { c_block = b;
             c_assume = e_a;
             c_objectives = objs;
             c_controllables = c_list } ->
        let h' = typing_block h b in
        (* assumption *)
        expect h' (Etuplepat []) (Ck Clocks.Cbase) e_a;
        (* property *)
        List.iter (fun o -> expect h' (Etuplepat []) (Ck Clocks.Cbase) o.o_exp) objs;

        append_env h c_list

let typing_local_contract h contract =
  match contract with
    | None -> ()
    | Some { c_assume_loc = e_a_loc;
             c_enforce_loc = e_g_loc } ->
        (* assumption *)
        expect h (Etuplepat []) (Ck Clocks.Cbase) e_a_loc;
        (* property *)
        expect h (Etuplepat []) (Ck Clocks.Cbase) e_g_loc
     *)
    
(* check signature causality and update it in the global env *)
let update_signature h node =
  let set_arg_site vd ad =
    { ad with a_site = Signature.site_to_ssite (site_repr (Env.find vd.v_ident h)) }
  in
  let sign = Modules.find_value node.n_name in
  let sign =
    { sign with
      node_sites = node.n_sites;
      node_inputs = List.map2 set_arg_site node.n_input sign.node_inputs;
      node_outputs = List.map2 set_arg_site node.n_output sign.node_outputs } in
  (* TODO : check signature consistency *)
  Modules.replace_value node.n_name sign

let typing_node node =
  let senv = build_site_env node.n_sites in
  let h0 = append_env Env.empty senv node.n_input in
  let h0 = append_env h0 senv node.n_output in
  (* TODO *)
  (*let h = typing_contract h0 node.n_contract in*)
  let h = typing_block h0 senv node.n_block in
  (* TODO *)
  (*typing_local_contract h node.n_contract;*)
  (*update clock info in variables descriptions *)
  let set_site vd = { vd with v_site = site_repr (Env.find vd.v_ident h) } in
  let node = { node with n_input = List.map set_site node.n_input;
                         n_output = List.map set_site node.n_output }
  in
  (* check signature causality and update it in the global env *)
  update_signature h node;
  node

let program p =
  let program_desc pd = match pd with
    | Pnode nd -> Pnode (typing_node nd)
    | _ -> pd
  in
    { p with p_desc = List.map program_desc p.p_desc; }
