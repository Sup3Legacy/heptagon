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
(* the internal representation *)
open Location
open Idents
open Signature
open Types
open Linearity
open Clocks
open Initial
open Heptagon

(* Helper functions to create AST. *)
(* TODO : After switch, all mk_exp should take care of level_ck *)
let mk_exp desc ?(level_ck = Clocks.Cbase) ?(ct_annot = None) ?(loc = no_location) ty ~linearity =
  { e_desc = desc; e_ty = ty; e_ct_annot = ct_annot; e_linearity = linearity;
    e_level_ck = level_ck; e_loc = loc; }

let mk_app ?(params=[]) ?(ty_subst=[]) ?(unsafe=false) ?(inlined=false) op =
  { a_op = op; a_params = params; a_ty_subst=ty_subst; a_unsafe = unsafe; a_inlined = inlined }

let mk_op_app ?(params=[]) ?(ty_subst=[]) ?(unsafe=false) ?(reset=None) op args =
  Eapp(mk_app ~params:params ~ty_subst:ty_subst ~unsafe:unsafe op, args, reset)

let mk_type_dec name desc =
  { t_name = name; t_desc = desc; t_loc = no_location; }

let mk_equation ?(loc=no_location) desc =
  let _, s = Stateful.eqdesc Stateful.funs false desc in
  { eq_desc = desc;
    eq_stateful = s;
    eq_inits = Lno_init;
    eq_loc = loc; }

let mk_annot_eq_model aeqmdesc =
  { anneqm_desc = aeqmdesc; anneqm_loc = no_location }

let mk_equation_model p e ?(clock = Clocks.fresh_osynch_clock ()) lanneqm stateful ?(loc=no_location) =
  { eqm_lhs = p;
    eqm_rhs = e;
    eqm_clk = clock;
    eqm_stateful = stateful;
    eqm_annot = lanneqm;
    eqm_loc = loc }

let mk_var_dec ?(last = Var) ?(clock = fresh_clock()) name ty ~linearity =
  { v_ident = name; v_type = ty; v_linearity = linearity; v_clock = clock;
    v_last = last; v_loc = no_location }

let mk_var_dec_model ?(clock = fresh_osynch_clock ()) name ty =
  { vm_ident = name; vm_type = ty; vm_clock = clock; vm_loc = no_location }

let mk_block ?(stateful = true) ?(defnames = Env.empty) ?(locals = []) eqs =
  { b_local = locals; b_equs = eqs; b_defnames = defnames;
    b_stateful = stateful; b_loc = no_location; }

let mk_annot_model amdesc =
  { annm_desc = amdesc; annm_loc = no_location }

let mk_block_model ?(locals = []) lannm eqs =
  { bm_local = locals; bm_eqs = eqs; bm_annot = lannm; bm_loc = no_location }

let dfalse =
  mk_exp (Econst (mk_static_bool false)) (Tid Initial.pbool) ~linearity:Ltop
let dtrue =
  mk_exp (Econst (mk_static_bool true)) (Tid Initial.pbool) ~linearity:Ltop

let mk_ifthenelse e1 e2 e3 =
  { e3 with e_desc = mk_op_app Eifthenelse [e1; e2; e3] }

let mk_simple_equation pat e =
  mk_equation (Eeq(pat, e))

let mk_switch_equation e l =
  mk_equation (Eswitch (e, l))

let mk_typeparam_dec nametype nameclass =
  { t_nametype = nametype; t_nameclass = nameclass }

let mk_class_dec classname linsts loc =
  { c_nameclass = classname; c_insttypes = linsts; c_loc = loc }

let mk_ressource_dec name max loc =
  { r_name = name; r_max = max; r_loc = loc }

let mk_signature name ~extern ?(typeparamdecs=[]) ins outs stateful params constraints
      wcet lressutil loc =
  { sig_name = name;
    sig_typeparamdecs = typeparamdecs;
    sig_inputs = ins;
    sig_stateful = stateful;
    sig_outputs = outs;
    sig_params = params;
    sig_param_constraints = constraints;
    sig_external = extern;
    sig_wcet = wcet;
    sig_ressource = lressutil;
    sig_loc = loc }

let mk_node
    ?(typeparamdecs=[]) ?(input = []) ?(output = []) ?(contract = None)
    ?(stateful = true) ?(unsafe = false) ?(loc = no_location) ?(param = []) ?(constraints = [])
    name block =
  { n_name = name;
    n_stateful = stateful;
    n_unsafe = unsafe;
    n_typeparamdecs = typeparamdecs;
    n_input = input;
    n_output = output;
    n_contract = contract;
    n_block = block;
    n_loc = loc;
    n_params = param;
    n_param_constraints = constraints }

let mk_model ?(input = []) ?(output = []) ?(loc = no_location) name block =
  { m_name = name;
    m_input = input;
    m_output = output;
    m_block = block;
    m_loc = loc }



(** @return the set of variables defined in [pat]. *)
let vars_pat pat =
  let rec _vars_pat locals acc = function
    | Evarpat x ->
        if (IdentSet.mem x locals) || (IdentSet.mem x acc)
        then acc
        else IdentSet.add x acc
    | Etuplepat pat_list -> List.fold_left (_vars_pat locals) acc pat_list
  in _vars_pat IdentSet.empty IdentSet.empty pat

(** @return whether an object of name [n] belongs to
    a list of [var_dec]. *)
let rec vd_mem n = function
  | [] -> false
  | vd::l -> vd.v_ident = n || (vd_mem n l)

let args_of_var_decs =
  (* before the clocking the clock is wrong in the signature *)
 List.map
   (fun vd -> Signature.mk_arg (Some (Idents.source_name vd.v_ident))
                               vd.v_type (Linearity.check_linearity vd.v_linearity) Signature.Cbase)

(* Translate the typeparam_dec (of heptagon.ml) into a typeparam_def (of signature.ml) *)
let typeparamdefs_of_decs =
  List.map (fun tpdec -> Signature.mk_typeparam_def
                             (Names.shortname tpdec.t_nametype)
                             (Names.fullname tpdec.t_nameclass) ) 

let signature_of_node n =
    { node_inputs = args_of_var_decs n.n_input;
      node_outputs  = args_of_var_decs n.n_output;
      node_stateful = n.n_stateful;
      node_unsafe = n.n_unsafe;
      node_typeparams = typeparamdefs_of_decs n.n_typeparamdecs;
      node_params = n.n_params;
      node_param_constraints = n.n_param_constraints;
      node_external = false;
      node_wcet = None;  (* TODO: do some kind of summation here? :/ *)
      node_ressource = [];  (* TODO: do some kind of merge here? :/ *)
      node_loc = n.n_loc }
