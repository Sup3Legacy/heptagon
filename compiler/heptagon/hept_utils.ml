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

let mk_cl_option glws locws =
  { copt_gl_worksize = glws; copt_loc_worksize = locws }

let mk_app ?(params=[]) ?(ty_subst=[]) ?(unsafe=false) ?(inlined=false) ?(clopt=None) op =
  { a_op = op; a_params = params; a_ty_subst=ty_subst; a_unsafe = unsafe; a_inlined = inlined; a_cloption = clopt }

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

let mk_var_dec ?(last = Var) ?(clock = fresh_clock()) name ty ~linearity =
  { v_ident = name; v_type = ty; v_linearity = linearity; v_clock = clock;
    v_last = last; v_loc = no_location }

let mk_block ?(stateful = true) ?(defnames = Env.empty) ?(locals = []) eqs =
  { b_local = locals; b_equs = eqs; b_defnames = defnames;
    b_stateful = stateful; b_loc = no_location; }

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

let mk_kernel_dec name inputs outputs loc issrc srcbin dim ?(locals = []) =
  { k_namekernel = name; k_input = inputs; k_output = outputs; k_loc = loc;
    k_issource = issrc; k_srcbin = srcbin; k_dim = dim; k_local = locals }

let mk_signature name ~extern ?(typeparamdecs=[]) ins outs stateful params constraints loc =
  { sig_name = name;
    sig_typeparamdecs = typeparamdecs;
    sig_inputs = ins;
    sig_stateful = stateful;
    sig_outputs = outs;
    sig_params = params;
    sig_param_constraints = constraints;
    sig_external = extern;
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
      node_loc = n.n_loc }

let signature_of_kernel k =
   { k_input = args_of_var_decs k.k_input;
     k_output = args_of_var_decs k.k_output;
     k_loc = k.k_loc;
     k_issource = k.k_issource;
     k_srcbin = k.k_srcbin;
     k_dim = k.k_dim;
     k_local = args_of_var_decs k.k_local }
