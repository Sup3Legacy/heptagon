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
(** Scoping. Introduces unique indexes for local names and replace global
    names by qualified names *)


(* [local_const] is the environnement with local constant variables,
  that is for now only the statics node parameters.
  It is built with [build_const].
  When qualifying a constant var,
  it is first check in the local_const env, so qualified with [local_qn]
  if not found we try to qualify it with the global env. *)

(* The global environement is initialized by the scoping pass.
   This allow at the same time
   to qualify types, constants, constructors, fields and node calls,
   according to the current module definitions and opened modules. *)

(* [env] of type Rename.t is the renaming environnement
   used to map a var name to a var ident.
   It is initialized at node declaration level with the inputs and outputs,
   and then appended with the local var declarations at each block level
   with the [build] function.
   It checks that if a var is used with a last, it is declared as a last.*)

(* convention : Static operators get static params and static args.
   This scoping set the static params as the first static args :
    op<a1,a2> (a3) ==> op <a1> (a2,a3) ==> op (a1,a2,a3) *)

open Location
open Hept_parsetree
open Names
open Idents
open Format
open Static
open Global_printer
open Modules

module Error =
struct
  type error =
    | Evar_unbound of name
    | Equal_notfound of name*Names.qualname
    | Equal_unbound of name*name
    | Enot_last of name
    | Evariable_already_defined of name
    | Etypevar_already_defined of name
    | Econst_variable_already_defined of name
    | Estatic_exp_expected
    | Eredefinition of Names.qualname
    | Elinear_type_no_memalloc

  let message loc kind =
    begin match kind with
      | Evar_unbound name ->
          eprintf "%aThe variable %s is unbound.@."
            print_location loc
            name
      | Equal_notfound (s,q) ->
          eprintf "%aThe qualified %s %a can't be found.@."
            print_location loc
            s print_qualname q
      | Equal_unbound (s,n) ->
          eprintf "%aUnbound %s %a.@."
            print_location loc
            s print_name n
      | Enot_last name ->
          eprintf "%aThe variable %s should be declared as a last.@."
            print_location loc
            name
      | Evariable_already_defined name ->
          eprintf "%aThe variable %s is already defined.@."
            print_location loc
            name
      | Etypevar_already_defined name ->
          eprintf "%aThe type variable %s is already defined.@."
            print_location loc
            name
      | Econst_variable_already_defined name ->
          eprintf "%aThe const variable %s is already defined.@."
            print_location loc
            name
      | Estatic_exp_expected ->
          eprintf "%aA static expression was expected.@."
            print_location loc
      | Eredefinition qualname ->
          eprintf "%aName %a was already defined.@."
            print_location loc
            print_qualname qualname
      | Elinear_type_no_memalloc ->
          eprintf "%aLinearity annotations cannot be used without memory allocation.@."
            print_location loc
    end;
    raise Errors.Error

  exception ScopingError of error

  let error kind = raise (ScopingError(kind))
end

open Error

let safe_add loc add n x =
  try ((add n x) : unit)
  with Modules.Already_defined -> Error.message loc (Eredefinition n)

(** {3 Qualify when ToQ and check when Q according to the global env } *)

let _qualify_with_error s qfun cqfun q = match q with
  | ToQ name ->
      (try qfun name with Not_found -> error (Equal_unbound (s,name)))
  | Q q ->
      if cqfun q then q else error (Equal_notfound (s,q))

let qualify_value = _qualify_with_error "value" qualify_value check_value
let qualify_type = _qualify_with_error "type" qualify_type check_type
let qualify_class = _qualify_with_error "class" qualify_class check_class
let qualify_constrs =
  _qualify_with_error "constructor" qualify_constrs check_constrs
let qualify_field = _qualify_with_error "field" qualify_field check_field
let qualify_ressource = _qualify_with_error "ressource" qualify_ressource check_ressource

(** Qualify a var name as a constant variable,
    if not in local_const or global_const then raise Not_found *)
let qualify_var_as_const local_const c =
  if NamesSet.mem c local_const
  then local_qn c
  else qualify_const c

(** Qualify with [Names.local_qualname] when in local_const,
    otherwise qualify according to the global env *)
let qualify_const local_const c = match c with
  | ToQ c -> (try qualify_var_as_const local_const c
              with Not_found -> error (Equal_unbound ("constant",c )))
  | Q q -> if check_const q then q else raise Not_static

module Rename =
struct
  include
    (Map.Make (struct type t = string let compare = String.compare end))

  (** Rename a var *)
  let var loc env n =
    try fst (find n env)
    with Not_found -> Error.message loc (Evar_unbound n)

  (** Rename a last *)
  let last loc env n =
    try
      let id, last = find n env in
      if not last then Error.message loc (Enot_last n) else id
    with Not_found -> Error.message loc (Evar_unbound n)

  (** Adds a name to the list of used names and idents. *)
  let add_used_name env n =
    add n (ident_of_name n, false) env

  (** Add a var *)
  let add_var loc env n =
    if mem n env then Error.message loc (Evariable_already_defined n)
    else
        add n (ident_of_name n, false) env

  (** Add a last *)
  let add_last loc env n =
    if mem n env then Error.message loc (Evariable_already_defined n)
    else
        add n (ident_of_name n, true) env

  (** Add a var dec *)
  let add env vd =
    let add = match vd.v_last with
      | Var -> add_var
      | Last _ -> add_last in
    add vd.v_loc env vd.v_name

  (** Append a list of var dec *)
  let append env vd_list = List.fold_left add env vd_list

  (** Append a var model dec *)
  let add_vdm env vm =
    add_var vm.vm_loc env vm.vm_ident

  let append_vdm env vdm_list = List.fold_left add_vdm env vdm_list
end


(* Environment management for locally introduced types inside a node *)
module RenameType =
struct
  include (Map.Make (struct type t = string let compare = String.compare end))
  
  (** Rename a type variable *)
  let typevar loc tenv n =
    try fst (find n tenv)
    with Not_found -> Error.message loc (Evar_unbound n)
  
  (** Add a name of type variable to the list of used names/idents *)
  let add_used_name tenv tvd =
    add tvd.t_nametype tvd tenv
  
  (** Add a type var *)
  let add_typevar loc tenv tvd =
    if mem tvd.t_nametype tenv then
      Error.message loc (Etypevar_already_defined tvd.t_nametype)
    else
      add tvd.t_nametype tvd tenv
  
  (** Add a type var declaration *)
  let add loc tenv tvd = add_typevar loc tenv tvd
  
  (* No need for an append function (type variable are only defined at one place of the node) *)
end


let mk_app ?(params=[]) ?(ty_subst=[]) ?(unsafe=false) ?(inlined = false) op =
  { Heptagon.a_op = op;
    Heptagon.a_params = params;
    Heptagon.a_ty_subst = ty_subst;
    Heptagon.a_unsafe = unsafe;
    Heptagon.a_inlined = inlined }

let mk_signature name ~extern ?(typeparamdecs=[]) ins outs stateful params constraints
    wcet lressutil loc =
  { Heptagon.sig_name = name;
    Heptagon.sig_typeparamdecs = typeparamdecs;
    Heptagon.sig_inputs = ins;
    Heptagon.sig_stateful = stateful;
    Heptagon.sig_outputs = outs;
    Heptagon.sig_params = params;
    Heptagon.sig_param_constraints = constraints;
    Heptagon.sig_external = extern;
    Heptagon.sig_wcet = wcet;
    Heptagon.sig_ressource = lressutil;
    Heptagon.sig_loc = loc }


(** Function to build the defined static parameters set *)
let build_const loc vd_list =
  let _add_const_var loc c local_const =
    if NamesSet.mem c local_const
    then Error.message loc (Error.Econst_variable_already_defined c)
    else NamesSet.add c local_const in
  let build local_const vd =
    _add_const_var loc vd.v_name local_const in
  List.fold_left build NamesSet.empty vd_list


(** {3 Translate the AST into Heptagon} *)
let translate_iterator_type = function
  | Imap -> Heptagon.Imap
  | Imapi -> Heptagon.Imapi
  | Ifold -> Heptagon.Ifold
  | Ifoldi -> Heptagon.Ifoldi
  | Imapfold -> Heptagon.Imapfold

let rec translate_static_exp se =
  try
    let se_d = translate_static_exp_desc se.se_loc se.se_desc in
    Types.mk_static_exp Types.Tinvalid ~loc:se.se_loc se_d
  with
    | ScopingError err -> Error.message se.se_loc err

and translate_static_exp_desc _loc ed =
  let t = translate_static_exp in
  match ed with
    | Svar (Q q) -> Types.Svar q
    | Svar (ToQ _) -> assert false
    | Sint i -> Types.Sint i
    | Sfloat f -> Types.Sfloat f
    | Sbool b -> Types.Sbool b
    | Sstring s -> Types.Sstring s
    | Sconstructor c -> Types.Sconstructor (qualify_constrs c)
    | Sfield c -> Types.Sfield (qualify_field c)
    | Stuple se_list -> Types.Stuple (List.map t se_list)
    | Sarray_power (se,sn) -> Types.Sarray_power (t se, List.map t sn)
    | Sarray se_list -> Types.Sarray (List.map t se_list)
    | Srecord se_f_list ->
        let qualf (f, se) = (qualify_field f, t se) in
        Types.Srecord (List.map qualf se_f_list)
    | Sop (fn, se_list) -> Types.Sop (qualify_value fn, List.map t se_list)

let expect_static_exp e = match e.e_desc with
  | Econst se -> translate_static_exp se
  | _ ->  Error.message e.e_loc Estatic_exp_expected

let rec translate_type loc tenv ty =
  try
    (match ty with
      | Tprod ty_list ->
          Types.Tprod(List.map (translate_type loc tenv) ty_list)
      | Tid ln ->
        let unqualified_name = Hept_parsetree.unqualify ln in
        if (RenameType.mem unqualified_name tenv)  (* Is the type defined locally to the node? *)
          then (
            try
              let tvd = RenameType.find unqualified_name tenv in
              let nameclass = tvd.t_nameclass in
              Types.Tclasstype (current_qual unqualified_name, find_class (qualify_class (ToQ nameclass)))
            with Not_found -> assert false;
          )
          else Types.Tid (qualify_type ln)
      | Tarray (ty, e) ->
          let ty = translate_type loc tenv ty in
          Types.Tarray (ty, expect_static_exp e)
      | Tinvalid -> Types.Tinvalid
    )
  with
    | ScopingError err -> Error.message loc err

let rec translate_some_clock loc env ck = match ck with
  | None -> Clocks.fresh_clock()
  | Some(ck) -> translate_clock loc env ck

and translate_clock loc env ck = match ck with
  | Cbase -> Clocks.Cbase
  | Con(ck,c,x) -> Clocks.Con(translate_clock loc env ck, qualify_constrs c, Rename.var loc env x)

let rec translate_some_one_clock isInOutput loc env ock = match ock with
  | None ->
    if isInOutput then
      Clocks.base_osynch_clock
    else
      Clocks.fresh_osynch_period 1  (* Local var is period 1 by default *)
  | Some ock -> translate_one_clock loc env ock

and translate_one_clock loc env ock = match ock with
  | Cone (ph, per) -> Clocks.Cone (ph, per)
  | Cper per -> Clocks.fresh_osynch_period per

let rec translate_ct loc env ct = match ct with
  | Ck ck -> Clocks.Ck (translate_clock loc env ck)
  | Cprod c_l -> Clocks.Cprod (List.map (translate_ct loc env) c_l)

let rec translate_one_ct loc env oct = match oct with
  | Hept_parsetree.Ock ck -> Clocks.Ock (translate_one_clock loc env ck)
  | Hept_parsetree.Ocprod c_l -> Clocks.Ocprod (List.map (translate_one_ct loc env) c_l)


let rec translate_exp env e =
  try
    { Heptagon.e_desc = translate_desc e.e_loc env e.e_desc;
      Heptagon.e_ty = Types.invalid_type;
      Heptagon.e_linearity = Linearity.Ltop;
      Heptagon.e_level_ck = Clocks.Cbase;
      Heptagon.e_ct_annot = Misc.optional (translate_ct e.e_loc env) e.e_ct_annot;
      Heptagon.e_loc = e.e_loc }
  with ScopingError(error) -> Error.message e.e_loc error

and translate_desc loc env = function
  | Econst c -> Heptagon.Econst (translate_static_exp c)
  | Evar x -> Heptagon.Evar (Rename.var loc env x)
  | Elast x -> Heptagon.Elast (Rename.last loc env x)
  | Epre (None, e) -> Heptagon.Epre (None, translate_exp env e)
  | Epre (Some c, e) ->
      Heptagon.Epre (Some (expect_static_exp c),
                     translate_exp env e)
  | Efby (e1, e2) -> Heptagon.Efby (translate_exp env e1,
                                    translate_exp env e2)
  | Estruct f_e_list ->
      let f_e_list =
        List.map (fun (f,e) -> qualify_field f, translate_exp env e)
          f_e_list in
      Heptagon.Estruct f_e_list
  | Eapp ({ a_op = op; a_params = params; a_inlined = inl }, e_list) ->
      let e_list = List.map (translate_exp env) e_list in
      let params = List.map (expect_static_exp) params in
      let app = mk_app ~params:params ~inlined:inl (translate_op op) in
      Heptagon.Eapp (app, e_list, None)

  | Eiterator (it, { a_op = op; a_params = params }, n_list, pe_list, e_list) ->
      let e_list = List.map (translate_exp env) e_list in
      let pe_list = List.map (translate_exp env) pe_list in
      let n_list = List.map expect_static_exp n_list in
      let params = List.map (expect_static_exp) params in
      let app = mk_app ~params:params (translate_op op) in
      Heptagon.Eiterator (translate_iterator_type it,
                          app, n_list, pe_list, e_list, None)
  | Ewhen (e, c, x) ->
      let x = Rename.var loc env x in
      let e = translate_exp env e in
      let c = qualify_constrs c in
      Heptagon.Ewhen (e, c, x)
  | Emerge (x, c_e_list) ->
      let x = Rename.var loc env x in
      let c_e_list =
        let fun_c_e (c, e) =
          let e = translate_exp env e in
          let c = qualify_constrs c in
          (c, e) in
        List.map fun_c_e c_e_list in
      Heptagon.Emerge (x, c_e_list)
  | Ecurrent (c, x, eInit, e) ->
      let c = qualify_constrs c in
      let x = Rename.var loc env x in
      let eInit = translate_exp env eInit in
      let e = translate_exp env e in
      Heptagon.Ecurrent (c, x, eInit, e)
  | Esplit (x, e1) ->
    let x = translate_exp env (mk_exp (Evar x) loc) in
    let e1 = translate_exp env e1 in
      Heptagon.Esplit(x, e1)
  | Ewhenmodel (e1, (ph,per)) ->
    let e1 = translate_exp env e1 in
    Heptagon.Ewhenmodel (e1, (ph,per))
  | Ecurrentmodel ((ph,per), seInit, e1) ->
    let seInit = translate_static_exp seInit in
    let e1 = translate_exp env e1 in
    Heptagon.Ecurrentmodel ((ph,per), seInit, e1)
  | Edelay (d, e1) ->
    let e1 = translate_exp env e1 in
    Heptagon.Edelay (d, e1)
  | Edelayfby (d, seInit, e1) ->
    let seInit = translate_static_exp seInit in
    let e1 = translate_exp env e1 in
    Heptagon.Edelayfby (d, seInit, e1)
  | Ebuffer e1 ->
    let e1 = translate_exp env e1 in
    Heptagon.Ebuffer e1
  | Ebufferfby (seInit, e1) ->
    let seInit = translate_static_exp seInit in
    let e1 = translate_exp env e1 in
    Heptagon.Ebufferfby (seInit, e1)
  | Ebufferlat (l, e1) ->
    let e1 = translate_exp env e1 in
    Heptagon.Ebufferlat (l, e1)


and translate_op = function
  | Earrow -> Heptagon.Earrow
  | Eifthenelse -> Heptagon.Eifthenelse
  | Efield -> Heptagon.Efield
  | Efield_update -> Heptagon.Efield_update
  | Etuple -> Heptagon.Etuple
  | Earray -> Heptagon.Earray
  | Eselect -> Heptagon.Eselect
  | Eupdate -> Heptagon.Eupdate
  | Earray_fill -> Heptagon.Earray_fill
  | Eselect_slice -> Heptagon.Eselect_slice
  | Econcat -> Heptagon.Econcat
  | Eselect_dyn -> Heptagon.Eselect_dyn
  | Eselect_trunc -> Heptagon.Eselect_trunc
  | Efun ln -> Heptagon.Efun (qualify_value ln)
  | Enode ln -> Heptagon.Enode (qualify_value ln)
  | Ereinit -> Heptagon.Ereinit

and translate_pat loc env = function
  | Evarpat x -> Heptagon.Evarpat (Rename.var loc env x)
  | Etuplepat l -> Heptagon.Etuplepat (List.map (translate_pat loc env) l)

let rec translate_eq env tenv eq =
  let init = match eq.eq_desc with | Eeq(_, init, _) -> init | _ -> Linearity.Lno_init in
  { Heptagon.eq_desc = translate_eq_desc eq.eq_loc env tenv eq.eq_desc ;
    Heptagon.eq_stateful = false;
    Heptagon.eq_inits = init;
    Heptagon.eq_loc = eq.eq_loc; }

and translate_eq_desc loc env tenv = function
  | Eswitch(e, switch_handlers) ->
      let sh = List.map
        (translate_switch_handler loc env tenv)
        switch_handlers in
      Heptagon.Eswitch (translate_exp env e, sh)
  | Eeq(p, _, e) ->
      Heptagon.Eeq (translate_pat loc env p, translate_exp env e)
  | Epresent (present_handlers, b) ->
      Heptagon.Epresent
        (List.map (translate_present_handler env tenv) present_handlers
           , fst (translate_block env tenv b))
  | Eautomaton state_handlers ->
      Heptagon.Eautomaton (List.map (translate_state_handler env tenv)
                             state_handlers)
  | Ereset (b, e) ->
      let b, _ = translate_block env tenv b in
      Heptagon.Ereset (b, translate_exp env e)
  | Eblock b ->
      let b, _ = translate_block env tenv b in
      Heptagon.Eblock b

and translate_eqm_annot eqmann =
  let desc = match eqmann.anneqm_desc with
    | Anneqm_minphase m -> Heptagon.Anneqm_minphase m
    | Anneqm_maxphase m -> Heptagon.Anneqm_maxphase m
    | Anneqm_label ln -> Heptagon.Anneqm_label ln
  in
  { Heptagon.anneqm_desc = desc;
    Heptagon.anneqm_loc = eqmann.anneqm_loc; }

and translate_eq_model env eqm =
  { Heptagon.eqm_lhs = translate_pat eqm.eqm_loc env eqm.eqm_lhs;
    Heptagon.eqm_rhs = translate_exp env eqm.eqm_rhs;
    Heptagon.eqm_clk = translate_some_one_clock false eqm.eqm_loc env None;
    Heptagon.eqm_stateful = false;
    Heptagon.eqm_annot = List.map translate_eqm_annot eqm.eqm_annot;
    Heptagon.eqm_loc = eqm.eqm_loc; }

and translate_block env tenv b =
  let env = Rename.append env b.b_local in
  { Heptagon.b_local = translate_vd_list env tenv b.b_local;
    Heptagon.b_equs = List.map (translate_eq env tenv) b.b_equs;
    Heptagon.b_defnames = Env.empty;
    Heptagon.b_stateful = false;
    Heptagon.b_loc = b.b_loc; }, env

and translate_bm_annot bmann =
  let desc = match bmann.annm_desc with
    | Ann_range (l, u, lab1, lab2) -> Heptagon.Ann_range (l, u, lab1, lab2)
    | Ann_before (lab1, lab2) -> Heptagon.Ann_before (lab1, lab2)
  in
  { Heptagon.annm_desc = desc;
    Heptagon.annm_loc = bmann.annm_loc; }

and translate_block_model env bm =
  let env = Rename.append_vdm env bm.bm_local in
  { Heptagon.bm_local = translate_vd_model_list false env bm.bm_local;
    Heptagon.bm_eqs = List.map (translate_eq_model env) bm.bm_eqs;
    Heptagon.bm_annot = List.map translate_bm_annot bm.bm_annot;
    Heptagon.bm_loc = bm.bm_loc }, env

and translate_state_handler env tenv sh =
  let b, env = translate_block env tenv sh.s_block in
  { Heptagon.s_state = sh.s_state;
    Heptagon.s_block = b;
    Heptagon.s_until = List.map (translate_escape env) sh.s_until;
    Heptagon.s_unless =
      List.map (translate_escape env) sh.s_unless; }

and translate_escape env esc =
  { Heptagon.e_cond = translate_exp env esc.e_cond;
    Heptagon.e_reset = esc.e_reset;
    Heptagon.e_next_state = esc.e_next_state }

and translate_present_handler env tenv ph =
  { Heptagon.p_cond = translate_exp env ph.p_cond;
    Heptagon.p_block = fst (translate_block env tenv ph.p_block) }

and translate_switch_handler loc env tenv sh =
  try
    { Heptagon.w_name = qualify_constrs sh.w_name;
      Heptagon.w_block = fst (translate_block env tenv sh.w_block) }
  with
    | ScopingError err -> Error.message loc err

and translate_var_dec env tenv vd =
  (* env is initialized with the declared vars before their translation *)
    { Heptagon.v_ident = Rename.var vd.v_loc env vd.v_name;
      Heptagon.v_type = translate_type vd.v_loc tenv vd.v_type;
      Heptagon.v_linearity = Linearity.check_linearity vd.v_linearity;
      Heptagon.v_last = translate_last vd.v_last;
      Heptagon.v_clock = translate_some_clock vd.v_loc env vd.v_clock;
      Heptagon.v_loc = vd.v_loc }

(** [env] should contain the declared variables prior to this translation *)
and translate_vd_list env tenv =
  List.map (translate_var_dec env tenv)

and translate_var_dec_model isInOutput env vdm =
  { Heptagon.vm_ident = Rename.var vdm.vm_loc env vdm.vm_ident;
    Heptagon.vm_type = translate_type vdm.vm_loc RenameType.empty vdm.vm_type;
    Heptagon.vm_clock = translate_some_one_clock isInOutput vdm.vm_loc env vdm.vm_clock;
    Heptagon.vm_loc = vdm.vm_loc }


and translate_vd_model_list isInOutput env =
  List.map (translate_var_dec_model isInOutput env)

and translate_last = function
  | Var -> Heptagon.Var
  | Last (None) -> Heptagon.Last None
  | Last (Some e) -> Heptagon.Last (Some (expect_static_exp e))

let translate_objective_kind obj =
  match obj with
  | Obj_enforce    -> Heptagon.Obj_enforce
  | Obj_reachable  -> Heptagon.Obj_reachable
  | Obj_attractive -> Heptagon.Obj_attractive

let translate_objective env obj =
  { Heptagon.o_kind = translate_objective_kind obj.o_kind;
    Heptagon.o_exp = translate_exp env obj.o_exp
  }

let translate_contract env tenv opt_ct =
  match opt_ct with
  | None -> None, env
  | Some ct ->
      let env' = Rename.append env ct.c_controllables in
      let b, env = translate_block env tenv ct.c_block in
      Some { Heptagon.c_assume = translate_exp env ct.c_assume;
             Heptagon.c_objectives = List.map (translate_objective env) ct.c_objectives;
             Heptagon.c_assume_loc = translate_exp env ct.c_assume_loc;
             Heptagon.c_enforce_loc = translate_exp env ct.c_enforce_loc;
             Heptagon.c_controllables = translate_vd_list env' tenv ct.c_controllables;
             Heptagon.c_block = b }, env'

let params_of_var_decs env p_l =
  let pofvd env vd =
    let env = Rename.add_used_name env vd.v_name in
    Signature.mk_param vd.v_name (translate_type vd.v_loc RenameType.empty vd.v_type), env
  in
  Misc.mapfold pofvd env p_l


let translate_constrnt e = expect_static_exp e

(*
let args_of_var_decs =
  let arg_of_vd vd =
    if Linearity.is_linear vd.v_linearity && not !Compiler_options.do_mem_alloc then
      message vd.v_loc Elinear_type_no_memalloc
    else
      Signature.mk_arg ~linearity:vd.v_linearity
        (Some vd.v_name)
        (translate_type vd.v_loc vd.v_type)
  in
    List.map arg_of_vd
*)

let translate_typeparam_dec loc tenv tparamdec =
  try
    let tenv = RenameType.add loc tenv tparamdec in (* Add tparamdec to the typing environment *)
    { Heptagon.t_nametype = current_qual tparamdec.t_nametype;
      Heptagon.t_nameclass = qualify_class (ToQ tparamdec.t_nameclass) }, tenv
  with
    | ScopingError err -> Error.message loc err

let translate_node node =
  let n = current_qual node.n_name in
  Idents.enter_node n;
  let params, env = params_of_var_decs Rename.empty node.n_params in
  
  (* Getting the local type environment and the type parameter declarations of the node *)
  let (typeparamdecs, tenv) = List.fold_left
    (fun (tres,env) tpd ->
      let (hres, env1) = translate_typeparam_dec node.n_loc env tpd in
      (hres::tres, env1) )
    ([], RenameType.empty)
    node.n_typeparams in
  
  let constraints = List.map translate_constrnt node.n_constraints in
  let env = Rename.append env (node.n_input) in
  (* inputs should refer only to inputs *)
  let inputs = translate_vd_list env tenv node.n_input in
  (* Inputs and outputs define the initial local env *)
  let env0 = Rename.append env node.n_output in
  let outputs = translate_vd_list env0 tenv node.n_output in
  (* Enrich env with controllable variables (used in block) *)
  let contract, env = translate_contract env0 tenv node.n_contract in
  let b, _ = translate_block env tenv node.n_block in
  (* add the node signature to the environment *)
  let nnode = { Heptagon.n_name = n;
               Heptagon.n_stateful = node.n_stateful;
               Heptagon.n_unsafe = node.n_unsafe;
               Heptagon.n_typeparamdecs = typeparamdecs;
               Heptagon.n_input = inputs;
               Heptagon.n_output = outputs;
               Heptagon.n_contract = contract;
               Heptagon.n_block = b;
               Heptagon.n_loc = node.n_loc;
               Heptagon.n_params = params;
               Heptagon.n_param_constraints = constraints; }
  in
  safe_add node.n_loc add_value n (Hept_utils.signature_of_node nnode);
  nnode

let translate_model md =
  let n = current_qual md.Hept_parsetree.m_name in
  let env = Rename.append_vdm Rename.empty md.m_input in
  let linputs = translate_vd_model_list true env md.m_input in
  let env = Rename.append_vdm env md.m_output in
  let loutputs = translate_vd_model_list true env md.m_output in
  let bm, _ = translate_block_model env md.m_block in

  let mmodel = {
    Heptagon.m_name = n;
    Heptagon.m_input = linputs;
    Heptagon.m_output = loutputs;
    Heptagon.m_block = bm;
    Heptagon.m_loc = md.m_loc;
  } in
  mmodel

let translate_typedec ty =
    let n = current_qual ty.t_name in
    let tydesc = match ty.t_desc with
      | Type_abs ->
          safe_add ty.t_loc add_type n Signature.Tabstract;
          Heptagon.Type_abs
      | Type_alias t ->
          let t = translate_type ty.t_loc RenameType.empty t in
          safe_add ty.t_loc add_type n (Signature.Talias t);
          Heptagon.Type_alias t
      | Type_enum(tag_list) ->
          let tag_list = List.map current_qual tag_list in
          List.iter (fun tag -> add_constrs tag n) tag_list;
          safe_add ty.t_loc add_type n (Signature.Tenum tag_list);
          Heptagon.Type_enum tag_list
      | Type_struct(field_ty_list) ->
          let translate_field_type (f,t) =
            let f = current_qual f in
            let t = translate_type ty.t_loc RenameType.empty t in
            add_field f n;
            Signature.mk_field f t in
          let field_list = List.map translate_field_type field_ty_list in
          safe_add ty.t_loc add_type n (Signature.Tstruct field_list);
          Heptagon.Type_struct field_list in
    { Heptagon.t_name = n;
      Heptagon.t_desc = tydesc;
      Heptagon.t_loc = ty.t_loc }

let translate_const_dec cd =
  let c_name = current_qual cd.c_name in
  let c_type = translate_type cd.c_loc RenameType.empty cd.c_type in
  let c_value = match cd.c_value with
    | None -> None
    | Some cval -> Some (expect_static_exp cval) in
  replace_const c_name (Signature.mk_const_def c_type c_value);
  { Heptagon.c_name = c_name;
    Heptagon.c_type = c_type;
    Heptagon.c_value = c_value;
    Heptagon.c_loc = cd.c_loc; }

let translate_classdec cd =
  try
    let c_nclass = current_qual cd.c_nameclass in
    let c_linsts = List.map (fun tyname -> qualify_type (ToQ tyname)) cd.c_insttypes in
    replace_class c_nclass (Types.mk_type_class c_nclass c_linsts);
    Hept_utils.mk_class_dec c_nclass c_linsts cd.c_loc
  with
    | ScopingError err -> Error.message cd.c_loc err


let translate_ressourcedec rd =
  try
    let r_qname = current_qual rd.r_name in
    replace_ressource r_qname (Signature.mk_ressource_def rd.r_name rd.r_max);    
    Hept_utils.mk_ressource_dec rd.r_name rd.r_max rd.r_loc
  with
    | ScopingError err -> Error.message rd.r_loc err

let translate_program p =
  let translate_program_desc pd = match pd with
    | Ppragma _ -> Misc.unsupported "pragma in scoping"
    | Pconst c -> Heptagon.Pconst (translate_const_dec c)
    | Ptype t -> Heptagon.Ptype (translate_typedec t)
    | Pclass c -> Heptagon.Pclass (translate_classdec c)
    | Pnode n -> Heptagon.Pnode (translate_node n)
    | Pmodel m -> Heptagon.Pmodel (translate_model m)
  in
  let desc = List.map translate_program_desc p.p_desc in
  { Heptagon.p_modname = Names.modul_of_string p.p_modname;
    Heptagon.p_opened = p.p_opened;
    Heptagon.p_desc = desc; }


(* --------------------------------------------------------- *)
let translate_signature s =
  let rec translate_some_clock ck = match ck with
    | None -> Signature.Cbase
    | Some ck -> translate_clock ck
  and translate_clock ck = match ck with
    | Cbase -> Signature.Cbase
    | Con(ck,c,x) -> Signature.Con(translate_clock ck, qualify_constrs c, x)
  and translate_arg tenv a =
    Signature.mk_arg a.a_name (translate_type s.sig_loc tenv a.a_type)
      a.a_linearity (translate_some_clock a.a_clock)
(*  and translate_ressource_util (nress, v) = ( (qualify_ressource nress), v) *)
  in
  let n = current_qual s.sig_name in
  let tp = List.map 
    (fun stp -> Signature.mk_typeparam_def stp.t_nametype stp.t_nameclass )
    s.sig_typeparams in
  
  let (tpdecs,tenv) = List.fold_left
    (fun (tres,env) tpd ->
      let (hres, env1) = translate_typeparam_dec s.sig_loc env tpd in
      (hres::tres, env1) )
    ([], RenameType.empty)
    s.sig_typeparams in
  
  let i = List.map (translate_arg tenv) s.sig_inputs in
  let o = List.map (translate_arg tenv) s.sig_outputs in
  let p, _ = params_of_var_decs Rename.empty s.sig_params in
  let c = List.map translate_constrnt s.sig_param_constraints in
  (*let lress_used = List.map translate_ressource_util s.sig_ressource in *)

  let sig_node =
    Signature.mk_node
      ~extern:s.sig_external ~typeparams:tp s.sig_loc i o s.sig_stateful s.sig_unsafe p
      ~lressutil:s.sig_ressource ~owcet:s.sig_wcet in
  Check_signature.check_signature sig_node;
  safe_add s.sig_loc add_value n sig_node;
  mk_signature n ~typeparamdecs:tpdecs i o s.sig_stateful p c s.sig_wcet
      s.sig_ressource s.sig_loc ~extern:s.sig_external


let translate_interface_desc = function
  | Itypedef tydec -> Heptagon.Itypedef (translate_typedec tydec)
  | Iconstdef const_dec -> Heptagon.Iconstdef (translate_const_dec const_dec)
  | Iclassdef cd -> Heptagon.Iclassdef (translate_classdec cd)
  | Iressourcedef rd ->  Heptagon.Iressourcedef (translate_ressourcedec rd)
  | Isignature s -> Heptagon.Isignature (translate_signature s)

let translate_interface i =
  let desc = List.map translate_interface_desc i.i_desc in
  { Heptagon.i_modname = Names.modul_of_string i.i_modname;
    Heptagon.i_opened = i.i_opened;
    Heptagon.i_desc = desc; }
