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
open Types
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
    | Equal_notfound of name*qualname
    | Equal_unbound of name*name
    | Enot_last of name
    | Evariable_already_defined of name
    | Econst_variable_already_defined of name
    | Estatic_exp_expected

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
      | Econst_variable_already_defined name ->
          eprintf "%aThe const variable %s is already defined.@."
            print_location loc
            name
      | Estatic_exp_expected ->
          eprintf "%aA static expression was expected.@."
            print_location loc
    end;
    raise Errors.Error

  exception ScopingError of error

  let error kind = raise (ScopingError(kind))
end

open Error


(** {3 Qualify when ToQ and check when Q according to the global env } *)

let _qualify_with_error s qfun cqfun q = match q with
  | ToQ name ->
      (try qfun name with Not_found -> error (Equal_unbound (s,name)))
  | Q q ->
      if cqfun q then q else error (Equal_notfound (s,q))

let qualify_value = _qualify_with_error "value" qualify_value check_value
let qualify_type = _qualify_with_error "type" qualify_type check_type
let qualify_constrs =
  _qualify_with_error "constructor" qualify_constrs check_constrs
let qualify_field = _qualify_with_error "field" qualify_field check_field

(** Qualify a var name as a constant variable,
    if not in local_const or global_const then raise Not_found *)
let qualify_var_as_const local_const c =
  if S.mem c local_const
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
  open Error
  include
    (Map.Make (struct type t = string let compare = String.compare end))
  (** Rename a var *)
  let var loc env n =
    try fst (find n env)
    with Not_found -> message loc (Evar_unbound n)
  (** Rename a last *)
  let last loc env n =
    try
      let id, last = find n env in
      if not last then message loc (Enot_last n) else id
    with Not_found -> message loc (Evar_unbound n)
  (** Add a var *)
  let add_var loc env n =
    if mem n env then message loc (Evariable_already_defined n)
    else
        add n (ident_of_name n, false) env
  (** Add a last *)
  let add_last loc env n =
    if mem n env then message loc (Evariable_already_defined n)
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
end


(** Function to build the defined static parameters set *)
let build_const loc vd_list =
  let _add_const_var loc c local_const =
    if S.mem c local_const
    then Error.message loc (Error.Econst_variable_already_defined c)
    else S.add c local_const in
  let build local_const vd =
    _add_const_var loc vd.v_name local_const in
  List.fold_left build S.empty vd_list


(** { 3 Translate the AST into Heptagon. } *)
let translate_iterator_type = function
  | Imap -> Heptagon.Imap
  | Ifold -> Heptagon.Ifold
  | Ifoldi -> Heptagon.Ifoldi
  | Imapfold -> Heptagon.Imapfold

(** convention : static params are set as the first static args,
    op<a1,a2> (a3) == op <a1> (a2,a3) == op (a1,a2,a3) *)
let static_app_from_app app args=
  match app.a_op with
    | Efun (Q ({ qual = "Pervasives" } as q))
    | Enode (Q ({ qual = "Pervasives" } as q)) ->
        q, (app.a_params @ args)
    | _ -> raise Not_static

let rec translate_static_exp local_const se =
  try
    let se_d = translate_static_exp_desc local_const se.se_desc in
    Types.mk_static_exp ~loc:se.se_loc se_d
  with
    | ScopingError err -> message se.se_loc err

and translate_static_exp_desc local_const ed =
  let t = translate_static_exp local_const in
  match ed with
    | Svar q -> Types.Svar (qualify_const local_const q)
    | Sint i -> Types.Sint i
    | Sfloat f -> Types.Sfloat f
    | Sbool b -> Types.Sbool b
    | Sconstructor c -> Types.Sconstructor (qualify_constrs c)
    | Sfield c -> Types.Sfield (qualify_field c)
    | Stuple se_list -> Types.Stuple (List.map t se_list)
    | Sarray_power (se,sn) -> Types.Sarray_power (t se, t sn)
    | Sarray se_list -> Types.Sarray (List.map t se_list)
    | Srecord se_f_list ->
        let qualf (f, se) = (qualify_field f, t se) in
        Types.Srecord (List.map qualf se_f_list)
    | Sop (fn, se_list) -> Types.Sop (qualify_value fn, List.map t se_list)

let rec static_exp_of_exp local_const e =
  try
    let t = static_exp_of_exp local_const in
    let desc = match e.e_desc with
      | Evar n -> Types.Svar (qualify_const local_const (ToQ n))
      | Econst se -> translate_static_exp_desc local_const se.se_desc
      | Eapp({ a_op = Earray_fill; a_params = [n] }, [e]) ->
          Types.Sarray_power (t e, t n)
      | Eapp({ a_op = Earray }, e_list) ->
          Types.Sarray (List.map t e_list)
      | Eapp({ a_op = Etuple }, e_list) ->
          Types.Stuple (List.map t e_list)
      | Eapp(app, e_list) ->
          let op, args = static_app_from_app app e_list in
          Types.Sop (op, List.map t args)
      | Estruct e_list ->
          Types.Srecord (List.map (fun (f,e) -> qualify_field f, t e) e_list)
      | _ -> raise Not_static in
    Types.mk_static_exp ~loc:e.e_loc desc
  with
    | ScopingError err -> message e.e_loc err

let expect_static_exp local_const e =
  try static_exp_of_exp local_const e
  with Not_static -> message e.e_loc Estatic_exp_expected

let rec translate_type loc local_const ty =
  try
    (match ty with
      | Tprod ty_list ->
          Types.Tprod(List.map (translate_type loc local_const) ty_list)
      | Tid ln -> Types.Tid (qualify_type ln)
      | Tarray (ty, e) ->
          let ty = translate_type loc local_const ty in
          Types.Tarray (ty, expect_static_exp local_const e))
  with
    | ScopingError err -> message loc err


and translate_exp local_const env e =
  try
    let desc =
      (*try (* try to see if the exp is a constant *)
        Heptagon.Econst (static_exp_of_exp local_const e)
        with
        Not_static -> *) translate_desc e.e_loc local_const env e.e_desc in
    { Heptagon.e_desc = desc;
      Heptagon.e_ty = Types.invalid_type;
      Heptagon.e_loc = e.e_loc }
  with ScopingError(error) -> message e.e_loc error

and translate_desc loc local_const env = function
  | Econst c -> Heptagon.Econst (translate_static_exp local_const c)
  | Evar x -> (
      try (* First check if it is a const var *)
        Heptagon.Econst
          (Types.mk_static_exp
             ~loc:loc (Types.Svar (qualify_var_as_const local_const x)))
      with Not_found -> Heptagon.Evar (Rename.var loc env x))
  | Elast x -> Heptagon.Elast (Rename.last loc env x)
  | Epre (None, e) -> Heptagon.Epre (None, translate_exp local_const env e)
  | Epre (Some c, e) ->
      Heptagon.Epre (Some (expect_static_exp local_const c),
                     translate_exp local_const env e)
  | Efby (e1, e2) -> Heptagon.Efby (translate_exp local_const env e1,
                                    translate_exp local_const env e2)
  | Estruct f_e_list ->
      let f_e_list =
        List.map (fun (f,e) -> qualify_field f, translate_exp local_const env e)
          f_e_list in
      Heptagon.Estruct f_e_list
  | Eapp ({ a_op = op; a_params = params }, e_list) ->
      let e_list = List.map (translate_exp local_const env) e_list in
      let params = List.map (expect_static_exp local_const) params in
      let app = Heptagon.mk_op ~params:params (translate_op op) in
      Heptagon.Eapp (app, e_list, None)
  | Eiterator (it, { a_op = op; a_params = params }, n, e_list) ->
      let e_list = List.map (translate_exp local_const env) e_list in
      let n = expect_static_exp local_const n in
      let params = List.map (expect_static_exp local_const) params in
      let app = Heptagon.mk_op ~params:params (translate_op op) in
      Heptagon.Eiterator (translate_iterator_type it,
                          app, n, e_list, None)

and translate_op = function
  | Eequal -> Heptagon.Eequal
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
  | Efun ln -> Heptagon.Efun (qualify_value ln)
  | Enode ln -> Heptagon.Enode (qualify_value ln)

and translate_pat loc env = function
  | Evarpat x -> Heptagon.Evarpat (Rename.var loc env x)
  | Etuplepat l -> Heptagon.Etuplepat (List.map (translate_pat loc env) l)

let rec translate_eq local_const env eq =
  { Heptagon.eq_desc = translate_eq_desc eq.eq_loc local_const env eq.eq_desc ;
    Heptagon.eq_statefull = false;
    Heptagon.eq_loc = eq.eq_loc }

and translate_eq_desc loc local_const env = function
  | Eswitch(e, switch_handlers) ->
      let sh = List.map
        (translate_switch_handler loc local_const env)
        switch_handlers in
      Heptagon.Eswitch (translate_exp local_const env e, sh)
  | Eeq(p, e) ->
      Heptagon.Eeq (translate_pat loc env p, translate_exp local_const env e)
  | Epresent (present_handlers, b) ->
      Heptagon.Epresent
        (List.map (translate_present_handler local_const env) present_handlers
           , fst (translate_block local_const env b))
  | Eautomaton state_handlers ->
      Heptagon.Eautomaton (List.map (translate_state_handler local_const env)
                             state_handlers)
  | Ereset (b, e) ->
      let b, _ = translate_block local_const env b in
      Heptagon.Ereset (b, translate_exp local_const env e)

and translate_block local_const env b =
  let env = Rename.append env b.b_local in
  { Heptagon.b_local = translate_vd_list local_const env b.b_local;
    Heptagon.b_equs = List.map (translate_eq local_const env) b.b_equs;
    Heptagon.b_defnames = Env.empty;
    Heptagon.b_statefull = false;
    Heptagon.b_loc = b.b_loc }, env

and translate_state_handler local_const env sh =
  let b, env = translate_block local_const env sh.s_block in
  { Heptagon.s_state = sh.s_state;
    Heptagon.s_block = b;
    Heptagon.s_until = List.map (translate_escape local_const env) sh.s_until;
    Heptagon.s_unless =
      List.map (translate_escape local_const env) sh.s_unless; }

and translate_escape local_const env esc =
  { Heptagon.e_cond = translate_exp local_const env esc.e_cond;
    Heptagon.e_reset = esc.e_reset;
    Heptagon.e_next_state = esc.e_next_state }

and translate_present_handler local_const env ph =
  { Heptagon.p_cond = translate_exp local_const env ph.p_cond;
    Heptagon.p_block = fst (translate_block local_const env ph.p_block) }

and translate_switch_handler loc local_const env sh =
  try
    { Heptagon.w_name = qualify_constrs sh.w_name;
      Heptagon.w_block = fst (translate_block local_const env sh.w_block) }
  with
    | ScopingError err -> message loc err

and translate_var_dec local_const env vd =
  (* env is initialized with the declared vars before their translation *)
    { Heptagon.v_ident = Rename.var vd.v_loc env vd.v_name;
      Heptagon.v_type = translate_type vd.v_loc local_const vd.v_type;
      Heptagon.v_last = translate_last local_const vd.v_last;
      Heptagon.v_loc = vd.v_loc }

and translate_vd_list local_const env =
  List.map (translate_var_dec local_const env)

and translate_last local_const = function
  | Var -> Heptagon.Var
  | Last (None) -> Heptagon.Last None
  | Last (Some e) -> Heptagon.Last (Some (expect_static_exp local_const e))

let translate_contract local_const env ct =
  let b, _ = translate_block local_const env ct.c_block in
  { Heptagon.c_assume = translate_exp local_const env ct.c_assume;
    Heptagon.c_enforce = translate_exp local_const env ct.c_enforce;
    Heptagon.c_block = b }

let params_of_var_decs local_const =
  List.map (fun vd -> Signature.mk_param
                        vd.v_name
                        (translate_type vd.v_loc local_const vd.v_type))

let args_of_var_decs local_const =
  List.map (fun vd -> Signature.mk_arg
                        (Some vd.v_name)
                        (translate_type vd.v_loc local_const vd.v_type))

let translate_node node =
  Idents.new_function ();
  (* Node's params go to local_const env *)
  let local_const = build_const node.n_loc node.n_params in
  (* Inputs and outputs define the initial local env *)
  let env0 = Rename.append Rename.empty (node.n_input @ node.n_output) in
  let params = params_of_var_decs local_const node.n_params in
  let inputs = translate_vd_list local_const env0 node.n_input in
  let outputs = translate_vd_list local_const env0 node.n_output in
  let b, env = translate_block local_const env0 node.n_block in
  let contract =
    Misc.optional (translate_contract local_const env) node.n_contract in
  (* the env of the block is used in the contract translation *)
  let n = current_qual node.n_name in
  (* add the node signature to the environment *)
  let i = args_of_var_decs local_const node.n_input in
  let o = args_of_var_decs local_const node.n_output in
  let p = params_of_var_decs local_const node.n_params in
  add_value n (Signature.mk_node i o node.n_statefull p);
  { Heptagon.n_name = n;
    Heptagon.n_statefull = node.n_statefull;
    Heptagon.n_input = inputs;
    Heptagon.n_output = outputs;
    Heptagon.n_contract = contract;
    Heptagon.n_block = b;
    Heptagon.n_loc = node.n_loc;
    Heptagon.n_params = params;
    Heptagon.n_params_constraints = []; }

let translate_typedec ty =
    let n = current_qual ty.t_name in
    let tydesc = match ty.t_desc with
      | Type_abs ->
          add_type n Signature.Tabstract;
          Heptagon.Type_abs
      | Type_alias t ->
          let t = translate_type ty.t_loc S.empty t in
          add_type n (Signature.Talias t);
          Heptagon.Type_alias t
      | Type_enum(tag_list) ->
          let tag_list = List.map current_qual tag_list in
          List.iter (fun tag -> add_constrs tag n) tag_list;
          add_type n (Signature.Tenum tag_list);
          Heptagon.Type_enum tag_list
      | Type_struct(field_ty_list) ->
          let translate_field_type (f,t) =
            let f = current_qual f in
            let t = translate_type ty.t_loc S.empty t in
            add_field f n;
            Signature.mk_field f t in
          let field_list = List.map translate_field_type field_ty_list in
          add_type n (Signature.Tstruct field_list);
          Heptagon.Type_struct field_list in
    { Heptagon.t_name = n;
      Heptagon.t_desc = tydesc;
      Heptagon.t_loc = ty.t_loc }


let translate_const_dec cd =
  let c_name = current_qual cd.c_name in
  let c_type = translate_type cd.c_loc S.empty cd.c_type in
  let c_value = expect_static_exp S.empty cd.c_value in
  add_const c_name (Signature.mk_const_def c_type c_value);
  { Heptagon.c_name = c_name;
    Heptagon.c_type = c_type;
    Heptagon.c_value = c_value;
    Heptagon.c_loc = cd.c_loc; }

let translate_program p =
  List.iter open_module p.p_opened;
  let consts = List.map translate_const_dec p.p_consts in
  let types = List.map translate_typedec p.p_types in
  let nodes = List.map translate_node p.p_nodes in
  { Heptagon.p_modname = p.p_modname;
    Heptagon.p_opened = p.p_opened;
    Heptagon.p_types = types;
    Heptagon.p_nodes = nodes;
    Heptagon.p_consts = consts; }

let translate_signature s =
  let local_const = build_const s.sig_loc s.sig_params in
  let translate_arg a =
    Signature.mk_arg a.a_name (translate_type s.sig_loc local_const a.a_type) in
  let n = current_qual s.sig_name in
  let i = List.map translate_arg s.sig_inputs in
  let o = List.map translate_arg s.sig_outputs in
  let p = params_of_var_decs local_const s.sig_params in
  add_value n (Signature.mk_node i o s.sig_statefull p);
  Heptagon.mk_signature n i o s.sig_statefull p s.sig_loc


let translate_interface_desc = function
  | Iopen n -> open_module n; Heptagon.Iopen n
  | Itypedef tydec -> Heptagon.Itypedef (translate_typedec tydec)
  | Iconstdef const_dec -> Heptagon.Iconstdef (translate_const_dec const_dec)
  | Isignature s -> Heptagon.Isignature (translate_signature s)

let translate_interface_decl idecl =
  let desc = translate_interface_desc idecl.interf_desc in
  { Heptagon.interf_desc = desc;
    Heptagon.interf_loc = idecl.interf_loc }

let translate_interface i = List.map translate_interface_decl i

