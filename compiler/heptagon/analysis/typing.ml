(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* type checking *)

open Misc
open Names
open Name_utils
open Idents
open Location
open Modules
open Initial
open Static
open Signature
open Global_printer
open Heptagon
open Hept_mapfold
open Pp_tools
open Format

type value = { vd: var_dec; mutable last: bool }

type error =
  | Emissing of name
  | Emissingcase of name
  | Eundefined of name
  | Elast_undefined of name
  | Etype_clash of ty * ty
  | Eargs_clash of ty * ty
  | Earity_clash of int * int
  | Estatic_arity_clash of int * int
  | Ealready_defined of name
  | Enon_exaustive
  | Epartial_switch
  | Etoo_many_outputs
  | Esome_fields_are_missing
  | Esubscripted_value_not_an_array of ty
  | Earray_subscript_should_be_const
  | Eundefined_const of qualname
  | Econstraint_solve_failed of constrnt
  | Etype_should_be_static of ty
  | Erecord_type_expected of ty
  | Eno_such_field of ty * qualname
  | Eempty_record
  | Eempty_array
  | Efoldi_bad_args of ty
  | Emapi_bad_args of ty
  | Emerge_bad_sampler of ty * ty
  | Emerge_missing_constrs
  | Emerge_uniq
  | Emerge_mix of qualname
  | Epat_should_be_async of ty
  | Estatic_constraint of constrnt
  | Eshould_be_async of ty
  | Esplit_enum of ty
  | Esplit_tuple of ty
  | Eenable_memalloc
  | Ebad_format
  | Eformat_string_not_constant

exception Unify
exception Should_be_async of ty
exception TypingError of error

let error kind = raise (TypingError(kind))

let message loc kind =
  begin match kind with
    | Emissing(s) ->
        eprintf "%aNo equation is given for name %s.@."
          print_location loc
          s;
    | Emissingcase(s) ->
        eprintf "%aCase %s not defined.@."
          print_location loc
          s;
    | Eundefined(s) ->
        eprintf "%aThe name %s is unbound.@."
          print_location loc
          s;
    | Elast_undefined(s) ->
        eprintf "%aThe name %s does not have a last value.@."
          print_location loc
          s;
    | Etype_clash(expected_ty, actual_ty) ->
        eprintf "%aType Clash: this expression has type %a, @\n\
            but is expected to have type %a.@."
          print_location loc
          print_type actual_ty
          print_type expected_ty
    | Eargs_clash(expected_ty, actual_ty) ->
        eprintf "%aType Clash: arguments of type %a were given, @\n\
            but %a was expected.@."
          print_location loc
          print_type actual_ty
          print_type expected_ty
    | Earity_clash(expected_arit, actual_arit) ->
        eprintf "%aType Clash: this expression expects %d arguments,@\n\
            but is expected to have %d.@."
          print_location loc
          expected_arit actual_arit
    | Estatic_arity_clash(expected_arit, actual_arit) ->
        eprintf "%aType Clash: this node expects %d static parameters,@\n\
            but was given %d.@."
          print_location loc
          expected_arit actual_arit
    | Ealready_defined(s) ->
        eprintf "%aThe name %s is already defined.@."
          print_location loc
          s
    | Emerge_missing_constrs ->
        eprintf "%aSome constructors are missing in this merge@."
          print_location loc
    | Emerge_uniq ->
        eprintf "%aThe constructor is matched more than one time.@."
          print_location loc
    | Emerge_mix c ->
        eprintf "%aYou can't mix constructors from different types.@\n\
          The constructor %a is unexpected.@."
          print_location loc
          print_qualname c
    | Emerge_bad_sampler (exp_ty,ty) ->
        eprintf "%aThe first argument of merge is of type %a@\n\
                 but is expected to be of type %a@."
          print_location loc
          Global_printer.print_type ty
          Global_printer.print_type exp_ty
    | Enon_exaustive ->
        eprintf "%aSome constructors are missing in this pattern/matching.@."
          print_location loc
    | Epartial_switch ->
        eprintf "%aCases are missing.@."
          print_location loc
    | Etoo_many_outputs ->
        eprintf "%aA function may only returns a basic value.@."
          print_location loc
    | Esome_fields_are_missing ->
        eprintf "%aSome fields are missing.@."
          print_location loc
    | Esubscripted_value_not_an_array  ty ->
        eprintf "%aSubscript used on a non array type : %a.@."
          print_location loc
          Global_printer.print_type ty
    | Earray_subscript_should_be_const ->
        eprintf "%aSubscript has to be a static value.@."
          print_location loc
    | Eundefined_const ln ->
        eprintf "%aThe const name '%s' is unbound.@."
          print_location loc
          (fullname ln)
    | Econstraint_solve_failed c ->
        eprintf "%aThe following constraint cannot be satisified:@\n%a.@."
          print_location loc
          print_constrnt c
    | Etype_should_be_static ty ->
        eprintf "%aThis type should be static : %a.@."
          print_location loc
          print_type ty
    | Erecord_type_expected ty ->
        eprintf "%aA record was expected (found %a).@."
          print_location loc
          print_type ty
    | Eno_such_field (ty, f) ->
        eprintf "%aThe record type '%a' does not have a '%s' field.@."
          print_location loc
          print_type ty
          (shortname f)
    | Eempty_record ->
        eprintf "%aThe record is empty.@."
          print_location loc
    | Eempty_array ->
        eprintf "%aThe array is empty.@."
          print_location loc
    | Efoldi_bad_args  ty ->
        eprintf
          "%aThe function given to foldi should expect an integer \
               as the last but one argument (found: %a).@."
          print_location loc
          print_type ty
    | Epat_should_be_async ty ->
        eprintf "%aThis pattern is expected to be of async vars \
                   but the type found is %a.@."
          print_location loc
          print_type ty
    | Emapi_bad_args  ty ->
        eprintf
          "%aThe function given to mapi should expect an integer \
               as the last argument (found: %a).@."
          print_location loc
          print_type ty
    | Estatic_constraint c ->
        eprintf "%aThis application doesn't respect the static constraint :@\n%a.@."
          print_location loc
          print_static_exp c

    | Eshould_be_async ty ->
        eprintf "%aThis expression is expected to be async \
                   but the type found is %a.@."
          print_location loc
          print_type ty
    | Esplit_enum ty ->
        eprintf
          "%aThe first argument of split has to be an \
               enumerated type (found: %a).@."
          print_location loc
          print_type ty
    | Esplit_tuple ty ->
        eprintf
          "%aThe second argument of spit cannot \
               be a tuple (found: %a).@."
          print_location loc
          print_type ty
    | Eenable_memalloc ->
      eprintf
        "%aThis function was compiled with linear types. \
               Enable linear typing to call it.@."
          print_location loc
    | Ebad_format ->
      eprintf
        "%aThe format string is invalid@."
          print_location loc
    | Eformat_string_not_constant ->
      eprintf
        "%aA static format string was expected@."
          print_location loc
  end;
  raise Errors.Error

(** Add wrappers around Modules function to raise errors
    and display the correct location. *)
let find_with_error find_fun f =
  try find_fun f
  with Not_found -> error (Eundefined(fullname f))

let find_value v = find_with_error find_value v
let find_constrs c = Tid (find_with_error find_constrs c)
let find_field f = find_with_error find_field f


(** Helper functions to work with types *)
let element_type ty =
  match unalias_type ty with
    | Tarray (ty, _) -> ty
    | _ -> error (Esubscripted_value_not_an_array ty)

let array_size ty =
  match unalias_type ty with
    | Tarray (_, e) -> e
    | _ -> error (Esubscripted_value_not_an_array ty)

let unalias_type ty =
  try unalias_type ty
  with Undefined_type ln -> error (Eundefined (fullname ln))

let flatten_ty_list l =
  List.fold_right
    (fun arg args -> match arg with Tprod l -> l@args | a -> a::args ) l []

let kind f ty_desc =
  let ty_of_arg v =
    if Linearity.is_linear v.a_linearity && not !Compiler_options.do_linear_typing then
      error Eenable_memalloc;
    v.a_type
  in
  let op = if ty_desc.node_stateful then Enode f else Efun f in
    op, List.map ty_of_arg ty_desc.node_inputs,
  List.map ty_of_arg ty_desc.node_outputs

let typ_of_name h x =
  try
    let { vd = vd } = Env.find x h in vd.v_type
  with
      Not_found -> error (Eundefined(name x))

let typ_of_qual x = (Modules.find_const x).Signature.c_type

let sig_of_qual f = Modules.find_value f

let vd_of_name h x =
  try
    let { vd = vd } = Env.find x h in vd
  with
      Not_found -> error (Eundefined(name x))


let build_subst names values =
  if List.length names <> List.length values
  then error (Estatic_arity_clash (List.length names, List.length values));
  List.fold_left2 (fun m n v -> QualEnv.add n v m)
    QualEnv.empty names values

let add_distinct_env id vd env =
  if Env.mem id env then
    error (Ealready_defined(name id))
  else
    Env.add id vd env

let add_distinct_qualset n acc =
  if QualSet.mem n acc then
    error (Ealready_defined (fullname n))
  else
    QualSet.add n acc

let add_distinct_seset n acc =
  if SESet.mem n acc then
    error (Ealready_defined (Misc.print_pp_to_string print_static_exp n))
  else
    SESet.add n acc

let add_distinct_S n acc =
  if NamesSet.mem n acc then
    error (Ealready_defined n)
  else
    NamesSet.add n acc

(** Add two sets of names provided they are distinct *)
let add env1 env2 =
  Env.fold add_distinct_env env1 env2

(** Checks that constructors are included in constructor list from type
    def and returns the difference *)
let included_const s1 s2 =
  QualSet.iter
    (fun elt -> if not (QualSet.mem elt s2)
      then error (Emissingcase (fullname elt)))
    s1

let diff_const defined_names local_names =
  included_const local_names defined_names;
  QualSet.diff defined_names local_names

(** Checks that local_names are included in defined_names and returns
    the difference *)
let included_env s1 s2 =
  Env.iter
    (fun elt _ -> if not (Env.mem elt s2) then error (Emissing(name elt)))
    s1

let diff_env defined_names local_names =
  included_env local_names defined_names;
  Env.diff defined_names local_names

(** [merge [set1;...;setn]] returns a set of names defined in every seti
    and only partially defined names *)
let rec merge local_names_list =
  let two s1 s2 =
    let total, partial = Env.partition (fun elt -> Env.mem elt s2) s1 in
    let partial =
      Env.fold (fun elt vd env ->
                  if not (Env.mem elt total) then Env.add elt vd env
                  else env)
        s2 partial in
    total, partial in
  match local_names_list with
    | [] -> Env.empty, Env.empty
    | [s] -> s, Env.empty
    | s :: local_names_list ->
        let total, partial1 = merge local_names_list in
        let total, partial2 = two s total in
        total, Env.union partial1 partial2

(** Checks that every partial name has a last value *)
let all_last h env =
  Env.iter
    (fun elt _ ->
       if not (Env.find elt h).last
       then error (Elast_undefined(name elt)))
    env

let last = function | Var -> false | Last _ -> true

(** Checks that a field is not defined twice in a list
    of field name, exp.*)
let check_field_unicity l =
  let add_field acc (f,e) =
    if NamesSet.mem (shortname f) acc then
      message e.e_loc (Ealready_defined (fullname f))
    else
      NamesSet.add (shortname f) acc
  in
  ignore (List.fold_left add_field NamesSet.empty l)

(** Checks that a field is not defined twice in a list
    of field name, exp.*)
let check_static_field_unicity l =
  let add_field acc (f,se) =
    if NamesSet.mem (shortname f) acc then
      message se.se_loc (Ealready_defined (fullname f))
    else
      NamesSet.add (shortname f) acc
  in
  ignore (List.fold_left add_field NamesSet.empty l)


(** negative value is infinite *)
let rec type_cardinal t =
  let product l =
    List.fold_left (fun c t -> mk_static_int_op "*" [c;(type_cardinal t)]) (mk_static_int 1) l
  in
  match unalias_type t with
  | Tprod t_l -> product t_l
  | _ when t = Initial.tbool -> mk_static_int 2
  | _ when t = Initial.tint -> mk_static_int (-1)
  | _ when t = Initial.tfloat -> mk_static_int (-1)
  | Tid n -> 
    (match find_type n with
    | Tabstract -> mk_static_int (-1)
    | Talias _ -> Misc.internal_error "should be unaliased"
    | Tenum cn_l -> mk_static_int (List.length cn_l)
    | Tstruct f_l ->
        let ft_l = List.map (fun f -> f.f_type) f_l in
        product ft_l
    )
  | Tarray (t, s) -> mk_static_int_op "*" [(type_cardinal t);s]
  | Tbounded s -> s
  | Tinvalid -> mk_static_int (-1)
  | Tfuture _ -> mk_static_int (-1)

let rec type_enumerate t =
  try (match unalias_type t with
    | _ when t = Initial.tbool -> [mk_static_bool true; mk_static_bool false]
    | Tid n ->
      (match find_type n with
      | Tenum cn_l -> List.map (fun c -> mk_static_exp t (Sconstructor c)) cn_l
      | _ -> raise Errors.Error)
    | Tbounded s ->
      let rec loop i c_l = match i with
        | 0 -> c_l
        | _ -> loop (i-1) ((mk_static_int i)::c_l)
      in
      (try loop (Int32.to_int (Static.int_of_static_exp s)) []
       with _ -> raise Errors.Error)
    | _ -> raise Errors.Error)
  with Errors.Error ->
    Misc.internal_error "enumerate of this type is not supported@."


(** returns (unicity, completness) of the enumeration [se_l] of type [t] *)
let check_type_coverage t se_l =
  let unicity = se_list_unicity se_l in
  let completness =
    let u = Int32.to_int (int_of_static_exp (type_cardinal t)) in
    List.length se_l = u
  in
  (unicity, completness)


(** @return the qualified name and list of fields of
    the type with name [n].
    Prints an error message if the type is not a record type.
    [loc] is the location used for error reporting.*)
let struct_info_from_name n =
  try
    find_struct n
  with
      Not_found -> error (Erecord_type_expected (Tid n))

(** @return the qualified name and list of fields of a record type.
    Prints an error message if the type is not a record type.
    [loc] is the location used for error reporting.*)
let struct_info ty = match ty with
  | Tid n -> struct_info_from_name n
  | _ -> error (Erecord_type_expected ty)

(** @return the qualified name and list of fields of the
    record type corresponding to the field named [n].
    Prints an error message if the type is not a record type.
    [loc] is the location used for error reporting.*)
let struct_info_from_field f =
  try
    let t = find_field f in
    t, struct_info_from_name t
  with
      Not_found -> error (Eundefined (fullname f))

(** Unify is symetrical, it checks coherence of types
    and returns the biggest type. *)
let rec _unify t1 t2 =
  match t1, t2 with
    | b1, b2 when b1 = b2 -> t1
    | Tprod t1_list, Tprod t2_list ->
        (try
           Tprod (List.map2 (_unify ) t1_list t2_list)
         with
             _ -> raise Unify)
    | Tarray (ty1, e1), Tarray (ty2, e2) ->
        (try
           add_constraint_eq ~unsafe:true e1 e2
         with Solve_failed _ ->
           raise Unify);
        Tarray(_unify ty1 ty2, e1)
    | Tfuture ((),ty1), Tfuture ((),ty2) ->
        Tfuture ((),_unify ty1 ty2)
    | Tbounded n1, Tbounded n2 ->
        Tbounded (Initial.mk_static_int_op "max" [n1;n2])
        (* type int{<n} into int{<m} with m>n *)
    | (t, Tbounded _ | Tbounded _, t ) when t = Initial.tint ->
        t (* type [int{<n}] into [int] *)
    | _ -> raise Unify

(** In order to do some subtyping, expect is asymmetrical,
    the first argument is the expected type.
    So it checks whether t2 <= t1.*)
and _expect t1 t2 =
  match t1, t2 with
    | b1, b2 when b1 = b2 -> ()
    | Tprod t1_list, Tprod t2_list ->
        (try List.iter2 (_expect) t1_list t2_list
         with _ -> raise Unify)
    | Tarray (ty1, e1), Tarray (ty2, e2) ->
        (try add_constraint_eq ~unsafe:true e1 e2
          (* TODO No subtyping here. Changes at backends could allow it. *)
         with Solve_failed _ -> raise Unify);
        _expect ty1 ty2
    | Tfuture ((),ty1), Tfuture ((),ty2) ->
        _expect ty1 ty2
    | Tbounded n1, Tbounded n2 ->
        (try add_constraint_leq ~unsafe:true n2 n1
        (* subtype [int{<n2}] into [int{<n1}] if n2<n1 *)
         with Solve_failed _ -> raise Unify)
    | t, Tbounded _ when t = Initial.tint ->
        () (* subtype [int{<n}] into [int] *)
    | _ -> raise Unify

(** { 3 Constraints related functions } *)
and (curr_constrnt : constrnt list ref) = ref []

and solve ?(unsafe=false) c_l =
(*  let c_l = List.map (apply_subst_se m) c_l in *)
  try Static.solve c_l
  with Solve_failed c ->
    if unsafe then
      raise (Solve_failed c)
    else
      error (Estatic_constraint c)

(** [cenv] is the constant env which will be used to simplify the given constraints *)
and add_constraint ?(unsafe=false) c =
  let c = expect_se Initial.tbool c in
  curr_constrnt := (solve ~unsafe:unsafe [c])@(!curr_constrnt)

(** Add the constraint [c1=c2] *)
and add_constraint_eq ?(unsafe=false) c1 c2 =
  let c = mk_static_exp tbool (Sop (mk_pervasives "=",[c1;c2])) in
  add_constraint ~unsafe:unsafe c

(** Add the constraint [c1<=c2] *)
and add_constraint_leq ?(unsafe=false) c1 c2 =
  let c = mk_static_exp tbool (Sop (mk_pervasives "<=",[c1;c2])) in
  add_constraint ~unsafe:unsafe c


and get_constraints () =
  let l = !curr_constrnt in
  curr_constrnt := [];
  l

(** Unify is symetrical, it checks coherence of types
    and returns the biggest type. *)
and unify t1 t2 =
  let ut1 = unalias_type t1 in
  let ut2 = unalias_type t2 in
  try _unify ut1 ut2 with Unify -> error (Etype_clash(t1, t2))

and unify_l t_l =
  let ut_l = List.map unalias_type t_l in
  Misc.fold_left_1 unify ut_l

and expect t1 t2 =
  let ut1 = unalias_type t1 in
  let ut2 = unalias_type t2 in
  try _expect ut1 ut2 with Unify -> error (Etype_clash(t1,t2))

(** Unify_pty same as unify but on parameter type. *)
and expect_pty pt1 pt2 = match pt1, pt2 with
  | Ttype t1, Ttype t2 -> expect t1 t2
  | Tsig n1, Tsig n2 -> expect_sig n1 n2
  | _ -> raise Unify

and expect_arg a1 a2 =
  if a1.a_linearity != a2.a_linearity then raise Unify; (* TODO we could accept more... *)
  if a1.a_is_memory != a2.a_is_memory then raise Unify; (* TODO better errors *)
  expect a1.a_type a2.a_type

and expect_sig n1 n2 =
  List.iter2 expect_arg n1.node_inputs n2.node_inputs;
  List.iter2 expect_arg(* contravariance *) n2.node_outputs n1.node_outputs;
  if n1.node_stateful != n2.node_stateful then raise Unify; (* TODO better errors *)
  if n1.node_unsafe != n2.node_unsafe then raise Unify; (* TODO better errors *)
  List.iter2 (fun p1 p2 -> expect_pty p1.p_type p2.p_type) n1.node_params n2.node_params
  (* TODO do something with the constraints ! bug #14589 *)


(** [check_type t] checks that t exists *)
and check_type = function
  | Tarray(ty, e) ->
      let typed_e = expect_se (Tid Initial.pint) e in
      Tarray(check_type ty, typed_e)
  (* No need to check that the type is defined as it is done by the scoping. *)
  | Tid ty_name -> Tid ty_name
  | Tprod l -> Tprod (List.map (check_type ) l)
  | Tinvalid -> Tinvalid
  | Tfuture (a, t) -> Tfuture (a, check_type t)
  | Tbounded n ->
      let typed_n = expect_se (Tid Initial.pint) n in
      (* make sure it is strictly positive *)
      add_constraint_leq (mk_static_int 1) typed_n;
      Tbounded typed_n

(** @return the type of the field with name [f] in the list
    [fields]. [t1] is the corresponding record type and [loc] is
    the location, both used for error reporting. *)
and field_type f fields t1 loc =
  try
    check_type (field_assoc f fields)
  with
      Not_found -> message loc (Eno_such_field (t1, f))

and typing_static_exp se =
  try
  let desc, ty = match se.se_desc with
    | Sint v ->
      if Misc.int32_leq Int32.zero v
      then Sint v, Tbounded (Initial.mk_static_int32 (Int32.succ v))
      else Sint v, Tid Initial.pint
    | Sbool v-> Sbool v, Tid Initial.pbool
    | Sfloat v -> Sfloat v, Tid Initial.pfloat
    | Sstring v -> Sstring v, Tid Initial.pstring
    | Svar ln -> Svar ln, typ_of_qual ln
    | Sfun _ -> Misc.internal_error "cannot type a Sfun"
    | Sconstructor c -> Sconstructor c, find_constrs c
    | Sfield c -> Sfield c, Tid (find_field c)
    | Sop ({name = "="} as op, se_l) ->
        if List.length se_l != 2
        then message se.se_loc (Earity_clash (2, List.length se_l));
        let typed_se_l, _ = unify_se_l se_l in
        Sop (op, typed_se_l), Tid Initial.pbool
    | Sop (op, se_list) ->
        let ty_desc = find_value op in
        let typed_se_list =
          try
            List.map2 expect_se (types_of_arg_list ty_desc.node_inputs) se_list
          with Invalid_argument _ ->
            message se.se_loc (Earity_clash (List.length se_list,
                                             List.length ty_desc.node_inputs))
        in
        Sop (op, typed_se_list),
        prod (types_of_arg_list ty_desc.node_outputs)
    | Sarray_power (se, n_list) ->
        let typed_n_list = List.map (expect_se Initial.tint) n_list in
        let typed_se, ty = typing_static_exp se in
        let tarray =
          List.fold_left (fun ty typed_n -> Tarray(ty, typed_n)) ty typed_n_list
        in
        Sarray_power (typed_se, typed_n_list), tarray
    | Sarray [] ->
        message se.se_loc Eempty_array
    | Sarray (se_l) ->
        let typed_se_l, ty = unify_se_l se_l in
        Sarray typed_se_l, Tarray(ty, mk_static_int (List.length se_l))
    | Stuple se_list ->
        let typed_se_list, ty_list =
          List.split (List.map typing_static_exp se_list)
        in
        Stuple typed_se_list, prod ty_list
    | Srecord f_se_list ->
        (* find the record type using the first field *)
        let q, fields = match f_se_list with
          | [] -> error (Eempty_record)
          | (f,_)::_ -> struct_info_from_field f
        in
        check_static_field_unicity f_se_list;
        if List.length f_se_list <> List.length fields
        then message se.se_loc Esome_fields_are_missing;
        let typing_static_field fields t1 (f,se) =
          try
            let ty = check_type (field_assoc f fields) in
            let typed_se = expect_se ty se in
            f, typed_se
          with Not_found -> message se.se_loc (Eno_such_field (t1, f))
        in
        let f_se_list = List.map (typing_static_field fields (Tid q)) f_se_list in
        Srecord f_se_list, Tid q
     | Sasync se ->
          let typed_se, ty = typing_static_exp se in
          Sasync typed_se, Tfuture ((),ty)
  in
   { se with se_ty = ty; se_desc = desc }, ty

  with
      TypingError kind -> message se.se_loc kind

and expect_se exp_ty se =
  let se, ty = typing_static_exp se in
    try
      expect exp_ty ty; se
    with
      _ -> message se.se_loc (Etype_clash(exp_ty, ty))

and unify_se_l se_l =
  let aux ty se =
    let se, ty2 = typing_static_exp se in
    try se, (unify ty ty2)
    with _ -> message se.se_loc (Etype_clash(ty, ty2))
  in
  let se1, se_l = Misc.assert_1min se_l in
  let se1, ty1 = typing_static_exp se1 in
  let se_l, t = Misc.mapfold aux ty1 se_l in
  se1::se_l, t

let rec typing_ck h ck = match ck with
  | Clocks.Cbase | Clocks.Cvar _ -> ck
  | Clocks.Con (ck', sv, v) ->
      let t = typ_of_name h v in
      let sv = expect_se t sv in
      let ck' = typing_ck h ck' in
      Clocks.Con (ck', sv, v)

let rec typing_ct h ct = match ct with
  | Clocks.Ck ck -> Clocks.Ck (typing_ck h ck)
  | Clocks.Cprod ct_l -> Clocks.Cprod (List.map (typing_ct h) ct_l)

let rec typing h e =
  try
    let typed_desc,ty = match e.e_desc with
      | Econst c ->
          let typed_c, ty = typing_static_exp c in
            Econst typed_c, ty
      | Evar x ->
          Evar x, typ_of_name h x
      | Elast x ->
          Elast x, typ_of_name h x

      | Eapp(op, e_list, r) ->
          let ty, op, typed_e_list = typing_app h op e_list in
          Eapp(op, typed_e_list, r), ty

      | Estruct(l) ->
          (* find the record type using the first field *)
          let q, fields =
            (match l with
               | [] -> message e.e_loc (Eempty_record)
               | (f,_)::_ -> struct_info_from_field f
            ) in

          if List.length l <> List.length fields
          then message e.e_loc Esome_fields_are_missing;
          check_field_unicity l;
          let l = List.map (typing_field h fields (Tid q)) l in
          Estruct l, Tid q

      | Epre (None, e) ->
          let typed_e,ty = typing h e in
          Epre (None, typed_e), ty

      | Epre (Some c, e) ->
          let typed_c, t1 = typing_static_exp c in
          let typed_e, t2 = typing h e in
          let t = unify t1 t2 in
          Epre(Some typed_c, typed_e), t

      | Efby (e1, e2) ->
          let typed_e1, t1 = typing h e1 in
          let typed_e2, t2 = typing h e2 in
          let t = unify t1 t2 in
          Efby (typed_e1, typed_e2), t

      | Eiterator (it, ({ a_op = (Enode f | Efun f);
                          a_params = params } as app),
                   n_list, pe_list, e_list, reset) ->
          let ty_desc = find_value f in
          let op, expected_ty_list, result_ty_list = kind f ty_desc in
          let node_params =
            List.map (fun { p_name = n } -> local_qn_of f n) ty_desc.node_params in
          let m = build_subst node_params params in
          let expected_ty_list =
            List.map (apply_subst_ty m) expected_ty_list in
          let result_ty_list = List.map (apply_subst_ty m) result_ty_list in
          let result_ty_list = asyncify app.a_async result_ty_list in
          let typed_n_list = List.map (expect_se Initial.tint) n_list in
          (*typing of partial application*)
          let p_ty_list, expected_ty_list =
            Misc.split_at (List.length pe_list) expected_ty_list in
          let typed_pe_list = typing_args h p_ty_list pe_list in
          (*typing of other arguments*)
          let ty, typed_e_list = typing_iterator h it typed_n_list
            expected_ty_list result_ty_list e_list in
          let typed_params = typing_node_params ty_desc.node_params params in
          (* add size constraints *)
          let constrs = List.map (apply_subst_se m) ty_desc.node_param_constraints in
          List.iter (add_constraint_leq (mk_static_int 1)) typed_n_list;
          List.iter (add_constraint ) constrs;
          (* return the type *)
          Eiterator(it, { app with a_op = op; a_params = typed_params }
                      , typed_n_list, typed_pe_list, typed_e_list, reset), ty
      | Eiterator (it, ({ a_op = Ebang; } as app), n_list, [], [e], reset) ->
          let _, ty = typing h e in
          let typed_n_list = List.map (expect_se Initial.tint) n_list in
          let result_ty, expect_ty = (match ty with
            | Tarray (Tfuture (a, t), _) -> t, Tfuture(a,t)
            | _ -> message e.e_loc (Eshould_be_async ty))
          in
          let ty, typed_e_l = typing_iterator h it n_list [expect_ty] [result_ty] [e] in
          (* add size constraints *)
          List.iter (add_constraint_leq (mk_static_int 1)) typed_n_list;
          (* return the type *)
          Eiterator(it, app, typed_n_list, [], typed_e_l, reset), ty
      | Eiterator _ -> assert false

      | Ewhen (e, c, x) ->
          let typed_e, t = typing h e in
          let typed_c, tn_expected = typing_static_exp c in
          let tn_actual = typ_of_name h x in
          let _ = expect tn_expected tn_actual in
          Ewhen (typed_e, typed_c, x), t

      | Emerge (_, []) -> Misc.internal_error "Empty merge"
      | Emerge (x, c_e_list) ->
          (* verify the constructors : they should be unique,
             all of the same type and cover all the possibilities *)
          let c_l, e_l = List.split c_e_list in
          let typed_c_l, t_c = unify_se_l c_l in
          let unic, comp = check_type_coverage t_c typed_c_l in
          if not unic then message e.e_loc Emerge_uniq;
          if not comp then message e.e_loc Emerge_missing_constrs;
          (* check x *)
          (try expect t_c (typ_of_name h x)
           with _ -> message e.e_loc (Emerge_bad_sampler (t_c, typ_of_name h x)));
          (* type *)
          let e_l, t = unify_e_l h e_l in
          let c_e_list = List.combine typed_c_l e_l in
          Emerge (x, c_e_list), t

      | Esplit(c, _, e2) ->
          let ty_c = typ_of_name h c in
          let typed_e2, ty = typing h e2 in
          let cl =
            try type_enumerate ty_c
            with _ -> message e.e_loc (Esplit_enum ty_c)
          in
          begin match ty with
            | Tprod _ -> message e.e_loc (Esplit_tuple ty)
            | _ -> ()
          end;
          Esplit(c, cl, typed_e2), Tprod (repeat_list ty (List.length cl))
    in
    let typed_elck = typing_ck h e.e_level_ck in
    let typed_ectannot = Misc.optional (typing_ct h) e.e_ct_annot in
    { e with e_desc = typed_desc; e_ty = ty;
             e_ct_annot = typed_ectannot; e_level_ck = typed_elck }, ty
  with
      TypingError(kind) -> message e.e_loc kind

and typing_field h fields t1 (f, e) =
  try
    let ty = check_type (field_assoc f fields) in
    let typed_e = expect_e h ty e in
      f, typed_e
  with
      Not_found -> message e.e_loc (Eno_such_field (t1, f))

and expect_e h expected_ty e =
  let typed_e, actual_ty = typing h e in
  try
    expect expected_ty actual_ty;
    typed_e
  with TypingError(kind) -> message e.e_loc kind

and unify_e_l h e_l =
  let aux ty e =
    let e, ty2 = typing h e in
    try e,(unify ty ty2)
    with _ -> message e.e_loc (Etype_clash(ty, ty2))
  in
  let e1, e_l = Misc.assert_1min e_l in
  let e1, ty1 = typing h e1 in
  let e_l, t = Misc.mapfold aux ty1 e_l in
  e1::e_l, t

and typing_app h app e_list =
  match app.a_op with
    | Earrow ->
        let _ = assert_2 e_list in
        let typed_e_l, t = unify_e_l h e_list in
        t, app, typed_e_l

    | Eifthenelse ->
        let e1, e2, e3 = assert_3 e_list in
        let typed_e1 = expect_e h (Tid Initial.pbool) e1 in
        let typed_e_l, t = unify_e_l h [e2;e3] in
        t, app, (typed_e1::typed_e_l)

    | Efun {name = "="} ->
        let _ = assert_2 e_list in
        let typed_e_l, _ = unify_e_l h e_list in
        Tid Initial.pbool, app, typed_e_l

    | Efun { qual = Module "Iostream"; name = "printf" } ->
        let e1, format_args = assert_1min e_list in
        let typed_e1 = expect_e h Initial.tstring e1 in
        let typed_format_args = typing_format_args h typed_e1 format_args in
        Tprod [], app, typed_e1::typed_format_args

    | Efun { qual = Module "Iostream"; name = "fprintf" } ->
        let e1, e2, format_args = assert_2min e_list in
        let typed_e1 = expect_e h Initial.tfile e1 in
        let typed_e2 = expect_e h Initial.tstring e2 in
        let typed_format_args = typing_format_args h typed_e1 format_args in
        Tprod [], app, typed_e1::typed_e2::typed_format_args

    | (Efun f | Enode f) ->
        let ty_desc = find_value f in
        let op, expected_ty_list, result_ty_list = kind f ty_desc in
        let node_params = List.map (fun { p_name = n } -> local_qn_of f n) ty_desc.node_params in
        let m = build_subst node_params app.a_params in
        let expected_ty_list = List.map (apply_subst_ty m) expected_ty_list in
        let typed_e_list = typing_args h expected_ty_list e_list in
        let result_ty_list = List.map (apply_subst_ty m) result_ty_list in
        let result_ty_list = asyncify app.a_async result_ty_list in
        (* Type static parameters and generate constraints *)
        let typed_params = typing_node_params ty_desc.node_params app.a_params in
        let constrs = List.map (apply_subst_se m) ty_desc.node_param_constraints in
        List.iter (add_constraint ) constrs;
        (prod result_ty_list,
          { app with a_op = op; a_params = typed_params },
          typed_e_list)

    | Etuple ->
        let typed_e_list,ty_list =
          List.split (List.map (typing h) e_list) in
         prod ty_list, app, typed_e_list

    | Earray ->
        let typed_e_list, t = unify_e_l h e_list in
        let n = mk_static_int (List.length e_list) in
        Tarray(t, n), app, typed_e_list

    | Efield ->
        let e = assert_1 e_list in
        let f = assert_1 app.a_params in
        let fn =
          (match f.se_desc with
             | Sfield fn -> fn
             | _ -> assert false) in
        let typed_e, t1 = typing h e in
        let fields = struct_info t1 in (* not ready for inference *)
        let t2 = field_type fn fields t1 e.e_loc in
          t2, app, [typed_e]

    | Efield_update ->
        let e1, e2 = assert_2 e_list in
        let f = assert_1 app.a_params in
        let typed_e1, t1 = typing h e1 in
        let fields = struct_info t1 in
        let fn =
          (match f.se_desc with
             | Sfield fn -> fn
             | _ -> assert false) in
        let t2 = field_type fn fields t1 e1.e_loc in
        let typed_e2 = expect_e h t2 e2 in (* not ready for inference *)
        t1, app, [typed_e1; typed_e2]

    | Earray_fill ->
        let _, _ = assert_1min app.a_params in
        let e1 = assert_1 e_list in
        let typed_n_list = List.map (expect_se Initial.tint) app.a_params in
        let typed_e1, t1 = typing h e1 in
        List.iter (fun typed_n -> add_constraint_leq (mk_static_int 1) typed_n) typed_n_list;
        (List.fold_left (fun t1 typed_n -> Tarray (t1, typed_n)) t1 typed_n_list),
          { app with a_params = typed_n_list }, [typed_e1]

    | Eselect ->
        let e1 = assert_1 e_list in
        let typed_e1, t1 = typing h e1 in
        let typed_idx_list, ty =
          typing_array_subscript h app.a_params t1 in
          ty, { app with a_params = typed_idx_list }, [typed_e1]

    | Eselect_dyn ->
        let e1, defe, idx_list = assert_2min e_list in
        let typed_e1, t1 = typing h e1 in
        let typed_defe = expect_e h (element_type t1) defe in
        let ty, typed_idx_list =
          typing_array_subscript_dyn h idx_list t1 in
        ty, app, typed_e1::typed_defe::typed_idx_list

    | Eselect_trunc ->
        let e1, idx_list = assert_1min e_list in
        let typed_e1, t1 = typing h e1 in
        let ty, typed_idx_list =
          typing_array_subscript_dyn h idx_list t1 in
        ty, app, typed_e1::typed_idx_list

    | Eupdate ->
        let e1, e2, idx_list = assert_2min e_list in
        let typed_e1, t1 = typing h e1 in
        let ty, typed_idx_list =
          typing_array_subscript_dyn h idx_list t1 in
        let typed_e2 = expect_e h ty e2 in
          t1, app, typed_e1::typed_e2::typed_idx_list

    | Eselect_slice ->
        let e = assert_1 e_list in
        let idx1, idx2 = assert_2 app.a_params in
        let typed_idx1 = expect_se (Tid Initial.pint) idx1 in
        let typed_idx2 = expect_se (Tid Initial.pint) idx2 in
        let typed_e, t1 = typing h e in
        (*Create the expression to compute the size of the array *)
        let e1 = mk_static_int_op "-" [typed_idx2; typed_idx1] in
        let e2 = mk_static_int_op "+" [e1; mk_static_int 1] in
        add_constraint_leq (mk_static_int 1) e2;
        Tarray (element_type t1, e2),
        { app with a_params = [typed_idx1; typed_idx2] }, [typed_e]

    | Econcat ->
        let e1, e2 = assert_2 e_list in
        let typed_e1, t1 = typing h e1 in
        let typed_e2, t2 = typing h e2 in
        let t =
          (try unify (element_type t1) (element_type t2)
           with TypingError(kind) -> message e1.e_loc kind)
        in
        let n = mk_static_int_op "+" [array_size t1; array_size t2] in
        Tarray (t, n), app, [typed_e1; typed_e2]
    | Ebang ->
        let e = assert_1 e_list in
        let typed_e, t = typing h e in
        (match t with
          | Tfuture (_, t) -> t, app, [typed_e]
          | _ -> message e.e_loc (Eshould_be_async t))

    | Ereinit ->
        let e1, e2 = assert_2 e_list in
        let typed_e1, ty = typing h e1 in
        let typed_e2 = expect_e h ty e2 in
        ty, app, [typed_e1; typed_e2]

and typing_iterator h
    it n_list args_ty_list result_ty_list e_list =
  let rec array_of_idx_list l ty = match l with
    | [] -> ty
    | n::l -> array_of_idx_list l (Tarray(ty, n))
  in
  let mk_array_type ty_list = List.map (array_of_idx_list n_list) ty_list in
  let n_size = List.length n_list in
  let mk_array_type_butlast ty_list =
    map_butlast (array_of_idx_list n_list) ty_list in
  match it with
  | Imap ->
      let args_ty_list = mk_array_type args_ty_list in
      let result_ty_list = mk_array_type result_ty_list in
      let typed_e_list = typing_args h
        args_ty_list e_list in
      prod result_ty_list, typed_e_list

  | Imapi ->
      let args_ty_list, idx_ty_list = split_nlast n_size args_ty_list in
      let args_ty_list = mk_array_type args_ty_list in
      let result_ty_list = mk_array_type result_ty_list in
      (* Last but one arg of the function should accept bounded integers *)
      List.iter2
        (fun idx_ty n ->
          (try expect idx_ty (Tbounded n)
           with TypingError _ -> raise(TypingError(Emapi_bad_args idx_ty))))
        idx_ty_list n_list;
      let typed_e_list = typing_args h args_ty_list e_list in
      prod result_ty_list, typed_e_list

  | Ifold ->
      let args_ty_list = mk_array_type_butlast args_ty_list in
      let typed_e_list = typing_args h args_ty_list e_list in
      (*check accumulator type : output subtype of input*)
      if List.length result_ty_list > 1 then error Etoo_many_outputs;
      (try expect (last_element args_ty_list) (List.hd result_ty_list)
       with TypingError(kind) -> message (List.hd e_list).e_loc kind );
      (List.hd result_ty_list), typed_e_list

  | Ifoldi ->
      let args_ty_list, acc_ty = split_last args_ty_list in
      let args_ty_list, idx_ty_list = split_nlast n_size args_ty_list in
        (* Last but one arg of the function should be integer *)
      List.iter2
        (fun idx_ty n ->
          ( try expect idx_ty (Tbounded n)
            with TypingError _ -> raise (TypingError (Emapi_bad_args idx_ty))))
        idx_ty_list n_list;
      let args_ty_list = mk_array_type_butlast (args_ty_list@[acc_ty]) in
      let typed_e_list = typing_args h args_ty_list e_list in
      (*check accumulator type : output subtype of input*)
      if List.length result_ty_list > 1 then error Etoo_many_outputs;
      ( try expect (last_element args_ty_list) (List.hd result_ty_list)
        with TypingError(kind) -> message (List.hd e_list).e_loc kind );
      (List.hd result_ty_list), typed_e_list

    | Imapfold ->
      let args_ty_list = mk_array_type_butlast args_ty_list in
      let result_ty_list = mk_array_type_butlast result_ty_list in
      let typed_e_list = typing_args h args_ty_list e_list in
      (*check accumulator type : output subtype of input*)
      ( try expect (last_element args_ty_list) (last_element result_ty_list)
        with TypingError(kind) -> message (List.hd e_list).e_loc kind );
      prod result_ty_list, typed_e_list

and typing_array_subscript h idx_list ty  =
  match unalias_type ty, idx_list with
    | ty, [] -> [], ty
    | Tarray(ty, exp), idx::idx_list ->
        ignore (expect_se (Tid Initial.pint) exp);
        let typed_idx = expect_se (Tid Initial.pint) idx in
        add_constraint_leq (mk_static_int 0) idx;
        let bound = mk_static_int_op "-" [exp; mk_static_int 1] in
        add_constraint_leq idx bound;
        let typed_idx_list, ty = typing_array_subscript h idx_list ty in
        typed_idx::typed_idx_list, ty
    | _, _ -> raise (TypingError (Esubscripted_value_not_an_array ty))

(* This function checks that the array dimensions matches
   the subscript. It returns the base type wrt the nb of indices. *)
and typing_array_subscript_dyn h idx_list ty =
  match unalias_type ty, idx_list with
    | ty, [] -> ty, []
    | Tarray(ty, _), idx::idx_list ->
        let typed_idx = expect_e h (Tid Initial.pint) idx in
        let ty, typed_idx_list =
          typing_array_subscript_dyn h idx_list ty in
        ty, typed_idx::typed_idx_list
    | _, _ -> raise (TypingError (Esubscripted_value_not_an_array ty))

and typing_args h expected_ty_list e_list =
  let typed_e_list, args_ty_list =
    List.split (List.map (typing h) e_list)
  in
  let args_ty_list = flatten_ty_list args_ty_list in
  (match args_ty_list, expected_ty_list with
    | [], [] -> ()
    | _, _ ->
      (try
        expect (prod expected_ty_list)(prod args_ty_list) 
      with _ ->
        raise (TypingError (Eargs_clash (prod expected_ty_list, prod args_ty_list)))
      )
  );
  typed_e_list

and typing_node_params params_sig params =
  let aux p_sig p = match p_sig.p_type, p.se_desc with
    | Ttype _, Sfun _ -> Misc.internal_error "better typing error" (* TODO add real typing error *)
    | Ttype t, _ -> expect_se t p
    | Tsig n, Sfun (f, se_l) ->
        let n' = find_value f in
        let typed_se_l = typing_node_params n'.node_params se_l in
        expect_sig n {n' with node_params = []}; (* for now prevent partial application *)
        {p with se_desc = Sfun (f, typed_se_l)}
    | Tsig _, _ -> Misc.internal_error "better typing error" (* TODO add real typing error *)
  in
  List.map2 aux params_sig params

and typing_format_args h e args =
  let s = match e.e_desc with
    | Econst { se_desc = Sstring s } -> s
    | _ -> raise (TypingError Eformat_string_not_constant)
  in
  try
    let expected_ty_list = Printf_parser.types_of_format_string s in
    typing_args h expected_ty_list args
  with
    | Printf_parser.Bad_format -> raise (TypingError Ebad_format)

let rec typing_pat h acc = function
  | Evarpat(x) ->
      let vd = vd_of_name h x in
      let acc = add_distinct_env x vd acc in
      acc, vd.v_type
  | Etuplepat(pat_list) ->
      let acc, ty_list =
        List.fold_right
          (fun pat (acc, ty_list) ->
             let acc, ty = typing_pat h acc pat in acc, ty :: ty_list)
          pat_list (acc, []) in
      acc, Tprod(ty_list)

let rec typing_eq h acc eq =
  let typed_desc,acc = match eq.eq_desc with
    | Eautomaton(state_handlers) ->
        let typed_sh,acc =
          typing_automaton_handlers h acc state_handlers in
        Eautomaton(typed_sh),
        acc
    | Eswitch(e, switch_handlers) ->
        let typed_e,ty = typing h e in
        let typed_sh,acc =
          typing_switch_handlers h acc ty switch_handlers in
        Eswitch(typed_e,typed_sh),
        acc
    | Epresent(present_handlers, b) ->
        let typed_b, def_names, _ = typing_block h b in
        let typed_ph, acc =
          typing_present_handlers h
            acc def_names present_handlers in
        Epresent(typed_ph,typed_b),
        acc
    | Ereset(b, e) ->
        let typed_e = expect_e h (Tid Initial.pbool) e in
        let typed_b, def_names, _ = typing_block h b in
        Ereset(typed_b, typed_e),
        Env.union def_names acc
    | Eblock b ->
        let typed_b, def_names, _ = typing_block h b in
        Eblock typed_b,
        Env.union def_names acc
    | Eeq(pat, e) ->
        let acc, ty_pat = typing_pat h acc pat in
        let typed_e = expect_e h ty_pat e in
        Eeq(pat, typed_e),
        acc in
  { eq with eq_desc = typed_desc }, acc

and typing_eq_list h acc eq_list =
  mapfold (typing_eq h) acc eq_list

and typing_automaton_handlers h acc state_handlers =
  (* checks unicity of states *)
  let addname acc { s_state = n } =
    add_distinct_S n acc in
  let states =  List.fold_left addname NamesSet.empty state_handlers in

  let escape h ({ e_cond = e; e_next_state = n } as esc) =
    if not (NamesSet.mem n states) then error (Eundefined(n));
    let typed_e = expect_e h (Tid Initial.pbool) e in
    { esc with e_cond = typed_e } in

  let handler ({ s_block = b; s_until = e_list1;
                 s_unless = e_list2 } as s) =
    let typed_b, defined_names, h0 = typing_block h b in
    let typed_e_list1 = List.map (escape h0) e_list1 in
    let typed_e_list2 = List.map (escape h) e_list2 in
    { s with
        s_block = typed_b;
        s_until = typed_e_list1;
        s_unless = typed_e_list2 },
    defined_names in

  let typed_handlers,defined_names_list =
    List.split (List.map handler state_handlers) in
  let total, partial = merge defined_names_list in
  all_last h partial;
  typed_handlers,
      (add total (add partial acc))

and typing_switch_handlers h acc ty switch_handlers =
  let handler sh =
    let typed_b, defined_names, _ = typing_block h sh.w_block in
    let typed_c = expect_se ty sh.w_name in
    { w_name = typed_c; w_block = typed_b }, defined_names
  in
  let typed_switch_handlers, defined_names_list =
    List.split (List.map handler switch_handlers)
  in
  (* checks states coverage *)
  let s_l = List.map (fun w -> w.w_name) typed_switch_handlers in
  let unic, comp = check_type_coverage ty s_l in
  if not unic then error Enon_exaustive;
  if not comp then error Epartial_switch;
  (* check partial def are lasts *)
  let total, partial = merge defined_names_list in
  all_last h partial;
  (typed_switch_handlers, add total (add partial acc))

and typing_present_handlers h acc def_names
    present_handlers =
  let handler ({ p_cond = e; p_block = b }) =
    let typed_e = expect_e h (Tid Initial.pbool) e in
    let typed_b, defined_names, _ = typing_block h b in
    { p_cond = typed_e; p_block = typed_b },
    defined_names
  in

  let typed_present_handlers, defined_names_list =
    List.split (List.map handler present_handlers) in
  let total, partial = merge (def_names :: defined_names_list) in
  all_last h partial;
  (typed_present_handlers,
   (add total (add partial acc)))

and typing_block h
    ({ b_local = l; b_equs = eq_list; b_loc = loc } as b) =
  try
    let typed_l, (local_names, h0) = build h l in
    let typed_eq_list, defined_names =
      typing_eq_list h0 Env.empty eq_list in
    let defnames = diff_env defined_names local_names in
    { b with
        b_defnames = defnames;
        b_local = typed_l;
        b_equs = typed_eq_list },
    defnames, h0
  with
    | TypingError(kind) -> message loc kind

(** Builds environments from a var_dec list.
    [h] is the environment to start from.
    @return the typed list of var_dec, an environment mapping
    names to their types (aka defined names) and the environment
    mapping names to types and last that will be used for typing (aka h).*)
and build h decs =
  let var_dec (acc_defined, h) vd =
    try
      let ty = check_type vd.v_type in

      let last_dec = match vd.v_last with
        | Last (Some se) -> Last (Some (expect_se ty se))
        | Var | Last None -> vd.v_last in

      if Env.mem vd.v_ident h then
        error (Ealready_defined(name vd.v_ident));

      let vd = { vd with v_last = last_dec; v_type = ty } in
      let acc_defined = Env.add vd.v_ident vd acc_defined in
      let h = Env.add vd.v_ident { vd = vd; last = last vd.v_last } h in
      vd, (acc_defined, h)
    with
        TypingError(kind) -> message vd.v_loc kind
  in
  let decs, (local_names, h) = mapfold var_dec (Env.empty, h) decs in
  let check_vd h vd =
    let v_last = match vd.v_last with
      | Var -> Var
      | Last s -> Last (Misc.optional (expect_se vd.v_type) s)
    in
    let v_clock = typing_ck h vd.v_clock in
    { vd with v_last; v_clock }
  in
  let decs = List.map (check_vd h) decs in
  decs, (local_names, h)

let typing_contract h contract =
  match contract with
    | None -> None,h
    | Some ({ c_block = b;
              c_assume = e_a;
              c_enforce = e_g;
              c_controllables = c }) ->
        let typed_b, defined_names, h' = typing_block h b in
          (* check that the equations do not define other unexpected names *)
          included_env defined_names Env.empty;

        (* assumption *)
        let typed_e_a = expect_e h' (Tid Initial.pbool) e_a in
        (* property *)
        let typed_e_g = expect_e h' (Tid Initial.pbool) e_g in

        let typed_c, (_, h) = build h c in

        Some { c_block = typed_b;
               c_assume = typed_e_a;
               c_enforce = typed_e_g;
               c_controllables = typed_c }, h


let rec check_params_type ps =
  let check_param p =
    let name = local_qn p.p_name in
    let ty = match p.p_type with
      | Ttype t ->
          let t = check_type t in
          let cd = find_const name in
          replace_const name { cd with Signature.c_type = t };
          Ttype t
      | Tsig n -> Tsig (typing_signature n name)
    in
    let p = { p with p_type = ty } in
    p
  in
  List.map check_param ps

and typing_arg a =
  { a with a_type = check_type a.a_type }

and typing_signature s n =
  Idents.push_node n;
  let params = check_params_type s.node_params in
  let inputs = List.map (typing_arg ) s.node_inputs in
  let outputs = List.map (typing_arg ) s.node_outputs in
  let s = { s with node_params = params;
                   node_inputs = inputs;
                   node_outputs = outputs }
  in
  replace_value n s;
  let _ = Idents.pop_node () in
  s


let node ({ n_name = f; n_input = i_list; n_output = o_list;
            n_contract = contract;
            n_block = b; n_loc = loc;
            n_params = node_params; } as n) =
  Idents.push_node f;
  try
    let typed_params = check_params_type node_params in
    let typed_i_list, (_, h) = build Env.empty i_list in
    let typed_o_list, (output_names, h) = build h o_list in

    (* typing contract *)
    let typed_contract, h = typing_contract h contract in

    let typed_b, defined_names, _ = typing_block h b in
    (* check that the defined names match exactly the outputs and locals *)
    included_env defined_names output_names;
    included_env output_names defined_names;

    (* update the node signature to add static params constraints *)
    let s = find_value f in
    let cl = List.map (expect_se Initial.tbool) s.node_param_constraints in
    let cl = cl @ get_constraints () in
    let cl = solve cl in
    (*TODO on solve les contraintes que l'on vient d'ajouter.*)
    (*Pour l'instant, sans apliquer de substitution avec apply_subst, solve n'aura rien a faire.*)
    let node_inputs = List.map (typing_arg ) s.node_inputs in
    let node_outputs = List.map (typing_arg ) s.node_outputs in
    replace_value f { s with node_param_constraints = cl;
                             node_inputs = node_inputs; node_outputs = node_outputs };
    let _ = Idents.pop_node () in
    { n with
        n_input = typed_i_list;
        n_output = typed_o_list;
        n_params = typed_params;
        n_contract = typed_contract;
        n_block = typed_b }
  with
    | TypingError(error) -> message loc error

let typing_const_dec cd =
  let ty = check_type cd.c_type in
  let se = expect_se ty cd.c_value in
  let const_def = { Signature.c_type = ty; Signature.c_value = se } in
  Modules.replace_const cd.c_name const_def;
  { cd with c_value = se; c_type = ty }

let typing_typedec td =
  let tydesc = match td.t_desc with
    | Type_abs -> Type_abs
    | Type_enum(tag_list) -> Type_enum tag_list
    | Type_alias t ->
        let t = check_type t in
          replace_type td.t_name (Talias t);
          Type_alias t
    | Type_struct(field_ty_list) ->
        let typing_field { f_name = f; f_type = ty } =
          { f_name = f; f_type = check_type ty }
        in
        let field_ty_list = List.map typing_field field_ty_list in
          replace_type td.t_name (Tstruct field_ty_list);
          Type_struct field_ty_list
  in
    { td with t_desc = tydesc }

let program p =
  let program_desc pd = match pd with
    | Pnode n -> Pnode (node n)
    | Pconst c -> Pconst (typing_const_dec c)
    | Ptype t -> Ptype (typing_typedec t)
  in
  { p with p_desc = List.map program_desc p.p_desc }

let interface i =
  let interface_desc id = match id with
      | Iconstdef c -> Iconstdef (typing_const_dec c)
      | Itypedef t -> Itypedef (typing_typedec t)
      | Isignature i ->
          let s = typing_signature i.sig_sig i.sig_name in
          Isignature { i with sig_sig = s }
  in
  { i with i_desc = List.map interface_desc i.i_desc }
