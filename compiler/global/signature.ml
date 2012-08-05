(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* global data in the symbol tables *)

open Misc
open Names
open Location
open Linearity

(** Warning: Whenever these types are modified,
    interface_format_version should be incremented. *)
let interface_format_version = "5"

(***************************************************************************)
(* Types *)

type future_t = unit
and async_t = (static_exp list) option

and ck =
  | Cbase
  | Con of ck * static_exp * name

and static_exp = { se_desc: static_exp_desc; se_ty: ty; se_loc: location }

and static_exp_desc =
  | Sfun of fun_name * (static_exp list) (** f<<3, n>> *)
  | Svar of constant_name
  | Sint of Int32.t
  | Sfloat of float
  | Sbool of bool
  | Sstring of string (** without enclosing quotes *)
  | Sconstructor of constructor_name
  | Sfield of field_name (** used as argument of Minils.Efield_update, doesn't exists in Obc. *)
  | Stuple of static_exp list
  | Sarray_power of static_exp * (static_exp list) (** power : 0^n^m : [[0,0,..],[0,0,..],..] *)
  | Sarray of static_exp list (** [ e1, e2, e3 ] *)
  | Srecord of (field_name * static_exp) list (** { f1 = e1; f2 = e2; ... } *)
  | Sop of fun_name * static_exp list (** defined ops for now in pervasives *)
  | Sasync of static_exp

and ty =
  | Tprod of ty list (** Product type used for tuples *)
  | Tid of type_name (** Usable type_name are defined types or pervasives {bool,int,float}
                         (see [Initial]), with the type static parameters*)
  | Tarray of ty * static_exp (** [base_type] * [size], ty should not be prod *)
  | Tbounded of static_exp (** [size], beware of cycles in static exp like
                               x = (4 : (Tbounded x)),
                               because of this the typing should do x = (4 : Tbounded (4 : int)) *)
  | Tinvalid
  | Tfuture of future_t * ty

and param = { p_name : name; p_type : param_ty }

and param_ty =
  | Ttype of ty
  | Tsig of node

(** Node argument : inputs and outputs *)
and arg = {
  a_name  : name option;
  a_type  : ty;
  a_clock : ck; (** [a_clock] set to [Cbase] means at the node activation clock *)
  a_linearity : linearity;
  (** [a_is_memory] is only correct after entering Minils (corrected with the Is_memory pass *)
  a_is_memory : bool;
}

(** Constraints on size expressions *)
and constrnt = static_exp

(** Node signature *)
and node = {
  node_inputs             : arg list;
  node_outputs            : arg list;
  node_stateful           : bool;
  node_unsafe             : bool;
  node_params             : param list;
  node_param_constraints  : constrnt list;
  node_external           : bool;
  node_loc                : location}

type field = { f_name : field_name; f_type : ty }
type structure = field list

type type_def =
  | Tabstract
  | Talias of ty
  | Tenum of constructor_name list
  | Tstruct of structure

type const_def = { c_type : ty; c_value : static_exp }


(** { 3 Helper functions } *)

let invalid_type = Tinvalid (** Invalid type given to untyped expression etc. *)

let prod = function
  | [ty]    -> ty
  | ty_list -> Tprod ty_list

let unprod = function
  | Tprod l -> l
  | t -> [t]

let asyncify async ty_list = match async with
  | None -> ty_list
  | Some _ -> List.map (fun ty -> Tfuture ((),ty)) ty_list

let mk_static_exp ?(loc = no_location) ty desc = (*note ~ty: replace as first arg*)
  { se_desc = desc; se_ty = ty; se_loc = loc }

let dummy_static_exp ty = mk_static_exp ty (Svar Names.dummy_qualname)

let names_of_arg_list l = List.map (fun ad -> ad.a_name) l

let types_of_arg_list l = List.map (fun ad -> ad.a_type) l

let types_of_param_list l = List.map (fun p -> p.p_type) l

let linearities_of_arg_list l = List.map (fun ad -> ad.a_linearity) l

let mk_arg ~is_memory ty linearity ck name =
  { a_type = ty; a_linearity = linearity; a_name = name; a_clock = ck;
    a_is_memory = is_memory }

let mk_param ty name = { p_name = name; p_type = ty }

let mk_field ty name = { f_name = name; f_type = ty }

let mk_const_def ty value =
  { c_type = ty; c_value = value }

let dummy_const ty = mk_const_def ty (dummy_static_exp ty)
let mk_node constraints loc ~extern ins outs stateful unsafe params =
  { node_inputs = ins;
    node_outputs  = outs;
    node_stateful = stateful;
    node_unsafe = unsafe;
    node_params = params;
    node_param_constraints = constraints;
    node_external = extern;
    node_loc = loc}

let dummy_node =
  mk_node [] ~extern:true no_location [] [] false false []

let rec field_assoc f = function
  | [] -> raise Not_found
  | { f_name = n; f_type = ty }::l ->
      if f = n then ty
      else field_assoc f l

(** permits to know whether a static_exp is a local parameter of a node. *)
let is_local_se se = match se.se_desc with
  | Svar {qual = LocalModule _} -> true
  | _ -> false


(** Comparison functions *)
let async_t_compare a1 a2 = Pervasives.compare a1 a2

let rec static_exp_compare se1 se2 =
  let cr = type_compare se1.se_ty se2.se_ty in
  if cr <> 0 then cr else static_exp_desc_compare se1.se_desc se2.se_desc


and static_exp_desc_compare sed1 sed2 =
  let c = Pervasives.compare in
  match sed1, sed2 with
    | Svar cn1, Svar cn2 -> c cn1 cn2
    | Sint i1, Sint i2 -> c i1 i2
    | Sfloat f1, Sfloat f2 -> c f1 f2
    | Sbool b1, Sbool b2 -> c b1 b2
    | Sstring s1, Sstring s2 -> c s1 s2
    | Sconstructor c1, Sconstructor c2 -> c c1 c2
    | Sfield f1, Sfield f2 -> c f1 f2
    | Stuple sel1, Stuple sel2 ->
        list_compare static_exp_compare sel1 sel2
    | Sarray_power (se11, sel1), Sarray_power (se12, sel2) ->
        let cr = static_exp_compare se11 se12 in
        if cr <> 0 then cr else list_compare static_exp_compare sel1 sel2
    | Sarray sel1, Sarray sel2 ->
        list_compare static_exp_compare sel1 sel2
    | Srecord fnsel1, Srecord fnsel2 ->
        let compare_field (fn1, se1) (fn2, se2) =
          let cr = c fn1 fn2 in
          if cr <> 0 then cr else static_exp_compare se1 se2 in
        list_compare compare_field fnsel1 fnsel2
    | Sfun (fn1, sel1), Sfun (fn2, sel2)
    | Sop (fn1, sel1), Sop (fn2, sel2) ->
        let cr = c fn1 fn2 in
        if cr <> 0 then cr else list_compare static_exp_compare sel1 sel2
    | Sasync se1, Sasync se2 ->
        static_exp_compare se1 se2

    | Svar _, _ -> 1

    | Sint _, Svar _ -> -1
    | Sint _, _ -> 1

    | Sfloat _, (Svar _ | Sint _) -> -1
    | Sfloat _, _ -> 1

    | Sbool _, (Svar _ | Sint _ | Sfloat _) -> -1
    | Sbool _, _ -> 1

    | Sstring _, (Svar _ | Sint _ | Sfloat _ | Sbool _) -> -1
    | Sstring _, _ -> 1

    | Sconstructor _, (Svar _ | Sint _ | Sfloat _ | Sbool _ | Sstring _) -> -1
    | Sconstructor _, _ -> 1

    | Sfield _, (Svar _ | Sint _ | Sfloat _ | Sbool _ | Sstring _ | Sconstructor _) -> -1
    | Sfield _, _ -> 1

    | Sasync _, (Svar _ | Sint _ | Sfloat _ | Sbool _ | Sstring _ | Sconstructor _ | Sfield _) -> -1
    | Sasync _, _ -> 1

    | Stuple _, (Srecord _ | Sop _ | Sarray _ | Sarray_power _ | Sfun _) -> 1
    | Stuple _, _ -> -1

    | Sarray_power _, (Srecord _ | Sop _ | Sarray _ | Sfun _) -> -1
    | Sarray_power _, _ -> 1

    | Sarray _, (Srecord _ | Sop _ | Sfun _) -> 1
    | Sarray _, _ -> -1

    | Srecord _, (Sop _ | Sfun _) -> 1
    | Srecord _, _ -> -1

    | Sop _, Sfun _ -> 1
    | Sop _, _ -> -1

    | Sfun _, _ -> -1

and type_compare ty1 ty2 = match ty1, ty2 with
  | Tprod tyl1, Tprod tyl2 -> list_compare type_compare tyl1 tyl2
  | Tid tyn1, Tid tyn2 -> Pervasives.compare tyn1 tyn2
  | Tarray (ty1, se1), Tarray (ty2, se2) ->
      let cr = type_compare ty1 ty2 in
      if cr <> 0 then cr else static_exp_compare se1 se2
  | Tinvalid, Tinvalid -> 0
  | Tfuture (a1, t1), Tfuture (a2, t2) ->
      let cr = type_compare t1 t2 in
      if cr <> 0 then cr else async_t_compare a1 a2
  | Tbounded n1, Tbounded n2 -> static_exp_compare n1 n2

  | Tprod _, _ -> 1

  | Tid _, Tprod _ -> -1
  | Tid _, _ -> 1

  | Tarray _, (Tprod _ | Tid _) -> -1
  | Tarray _, _ -> 1

  | Tinvalid, (Tfuture _ | Tbounded _ ) -> 1
  | Tinvalid, _ -> -1

  | Tfuture _, Tbounded _ -> 1
  | Tfuture _, _ -> -1

  | Tbounded _, _ -> -1

