open Names
open Idents
open Signature
open Types
open Clocks
open Modules
open Format
open Pp_tools


let rec _aux_print_modul ?(full=false) ff m = match m with
  | Pervasives -> ()
  | LocalModule -> ()
  | _ when m = g_env.current_mod && not full -> ()
  | Module m -> fprintf ff "%a." print_name m
  | QualModule { qual = m; name = n } -> fprintf ff "%a%a." (_aux_print_modul ~full:full) m print_name n

(** Prints a [modul] with a [.] at the end when not empty *)
let _print_modul ?(full=false) ff m = match m with
  | Pervasives -> ()
  | LocalModule -> ()
  | _ when m = g_env.current_mod && not full -> ()
  | Module m -> fprintf ff "%a" print_name m
  | QualModule { qual = m; name = n } -> fprintf ff "%a%a" (_aux_print_modul ~full:full) m print_name n
let print_full_modul ff m = _print_modul ~full:true ff m
let print_modul ff m = _print_modul ~full:false ff m

let _print_qualname ?(full=false) ff { qual = q; name = n} = match q with
  | Pervasives -> print_name ff n
  | LocalModule -> print_name ff n
  | _ when q = g_env.current_mod && not full -> print_name ff n
  | _ -> fprintf ff "%a%a" (_aux_print_modul ~full:full) q print_name n
let print_qualname ff qn = _print_qualname ~full:false ff qn
let print_full_qualname ff qn = _print_qualname ~full:true ff qn

let print_shortname ff {name = n} = print_name ff n

let print_async ff async = match async with
  | None -> ()
  | Some () -> fprintf ff "async "

let rec print_static_exp ff se = match se.se_desc with
  | Sint i -> fprintf ff "%d" i
  | Sbool b -> fprintf ff "%b" b
  | Sfloat f -> fprintf ff "%f" f
  | Sconstructor ln -> print_qualname ff ln
  | Sfield ln -> print_qualname ff ln
  | Svar id -> fprintf ff "%a" print_qualname id
  | Sop (op, se_list) ->
      if is_infix (shortname op)
      then
        let e1,e2 = Misc.assert_2 se_list in
        fprintf ff "(@[%a@ %a %a@])" print_static_exp e1 print_qualname op print_static_exp e2
      else
        fprintf ff "@[<2>%a@,%a@]"
          print_qualname op  print_static_exp_tuple se_list
  | Sarray_power (se, n) ->
      fprintf ff "%a^%a" print_static_exp se  print_static_exp n
  | Sarray se_list ->
      fprintf ff "@[<2>%a@]" (print_list_r print_static_exp "["";""]") se_list
  | Stuple se_list -> print_static_exp_tuple ff se_list
  | Srecord f_se_list ->
      print_record (print_couple print_qualname
                      print_static_exp """ = """) ff f_se_list
  | Sasync se -> fprintf ff "@[<2>async %a@]" print_static_exp se

and print_static_exp_tuple ff l =
  fprintf ff "@[<2>%a@]" (print_list_r print_static_exp "("","")") l

and print_type ff = function
  | Tinvalid -> fprintf ff "INVALID TYPE"
  | Tprod ty_list ->
      fprintf ff "@[<hov2>%a@]" (print_list_r print_type "(" " *" ")") ty_list
  | Tid id -> print_qualname ff id
  | Tarray (ty, n) ->
      fprintf ff "@[<hov2>%a^%a@]" print_type ty print_static_exp n
  | Tasync (a, t) -> fprintf ff "%a%a" print_async (Some a) print_type t

let print_field ff field =
  fprintf ff "@[%a: %a@]" print_qualname field.f_name  print_type field.f_type

let print_struct ff field_list = print_record print_field ff field_list

let print_size_constraint ff = function
  | Cequal (e1, e2) ->
      fprintf ff "@[%a = %a@]" print_static_exp e1 print_static_exp e2
  | Clequal (e1, e2) ->
      fprintf ff "@[%a <= %a@]" print_static_exp e1 print_static_exp e2
  | Cfalse -> fprintf ff "Cfalse"

let print_param ff p =
  fprintf ff "%a:%a"  Names.print_name p.p_name  print_type p.p_type

let print_interface_type ff name tdesc =
  match tdesc with
    | Tabstract -> fprintf ff "@[type %s@]" name
    | Tenum tag_name_list ->
        fprintf ff "@[<2>type %s =@ %a@]"
          name
          (print_list_r print_qualname "" " |" "") tag_name_list;
    | Tstruct f_ty_list ->
        fprintf ff "@[<2>type %s =@ %a@]" name print_struct f_ty_list
    | Talias t -> fprintf ff "@[<2>type %s = %a@]" name print_type t

let print_interface_const ff name c =
  fprintf ff "@[<2>const %a : %a = %a@]@."
      print_name name
      print_type c.Signature.c_type
      print_static_exp c.Signature.c_value

let print_interface_value ff name node =
  let print_arg ff arg = match arg.a_name with
      | None -> print_type ff arg.a_type
      | Some(name) ->
        fprintf ff "@[%a : %a@]" print_name name print_type arg.a_type in
  let print_node_params ff p_list =
    print_list_r (fun ff p -> print_name ff p.p_name) "<<" "," ">>" ff p_list
  in
  fprintf ff "@[<v 2>val %a%a@[%a@] returns @[%a@]@,@[%a@]@]"
    print_name name
    print_node_params node.node_params
    (print_list_r print_arg "(" ";" ")") node.node_inputs
    (print_list_r print_arg "(" ";" ")") node.node_outputs
    (print_list_r print_size_constraint " with: " "," "")
      node.node_params_constraints


let print_interface ff =
  let m = Modules.current_module () in
  NamesEnv.iter
    (fun key typdesc -> print_interface_type ff key typdesc) m.m_types;
  NamesEnv.iter
    (fun key constdec -> print_interface_const ff key constdec) m.m_consts;
  NamesEnv.iter
    (fun key sigtype -> print_interface_value ff key sigtype) m.m_values;
  Format.fprintf ff "@."

let print_ident ff id = Format.fprintf ff "%s" (name id)

 let rec print_ck ff = function
  | Cbase -> fprintf ff "base"
  | Con (ck, c, n) ->
      fprintf ff "%a on %a(%a)" print_ck ck print_qualname c print_ident n
  | Cvar { contents = Cindex _ } -> fprintf ff "base"
  | Cvar { contents = Clink ck } -> print_ck ff ck

let rec print_clock ff = function
  | Ck ck -> print_ck ff ck
  | Cprod ct_list ->
      fprintf ff "@[<2>(%a)@]" (print_list_r print_clock """ *""") ct_list

