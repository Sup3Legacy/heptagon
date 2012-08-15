open Names
open Signature
open Clocks
open Modules
open Format
open Pp_tools


let rec _aux_print_modul ~full ff m = match m with
  | Pervasives ->
      if !Compiler_options.full_qual_info
      then fprintf ff "_Pervasives."
      else ()
  | LocalModule m ->
      if !Compiler_options.full_qual_info
      then fprintf ff "_local_%a" (_aux_print_modul ~full:full) m
      else ()
  | _ when m = g_env.current_mod && not full -> ()
  | Module m -> fprintf ff "%a." print_name m
  | QualModule { qual = m; name = n } ->
      fprintf ff "%a%a." (_aux_print_modul ~full:full) m print_name n

(** Prints a [modul] with a [.] at the end when not empty *)
let _print_modul ~full ff m = match m with
  | Pervasives ->
      if !Compiler_options.full_qual_info
      then fprintf ff "_Pervasives"
      else ()
  | LocalModule m ->
      if !Compiler_options.full_qual_info
      then fprintf ff "_local_%a" (_aux_print_modul ~full:full) m
      else ()
  | _ when m = g_env.current_mod && not full -> ()
  | Module m -> fprintf ff "%a" print_name m
  | QualModule { qual = m; name = n } ->
      fprintf ff "%a%a" (_aux_print_modul ~full:full) m print_name n

let print_full_modul ff m = _print_modul ~full:true ff m
let print_modul ff m = _print_modul ~full:false ff m

let _print_qualname ?(full=false) ff { qual = q; name = n} = match q with
  | Pervasives -> print_name ff n
  | _ when q = g_env.current_mod && not full -> print_name ff n
  | LocalModule m ->
      if !Compiler_options.full_qual_info
      then fprintf ff "_local_%a%a" (_aux_print_modul ~full:full) m print_name n
      else print_name ff n
  | _ -> fprintf ff "%a%a" (_aux_print_modul ~full:full) q print_name n


let print_qualname ff qn = _print_qualname ~full:(!Compiler_options.full_qual_info) ff qn
let print_full_qualname ff qn = _print_qualname ~full:true ff qn

let print_qualenv print_value ff env =
  fprintf ff "@[<2>";
  QualEnv.iter (fun k v -> fprintf ff "%a -> %a@ " print_full_qualname k print_value v) env;
  fprintf ff "@]"

let print_shortname ff {name = n} = print_name ff n

let print_ident = Idents.print_ident

let rec print_ck ff = function
  | Cbase -> fprintf ff "."
  | Con (ck, c, n) ->
      fprintf ff "%a on %a(%a)" print_ck ck print_static_exp c print_ident n
  | Cvar { contents = Cindex i } -> fprintf ff "'a%i" i
  | Cvar { contents = Clink ck } -> fprintf ff "~> %a" print_ck ck

and print_ct ff = function
  | Ck ck -> print_ck ff ck
  | Cprod ct_list ->
      fprintf ff "@[<2>(%a)@]" (print_list_r print_ct """ *""") ct_list

and print_sck ff = function
  | Signature.Cbase -> fprintf ff "."
  | Signature.Con (ck, c, n) ->
      fprintf ff "%a on %a(%a)" print_sck ck print_static_exp c print_name n

and print_params ff p_l =
  fprintf ff "@[<2>%a@]" (print_list_r print_static_exp "<<" "," ">>") p_l

and print_static_exp_desc ff sed = match sed with
  | Sint i -> fprintf ff "%ld" i
  | Sbool b -> fprintf ff "%b" b
  | Sfloat f -> fprintf ff "%f" f
  | Sstring s -> fprintf ff "\"%s\"" (String.escaped s)
  | Sconstructor ln -> print_qualname ff ln
  | Sfield ln -> print_qualname ff ln
  | Svar id -> print_qualname ff id
  | Sfun (f, se_list) ->
      fprintf ff "@[<2>%a@,%a@]"
        print_qualname f
        print_params se_list
  | Sop (op, se_list) ->
      if is_infix op
      then
        let e1,e2 = Misc.assert_2 se_list in
        fprintf ff "(@[%a@ %s %a@])" print_static_exp e1  (shortname op)  print_static_exp e2
      else
        fprintf ff "@[<2>%a@,%a@]"
          print_qualname op  print_static_exp_tuple se_list
  | Sarray_power (se, n_list) ->
      fprintf ff "%a^%a" print_static_exp se (print_list print_static_exp """^""") n_list
  | Sarray se_list ->
      fprintf ff "@[<2>%a@]" (print_list_r print_static_exp "["",""]") se_list
  | Stuple se_list -> print_static_exp_tuple ff se_list
  | Srecord f_se_list ->
      print_record (print_couple print_qualname
                      print_static_exp """ = """) ff f_se_list
  | Sasync se -> fprintf ff "@[<2>async %a@]" print_static_exp se

and print_static_exp ff se =
  if !Compiler_options.full_type_info then
    fprintf ff "(%a : %a)"
      print_static_exp_desc se.se_desc print_type se.se_ty
  else
    fprintf ff "%a" print_static_exp_desc se.se_desc

and print_static_exp_tuple ff l =
  fprintf ff "@[<2>%a@]" (print_list_r print_static_exp "("","")") l

and print_type ff = function
  | Tinvalid -> fprintf ff "INVALID TYPE"
  | Tprod ty_list ->
      fprintf ff "@[<hov2>%a@]" (print_list_r print_type "(" " *" ")") ty_list
  | Tid id -> print_qualname ff id
  | Tarray (ty, n) ->
      fprintf ff "@[<hov2>%a^%a@]" print_type ty print_static_exp n
  | Tfuture (a, t) -> fprintf ff "(%a%a)" print_future a print_type t
  | Tbounded n -> fprintf ff "int{ < %a }" print_static_exp n

and print_async ff async = match async with
  | None -> ()
  | Some i_l -> fprintf ff "async@[%a@]" print_params i_l

and print_future ff future = match future with
  | () -> fprintf ff "future "

let print_field ff field =
  fprintf ff "@[%a: %a@]" print_qualname field.f_name  print_type field.f_type

let print_struct ff field_list = print_record print_field ff field_list

let print_constrnt ff c = print_static_exp ff c

let print_constraints ff c_l =
  fprintf ff "@[%a@]" (print_list_r print_constrnt "|"";"";") c_l

let print_interface_type ff (name,tdesc) =
  match tdesc with
    | Type_abstract -> fprintf ff "@[type %s@]" name
    | Type_enum tag_name_list ->
        fprintf ff "@[<2>type %s =@ %a@]"
          name
          (print_list_r print_qualname "" " |" "") tag_name_list;
    | Type_struct f_ty_list ->
        fprintf ff "@[<2>type %s =@ %a@]" name print_struct f_ty_list
    | Type_alias t -> fprintf ff "@[<2>type %s = %a@]" name print_type t

let print_type_dec ff t =
  let name = Misc.print_pp_to_string print_qualname t.t_name in
  print_interface_type ff (name, t.t_desc)

let print_interface_const ff (name,c) =
  fprintf ff "@[<2>const %a : %a = %a@]"
      print_name name
      print_type c.Signature.c_type
      print_static_exp c.Signature.c_value

let print_sarg ff arg = match arg.a_name with
    | None ->
        fprintf ff "@[%a :: %a@]" print_type arg.a_type print_sck arg.a_clock
    | Some(name) ->
        fprintf ff "@[%a : %a :: %a@]"
          print_name name
          print_type arg.a_type
          print_sck arg.a_clock

let rec print_sig_params ff p_l =
  let print_param ff p = match p.p_type with
    | Tconst ty -> fprintf ff "%a:%a" Names.print_name p.p_name print_type ty
(*    | Tabstype t -> print_interface_type ff (p.p_name, t) *)
    | Tsig node -> print_interface_value ff (p.p_name, node)
  in
  fprintf ff "@[<2>%a@]" (print_list_r print_param "<<" "," ">>") p_l

and print_interface_value ff (name,node) =
(*  let print_node_params ff (p_list, constraints) =
    fprintf ff "@[<2><<@[%a@]%a>>@]"
      (print_list_r (fun ff p -> print_name ff p.p_name) "" "," "") p_list
      print_constraints constraints
  in*)
  fprintf ff "@[<4>val %a@,@[<2>%a@]%a@,@[<1>%a@]@ returns @[<1>%a@]@]"
    print_name name
    print_sig_params node.node_params
    print_constraints node.node_param_constraints
    (print_list_r print_sarg "(" ";" ")") node.node_inputs
    (print_list_r print_sarg "(" ";" ")") node.node_outputs

let print_interface ff =
  let m = Modules.get_current_module () in
  Format.fprintf ff "@[<v>";
  NamesEnv.iter
    (fun key typdesc -> Format.fprintf ff "%a@," print_interface_type (key,typdesc)) m.m_types;
  NamesEnv.iter
    (fun key constdec -> Format.fprintf ff "%a@," print_interface_const (key,constdec)) m.m_consts;
  NamesEnv.iter
    (fun key sigtype -> Format.fprintf ff "%a@," print_interface_value (key,sigtype)) m.m_values;
  Format.fprintf ff "@]@."


