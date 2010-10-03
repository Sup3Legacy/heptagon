open Misc
open Names
open Idents
open Types
open Clocks
open Static
open Format
open Signature
open Global_printer
open Pp_tools
open Minils

(** Every print_ function is boxed, that is it doesn't export break points,
    Exceptions are [list] class functions *)

(** Every print_ function is without heading carry return or white space *)

let iterator_to_string i =
  match i with
    | Imap -> "map"
    | Ifold -> "fold"
    | Ifoldi -> "foldi"
    | Imapfold -> "mapfold"

let rec print_pat ff = function
  | Evarpat n -> print_ident ff n
  | Etuplepat pat_list ->
      fprintf ff "@[<2>(%a)@]" (print_list_r print_pat """,""") pat_list

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

let print_vd ff { v_ident = n; v_type = ty; v_clock = ck } =
  if !Compiler_options.full_type_info then
    fprintf ff "%a : %a :: %a" print_ident n print_type ty print_ck ck
  else fprintf ff "%a : %a" print_ident n print_type ty

let print_local_vars ff = function
  | [] -> ()
  | l -> fprintf ff "@[<4>%a@]@\n" (print_list_r print_vd "var "";"";") l

let print_const_dec ff c =
  if !Compiler_options.full_type_info then
    fprintf ff "const %a : %a = %a"
      print_qualname c.c_name print_type c.c_type print_static_exp c.c_value
  else
    fprintf ff "const %a = %a"
      print_qualname c.c_name print_static_exp c.c_value;
  fprintf ff "@."


let rec print_params ff l =
  fprintf ff "@[<2>%a@]" (print_list_r print_static_exp "<<"","">>") l

and print_node_params ff l =
  fprintf ff "@[<2>%a@]" (print_list_r print_param "<<"","">>") l

and print_exp_tuple ff l =
  fprintf ff "@[<2>(%a)@]" (print_list_r print_exp """,""") l

and print_vd_tuple ff l =
  fprintf ff "@[<2>%a@]" (print_list_r print_vd "("";"")") l

and print_index ff idx =
  fprintf ff "@[<2>%a@]" (print_list print_static_exp "[""][""]") idx

and print_dyn_index ff idx =
  fprintf ff "@[<2>%a@]" (print_list print_exp "[""][""]") idx

and print_exp ff e =
  if !Compiler_options.full_type_info then
    fprintf ff "(%a : %a :: %a)"
      print_exp_desc e.e_desc print_type e.e_ty print_ck e.e_ck
  else fprintf ff "%a" print_exp_desc e.e_desc

and print_every ff reset =
  print_opt (fun ff id -> fprintf ff " every %a" print_ident id) ff reset

and print_exp_desc ff = function
  | Econst c -> print_static_exp ff c
  | Evar x -> print_ident ff x
  | Efby ((Some c), e) ->
      fprintf ff "@[<2>%a fby@ %a@]" print_static_exp c print_exp e
  | Efby (None, e) -> fprintf ff "pre %a" print_exp e
  | Eapp (app, args, reset) ->
      fprintf ff "@[<2>%a@,%a@]"
        print_app (app, args) print_every reset
  | Ewhen (e, c, n) ->
      fprintf ff "@[<2>(%a@ when %a(%a))@]"
        print_exp e print_qualname c print_ident n
  | Emerge (x, tag_e_list) ->
      fprintf ff "@[<2>merge %a@ %a@]"
        print_ident x print_tag_e_list tag_e_list
  | Estruct f_e_list ->
      print_record (print_couple print_qualname print_exp """ = """) ff f_e_list
  | Eiterator (it, f, param, args, reset) ->
      fprintf ff "@[<2>(%s (%a)<<%a>>)@,%a@]%a"
        (iterator_to_string it)
        print_app (f, [])
        print_static_exp param
        print_exp_tuple args
        print_every reset

and print_app ff (app, args) = match app.a_op with
  | Eequal ->
    let e1, e2 = assert_2 args in
      fprintf ff "@[<2>%a@ = %a@]" print_exp e1  print_exp e2
  | Etuple -> print_exp_tuple ff args
  | Efun f | Enode f ->
      fprintf ff "@[%a@,%a@,%a@]"
        print_qualname f print_params app.a_params  print_exp_tuple args
  | Eifthenelse ->
    let e1, e2, e3 = assert_3 args in
      fprintf ff "@[<hv>if %a@ then %a@ else %a@]"
        print_exp e1 print_exp e2 print_exp e3
  | Efield ->
    let r = assert_1 args in
    let f = assert_1 app.a_params in
    fprintf ff "%a.%a" print_exp r print_static_exp f
  | Efield_update ->
    let r,e = assert_2 args in
    let f = assert_1 app.a_params in
      fprintf ff "@[<2>{%a with .%a =@ %a}@]"
        print_exp r print_static_exp f print_exp e
  | Earray -> fprintf ff "@[<2>%a@]" (print_list_r print_exp "["";""]") args
  | Earray_fill ->
    let e = assert_1 args in
    let n = assert_1 app.a_params in
      fprintf ff "%a^%a" print_exp e print_static_exp n
  | Eselect ->
    let e = assert_1 args in
      fprintf ff "%a%a" print_exp e print_index app.a_params
  | Eselect_slice ->
    let e = assert_1 args in
    let idx1, idx2 = assert_2 app.a_params in
      fprintf ff "%a[%a..%a]"
        print_exp e  print_static_exp idx1  print_static_exp idx2
  | Eselect_dyn ->
    let r, d, e = assert_2min args in
      fprintf ff "%a%a default %a"
        print_exp r  print_dyn_index e  print_exp d
  | Eupdate ->
    let e1, e2, idx = assert_2min args in
        fprintf ff "@[<2>(%a with %a =@ %a)@]"
          print_exp e1 print_dyn_index idx print_exp e2
  | Econcat ->
    let e1, e2 = assert_2 args in
      fprintf ff "@[<2>%a@ @@ %a@]" print_exp e1  print_exp e2

and print_handler ff c =
  fprintf ff "@[<2>%a@]" (print_couple print_qualname print_exp "("" -> "")") c

and print_tag_e_list ff tag_e_list =
  fprintf ff "@[%a@]" (print_list print_handler """""") tag_e_list


and print_eq ff { eq_lhs = p; eq_rhs = e } =
  if !Compiler_options.full_type_info
  then fprintf ff "@[<2>%a :: %a =@ %a@]"
    print_pat p  print_ck e.e_ck  print_exp e
  else fprintf ff "@[<2>%a =@ %a@]" print_pat p  print_exp e


and print_eqs ff = function
  | [] -> ()
  | l -> fprintf ff "@[<v2>let@ %a@]@\ntel" (print_list_r print_eq """;""") l

let print_open_module ff name = fprintf ff "open %a@." print_name name

let rec print_type_dec ff { t_name = name; t_desc = tdesc } =
  let print_type_desc ff = function
    | Type_abs -> ()
    | Type_alias ty -> fprintf ff  " =@ %a" print_type ty
    | Type_enum tag_name_list ->
        fprintf ff " =@ %a" (print_list print_qualname """|""") tag_name_list
    | Type_struct f_ty_list ->
        fprintf ff " =@ %a" (print_record print_field) f_ty_list in
  fprintf ff "@[<2>type %a%a@]@." print_qualname name print_type_desc tdesc


let print_contract ff { c_local = l; c_eq = eqs;
                        c_assume = e_a; c_enforce = e_g; } =
  fprintf ff "@[<v2>contract@\n%a%a@ assume %a;@ enforce %a@]"
    print_local_vars l
    print_eqs eqs
    print_exp e_a
    print_exp e_g


let print_node ff { n_name = n; n_input = ni; n_output = no;
                    n_contract = contract; n_local = nl;
                    n_equs = ne; n_params = params } =
  fprintf ff "@[node %a%a%a@ returns %a@]@\n%a%a%a@]@\n@."
    print_qualname n
    print_node_params params
    print_vd_tuple ni
    print_vd_tuple no
    (print_opt print_contract) contract
    print_local_vars nl
    print_eqs ne


let print oc { p_opened = pm; p_types = pt; p_nodes = pn; p_consts = pc } =
  let ff = formatter_of_out_channel oc in
  List.iter (print_open_module ff) pm;
  List.iter (print_const_dec ff) pc;
  List.iter (print_type_dec ff) pt;
  List.iter (print_node ff) pn;
  fprintf ff "@?"
