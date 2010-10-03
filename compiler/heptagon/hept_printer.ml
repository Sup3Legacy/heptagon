(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* The Heptagon printer *)

open Location
open Misc
open Names
open Idents
open Modules
open Static
open Format
open Global_printer
open Pp_tools
open Types
open Signature
open Heptagon

let iterator_to_string i =
  match i with
    | Imap -> "map"
    | Ifold -> "fold"
    | Ifoldi -> "foldi"
    | Imapfold -> "mapfold"

let print_iterator ff it =
  fprintf ff "%s" (iterator_to_string it)

let rec print_pat ff = function
  | Evarpat n -> print_ident ff n
  | Etuplepat pat_list ->
      fprintf ff "@[<2>(%a)@]" (print_list_r print_pat """,""") pat_list

let rec print_vd ff { v_ident = n; v_type = ty; v_last = last } =
  fprintf ff "%a%a : %a%a"
    print_last last  print_ident n
    print_type ty  print_last_value last

and print_last ff = function
  | Last _ -> fprintf ff "last "
  | _ -> ()

and print_last_value ff = function
  | Last (Some v) -> fprintf ff " = %a" print_static_exp v
  | _ -> ()

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

and print_exps ff e_list =
  print_list_r print_exp "(" "," ")" ff e_list

and print_exp ff e =
 if !Compiler_options.full_type_info then
    fprintf ff "(%a : %a)"
      print_exp_desc e.e_desc print_type e.e_ty
  else fprintf ff "%a" print_exp_desc e.e_desc

and print_exp_desc ff = function
  | Evar x -> print_ident ff x
  | Elast x -> fprintf ff "last %a" print_ident x
  | Econst c -> print_static_exp ff c
  | Epre(None, e) -> fprintf ff "pre %a" print_exp e
  | Epre(Some c, e) ->
    fprintf ff "@[<2>%a fby@ %a@]" print_static_exp c  print_exp e
  | Efby(e1, e2) ->
    fprintf ff "@[<2>%a fby@ %a@]" print_exp e1  print_exp e2
  | Eapp(app, args, reset) ->
    fprintf ff "@[<2>%a@,%a@]"
        print_app (app, args) print_every reset
  | Estruct(f_e_list) ->
    print_record (print_couple print_qualname print_exp """ = """) ff f_e_list
  | Eiterator (it, f, param, args, reset) ->
      fprintf ff "@[<2>(%s (%a)<<%a>>)@,%a@]%a"
        (iterator_to_string it)
        print_app (f, [])
        print_static_exp param
        print_exp_tuple args
        print_every reset

and print_every ff reset =
  print_opt (fun ff id -> fprintf ff " every %a" print_exp id) ff reset

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
  | Earrow ->
    let e1, e2 = assert_2 args in
      fprintf ff "@[<2>%a ->@ %a@]" print_exp e1  print_exp e2

let rec print_eq ff eq =
  match eq.eq_desc with
    | Eeq(p, e) ->
      fprintf ff "@[<2>%a =@ %a@]" print_pat p  print_exp e
    | Eautomaton(state_handler_list) ->
      fprintf ff "@[<v>@[<hv 2>automaton @ %a@]@,end@]"
        print_state_handler_list state_handler_list
    | Eswitch(e, switch_handler_list) ->
      fprintf ff "@[<v>@[<hv 2>switch (%a) {@ %a@]@,}@]"
        print_exp e
        print_switch_handler_list switch_handler_list
    | Epresent(present_handler_list, b) ->
      fprintf ff "@[<v>@[<hv 2>present @ %a%a@]@,end@]"
        print_present_handler_list present_handler_list
        print_default b
    | Ereset(b, e) ->
      fprintf ff "@[<v>@[<hv 2>reset @ %a@]@,every %a@]"
        print_block b   print_exp e

and print_state_handler_list ff tag_act_list =
  print_list
    (fun ff sh ->
       fprintf ff "@[<v 2>state %a:@ %a%a%a@]"
         print_name sh.s_state
         print_block sh.s_block
         (print_escape_list "until") sh.s_until
         (print_escape_list "unless") sh.s_unless)
    "" "" "" ff tag_act_list

and print_escape_list unless ff esc_list = match esc_list with
  | [] -> ()
  | _ ->
      fprintf ff "@,%s %a" unless
      (print_list
         (fun ff esc ->
           let cont = if esc.e_reset then "then" else "continue" in
             fprintf ff "@,| %a %s %a"
               print_exp esc.e_cond   cont  print_name esc.e_next_state)
         "" "" "") esc_list

and print_switch_handler_list ff tag_act_list =
  print_list
    (fun ff sh ->
       fprintf ff "@[<v 2>| %a:@ %a@]"
         print_qualname sh.w_name
         print_block sh.w_block)
    "" "" "" ff tag_act_list

and print_present_handler_list ff present_act_list =
  print_list
    (fun ff ph ->
       fprintf ff "@[<v 2>| %a:@ %a@]"
         print_exp ph.p_cond
         print_block ph.p_block)
    "" "" "" ff present_act_list

and print_default ff b =
  match b.b_equs with
    | [] -> ()
    | _ -> fprintf ff "@[<v 2>default@,%a@]" print_block b

and print_eq_list ff = function
  | [] -> ()
  | l -> print_list_r print_eq """;""" ff l

and print_block ff { b_local = v_list; b_equs = eqs } =
  fprintf ff "%a@[<v2>do@ %a@]" print_local_vars v_list  print_eq_list eqs

let rec print_type_def ff { t_name = name; t_desc = tdesc } =
  let print_type_desc ff = function
    | Type_abs -> ()
    | Type_alias ty -> fprintf ff  " =@ %a" print_type ty
    | Type_enum tag_name_list ->
        fprintf ff " =@ %a" (print_list print_qualname """|""") tag_name_list
    | Type_struct f_ty_list ->
        fprintf ff " =@ %a" (print_record print_field) f_ty_list in
  fprintf ff "@[<2>type %a%a@]@." print_qualname name print_type_desc tdesc

let print_contract ff { c_block = b;
                        c_assume = e_a; c_enforce = e_g; } =
  fprintf ff "@[<v2>contract@\n%a@ assume %a;@ enforce %a@]"
    print_block b
    print_exp e_a
    print_exp e_g

let print_node ff
    { n_name = n; n_input = ni;
      n_block = nb; n_output = no; n_contract = contract;
      n_params = params } =
  fprintf ff "@[node %a%a%a@ returns %a@]@\n%a%a@[<v2>let@ %a@]@\ntel@]@\n@."
    print_qualname n
    print_node_params params
    print_vd_tuple ni
    print_vd_tuple no
    (print_opt print_contract) contract
    print_local_vars nb.b_local
    print_eq_list nb.b_equs

let print_open_module ff name = fprintf ff "open %a@." print_name name

let print oc { p_opened = po; p_types = pt; p_nodes = pn; p_consts = pc } =
  let ff = Format.formatter_of_out_channel oc in
  List.iter (print_open_module ff) po;
  List.iter (print_const_dec ff) pc;
  List.iter (print_type_def ff) pt;
  List.iter (print_node ff) pn;
  fprintf ff "@?"
