open Format
open Pp_tools
open Names
open Global_printer
open Obc

let print_vd ff vd =
  fprintf ff "@[<v>";
  if vd.v_mutable then
    fprintf ff "mutable ";
  print_ident ff vd.v_ident;
  fprintf ff ": ";
  print_type ff vd.v_type;
  fprintf ff "@]"

let print_obj ff o =
  fprintf ff "@[<v>"; print_ident ff o.o_ident;
  fprintf ff " : "; print_qualname ff o.o_class;
  fprintf ff "@[<2>%a@]" (print_list_r print_static_exp "<<"","">>") o.o_params;
  (match o.o_size with
     | Some se -> fprintf ff "%a" (print_list_r print_static_exp "[" "][" "]") se
     | None -> ());
  fprintf ff "@]"

let rec print_lhs ff e =
  match e.pat_desc with
    | Lvar x -> print_ident ff x
    | Lmem x -> fprintf ff "mem("; print_ident ff x; fprintf ff ")"
    | Lfield (l, f) -> print_lhs ff l; fprintf ff ".%s" (shortname f)
    | Larray(x, idx) ->
        print_lhs ff x;
        fprintf ff "[";
        print_exp ff idx;
        fprintf ff "]"

and print_ext_value ff w = match w.w_desc with
  | Wvar x -> print_ident ff x
  | Wconst c -> print_static_exp ff c
  | Wmem x -> fprintf ff "mem("; print_ident ff x; fprintf ff ")"
  | Wfield (l, f) -> print_ext_value ff l; fprintf ff ".%s" (shortname f)
  | Warray(x, idx) ->
    print_ext_value ff x;
    fprintf ff "[";
    print_exp ff idx;
    fprintf ff "]"
  | Wbang w -> fprintf ff "(!%a)" print_ext_value w


and print_exps ff e_list = print_list_r print_exp "" "," "" ff e_list

and print_exp ff e =
  match e.e_desc with
    | Eextvalue lhs -> print_ext_value ff lhs
    | Eop(op, e_list) -> print_fun ff (op,e_list)
    | Estruct f_e_list ->
        fprintf ff "@[<v 1>";
        print_list_r
          (fun ff (field, e) -> print_qualname ff field;fprintf ff " = ";
             print_exp ff e)
          "{" ";" "}" ff f_e_list;
        fprintf ff "@]"
    | Earray e_list ->
        fprintf ff "@[";
        print_list_r print_exp "[" ";" "]" ff e_list;
        fprintf ff "@]"
    | Ebang e ->
        fprintf ff "!(%a)" print_exp e

and print_fun ff (f,e_list) =
  if is_infix f
  then
    let (e1,e2) = Misc.assert_2 e_list in
    fprintf ff "%a %a %a" print_exp e1 print_qualname f print_exp e2
 else
    fprintf ff "%a@[<1>%a@]" print_qualname f (print_list_l print_exp "(" "," ")") e_list

let print_asgn ff pref x e =
  fprintf ff "@[%s" pref; print_lhs ff x; fprintf ff " = ";
  fprintf ff "@["; print_exp ff e; fprintf ff "@]";
  fprintf ff "@]"

let print_obj_call ff = function
  | Oobj o -> print_ident ff o
  | Oarray (o, i) ->
      fprintf ff "%a%a"
        print_ident o
        (print_list_r print_lhs "[" "][" "]") i

let print_method_name ff = function
  | Mstep -> fprintf ff "step"
  | Mreset -> fprintf ff "reset"


let rec print_act ff a =
  let print_lhs_tuple ff var_list = match var_list with
    | [] -> ()
    | _ -> fprintf ff "@[(%a)@] =@ " (print_list print_lhs "" "," "") var_list in
  match a with
    | Aassgn (x, e) -> print_asgn ff "" x e
    | Acase(e, tag_act_list) ->
        fprintf ff "@[<v>@[<v 2>switch (";
        print_exp ff e; fprintf ff ") {@ ";
        print_tag_act_list ff tag_act_list;
        fprintf ff "@]@,}@]"
    | Afor(x, i1, i2, act_list) ->
        fprintf ff "@[<v>@[<v 2>for %a = %a to %a {@  %a @]@,}@]"
          print_vd x
          print_exp i1
          print_exp i2
          print_block act_list
    | Awhile (Wwhiledo, e, b) ->
         fprintf ff "@[<v>@[<v 2>while %a do {@  %a @]@,}@]"
           print_exp e
           print_block b
    | Awhile (Wdowhile, e, b) ->
         fprintf ff "@[<v>@[<v 2>do {@  %a @]@,} while %a @]"
           print_block b
           print_exp e
    | Acall_fun (var_list, f, es) ->
        fprintf ff "@[<2>%a%a@]"
          print_lhs_tuple var_list
          print_fun (f, es)
    | Acall (a, var_list, o, meth, es) ->
        fprintf ff "@[<2>%a%a%a.%a(%a)@]"
          print_lhs_tuple var_list
          print_async a
          print_obj_call o
          print_method_name meth
          print_exps es
    | Ablock b ->
        fprintf ff "do@\n  %a@\ndone" print_block b

and print_var_dec_list ff var_dec_list = match var_dec_list with
  | [] -> ()
  | _ ->
      fprintf ff "@[<hov 4>%a@]@ "
        (print_list_r print_vd "var " ";" ";") var_dec_list

and print_block ff b =
  fprintf ff "@[<v>%a%a@]"
    print_var_dec_list b.b_locals
    (print_list_r print_act "" ";" "") b.b_body

and print_tag_act_list ff tag_act_list =
  print_list
    (fun ff (tag, a) ->
       fprintf ff "@[<v 2>case %a:@ %a@]"
         print_static_exp tag
         print_block a)
    "" "" "" ff tag_act_list

let print_method_name ff = function
  | Mreset -> fprintf ff "reset"
  | Mstep -> fprintf ff "step"

let print_arg_list ff var_list =
  fprintf ff "(@[%a@])" (print_list_r print_vd "" "," "") var_list

let print_method ff md =
  fprintf ff "@[<v 2>@[%a%a@ returns %a {@]@ %a@]@\n}"
    print_method_name md.m_name
    print_arg_list md.m_inputs
    print_arg_list md.m_outputs
    print_block md.m_body

let print_class_def ff
    { cd_name = id; cd_mems = mem; cd_objs = objs; cd_methods = m_list } =
  fprintf ff "@[<v 2>machine "; print_qualname ff id; fprintf ff " =@,";
  if mem <> [] then begin
    fprintf ff "@[<hov 4>var ";
    print_list_r print_vd "" ";" "" ff mem;
    fprintf ff ";@]@,"
  end;
  if objs <> [] then begin
    fprintf ff "@[<hov 4>obj ";
    print_list print_obj "" ";" "" ff objs;
    fprintf ff ";@]@,"
  end;
  if mem <> [] || objs <> [] then fprintf ff "@,";
  print_list_r print_method "" "\n" "" ff m_list;
  fprintf ff "@]"

let print_open_module ff name =
  fprintf ff "open %s@." (modul_to_string name)

let print_const_dec ff c =
  fprintf ff "const %a = %a@." print_qualname c.c_name
    print_static_exp c.c_value

let print_prog_desc ff pd = match pd with
  | Pclass cd -> print_class_def ff cd; fprintf ff "@\n@\n"
  | Pconst cd -> print_const_dec ff cd
  | Ptype td -> print_type_dec ff td

let print_prog ff { p_opened = modules; p_desc = descs } =
  List.iter (print_open_module ff) modules;
  List.iter (print_prog_desc ff) descs

let print oc p =
  let ff = formatter_of_out_channel oc in
  fprintf ff "@[-- Code generated by the MiniLucid Compiler@.";
  fprintf ff "@[<v>"; print_prog ff p; fprintf ff "@]@]@."

