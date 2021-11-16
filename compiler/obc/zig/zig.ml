open Format
open List
open Names

let zigname_of_name name = 
  let buf = Buffer.create (String.length name) in
  let convert c =
    match c with
      | 'A'..'Z' | 'a'..'z' | '0'..'9' | '_' ->
          Buffer.add_char buf c
      | '\'' -> Buffer.add_string buf "_prime"
      | _ ->
          Buffer.add_string buf "lex";
          Buffer.add_string buf (string_of_int (Char.code c));
          Buffer.add_string buf "_" in
  String.iter convert name;
  Buffer.contents buf

type zigty =
  | Zigty_int
  | Zigty_float
  | Zigty_char
  | Zigty_id of qualname
  | Zigty_ptr of zigty
  | Zigty_arr of int * zigty
  | Zigty_void

type zigblock = {
  var_decls : (string * zigty) list;
  block_body : zigstm list;
}

and zigexpr =
  | Ziguop of string * zigexpr
  | Zigbop of string * zigexpr * zigexpr
  | Zigfun_call of string * zigexpr list
  | Zigaddrof of zigexpr
  | Zigstructlit of string * zigexpr list
  | Zigarraylit of zigexpr list
  | Zigconst of zigconst
  | Zigvar of string
  | Zigderef of zigexpr
  | Zigfield of zigexpr * qualname
  | Zigarray of zigexpr * zigexpr

and zigconst =
  | Zigint of int
  | Zigfloat of float
  | Zigtag of string
  | Zigstrlit of string

and ziglhs =
  | ZigLvar of string
  | ZigLderef of ziglhs
  | ZigLfield of ziglhs * qualname
  | ZigLarray of ziglhs * zigexpr

and zigstm =
  | Zigsexpr of zigexpr
  | Zigsblock of zigblock
  | Zigskip 
  | Zigaffect of ziglhs * zigexpr
  | Zigif of zigexpr * zigstm list * zigstm list
  | Zigswitch of zigexpr * (string * zigstm list) list
  | Zigwhile of zigexpr * zigstm list
  | Zigfor of string * zigexpr * zigexpr * zigstm list
  | Zigreturn of zigexpr

type zigdecl =
  | Zigdecl_enum of string * string list
  | Zigdecl_struct of string * (string * zigty) list
  | Zigdecl_constant of string * zigty * zigexpr

type zigfundef = {
  f_name: string;
  f_retty: zigty;
  f_args: (string * zigty) list;
  f_body: zigblock;
}

type zigdef =
  | Zigfundef of zigfundef
  | Zigvardef of string * zigty

(* Here no need for header files! *)
type zigfile = string * zigdecl list

let rec pp_list1 f sep fmt l = match l with
  | [] -> ()
  | [x] -> fprintf fmt "%a" f x
  | h :: t -> fprintf fmt "%a%s@ %a" f h sep (pp_list1 f sep) t

let rec pp_list f sep fmt l = match l with
  | [] -> ()
  | h :: t -> fprintf fmt "@ %a%s%a" f h sep (pp_list f sep) t

let pp_string fmt s =
  fprintf fmt "%s" (zigname_of_name s)

let rec modul_to_zigname q = match q with
  | Pervasives | LocalModule -> ""
  | Module m -> m ^ "__"
  | QualModule { qual = q; name = n } ->
      (modul_to_zigname q)^n^"__"

let zigname_of_qn qn =
  (modul_to_zigname qn.qual) ^ qn.name

let pp_qualname fmt q =
  pp_string fmt (zigname_of_qn q)

let pp_shortname fmt q =
  pp_string fmt q.name

let rec pp_zigty fmt zigty = match zigty with
  | Zigty_int -> fprintf fmt "isize" (* Kinda important! *)
  | Zigty_float -> fprintf fmt "f32"
  | Zigty_char -> fprintf fmt "u8" (* ! Or maybe signed ? *)
  | Zigty_id s -> pp_qualname fmt s
  | Zigty_ptr zigty' -> fprintf fmt "%a*" pp_zigty zigty'
  | Zigty_arr (n, zigty') -> fprintf fmt "%a[%d]" pp_zigty zigty' n
  | Zigty_void -> fprintf fmt "void"

let rec pp_array_decl zigty =
  match zigty with
    | Zigty_arr(n, zigty') ->
        let ty, s = pp_array_decl zigty' in
        ty, sprintf "[%d]%s" n s
    | _ -> zigty, ""

let truc = 0;;

let rec pp_vardecl fmt (s, zigty) = match zigty with
  | Zigty_arr _ ->
      let ty, indices = pp_array_decl zigty in
      fprintf fmt "%a %a%s = undefined" pp_zigty ty  pp_string s indices
  | _ -> fprintf fmt "%a: %a" pp_string s pp_zigty zigty  
and pp_param_list fmt l = pp_list1 pp_vardecl "," fmt l
and pp_var_list fmt l = pp_list pp_vardecl ";" fmt l

let rec pp_zigblock fmt cb =
  let pp_varlist = pp_list pp_vardecl ";" in
  fprintf fmt "%a%a" pp_varlist cb.var_decls pp_zigstm_list cb.block_body
and pp_zigstm_list fmt stml = pp_list pp_zigstm ";" fmt stml
and pp_zigstm fmt stm = match stm with
  | Zigsexpr e -> fprintf fmt "%a" pp_zigexpr e
  | Zigswitch (e, cl) ->
      let pp_clause fmt (tag, stml) =
        fprintf fmt "@[<v 2>case %a:%a@ break;@]"
          pp_zigexpr (Zigconst (Zigtag tag)) pp_zigstm_list stml in
      fprintf fmt
        "@[<v>@[<v 2>switch (%a) {%a@ @[<v 2>default:@ break;@]@]@ }@]"
        pp_zigexpr e (pp_list pp_clause "") cl
  | Zigaffect (lhs, e) ->
      fprintf fmt "%a = %a" pp_ziglhs lhs pp_zigexpr e
  | Zigif (c, t, []) ->
      fprintf fmt "@[<v>@[<v 2>if (%a) {%a@]@ }@]"
        pp_zigexpr c pp_zigstm_list t
  | Zigif (c, t, e) ->
      fprintf fmt "@[<v>@[<v 2>if (%a) {%a@]@ @[<v 2>} else {%a@]@ }@]"
        pp_zigexpr c pp_zigstm_list t pp_zigstm_list e
  | Zigfor(x, lower, upper, e) ->
      fprintf fmt
        "@[<v>@[<v 2>{@\nint %a;@\n@[<v 2>for (%a = %a; %a < %a; ++%a) {%a@]@ }@]@\n}@]"
        pp_string x
        pp_string x  pp_zigexpr lower  pp_string x
        pp_zigexpr upper  pp_string x  pp_zigstm_list e
  | Zigwhile (e, b) ->
      fprintf fmt "@[<v>@[<v 2>while (%a) {%a@]@ }@]" pp_zigexpr e pp_zigstm_list b
  | Zigsblock cb -> pp_zigblock fmt cb
  | Zigskip -> fprintf fmt ""
  | Zigreturn e -> fprintf fmt "return %a" pp_zigexpr e
and pp_zigexpr fmt ce = match ce with
  | Ziguop (s, e) -> fprintf fmt "%s(%a)" s  pp_zigexpr e
  | Zigbop (s, l, r) -> fprintf fmt "(%a%s%a)" pp_zigexpr l s pp_zigexpr r
  | Zigfun_call (s, el) ->
      fprintf fmt "%a(@[%a@])"  pp_string s  (pp_list1 pp_zigexpr ",") el
  | Zigaddrof (Zigderef e) -> pp_zigexpr fmt e
  | Zigderef (Zigaddrof e) -> pp_zigexpr fmt e
  | Zigaddrof e -> fprintf fmt "&%a" pp_zigexpr e
  | Zigstructlit (s, el) ->
      fprintf fmt "(%a){@[%a@]}" pp_string s (pp_list1 pp_zigexpr ",") el
  | Zigarraylit el -> (* TODO master : WRONG *)
      fprintf fmt "((int []){@[%a@]})" (pp_list1 pp_zigexpr ",") el
  | Zigconst c -> pp_zigconst fmt c
  | Zigvar s -> pp_string fmt s
  | Zigderef e -> fprintf fmt "*%a" pp_zigexpr e
  | Zigfield (Zigderef e, f) -> fprintf fmt "%a->%a" pp_zigexpr e pp_shortname f
  | Zigfield (e, f) -> fprintf fmt "%a.%a" pp_zigexpr e pp_shortname f
  | Zigarray (e1, e2) -> fprintf fmt "%a[%a]" pp_zigexpr e1 pp_zigexpr e2

and pp_zigconst_expr fmt ce = match ce with
  | Zigstructlit (_, el) ->
      fprintf fmt "{@[%a@]}" (pp_list1 pp_zigconst_expr ",") el
  | Zigarraylit el ->
      fprintf fmt "{@[%a@]}" (pp_list1 pp_zigconst_expr ",") el
  | _ -> pp_zigexpr fmt ce

and pp_ziglhs fmt ziglhs = match ziglhs with
  | ZigLvar s -> pp_string fmt s
  | ZigLderef lhs' -> fprintf fmt "*%a" pp_ziglhs lhs'
  | ZigLfield (ZigLderef lhs, f) -> fprintf fmt "%a->%a" pp_ziglhs lhs  pp_shortname f
  | ZigLfield (lhs, f) -> fprintf fmt "%a.%a" pp_ziglhs lhs  pp_shortname f
  | ZigLarray (lhs, e) ->
      fprintf fmt "%a[%a]"
        pp_ziglhs lhs
        pp_zigexpr e

and pp_zigconst fmt zigconst = match zigconst with
  | Zigint i -> fprintf fmt "%d" i
  | Zigfloat f -> fprintf fmt "%f" f
  | Zigtag t -> pp_string fmt t
  | Zigstrlit t -> fprintf fmt "\"%s\"" (String.escaped t)


let pp_zigdecl fmt zigdecl = match zigdecl with
  | Zigdecl_enum (s, sl) ->
    (* Original was "@[<v>@[<v 2>typedef enum {@ %a@]@ } %a;@ @]@\n" *)
      fprintf fmt "@[<v>const %a = struct {@ %a@}]@\n" 
      pp_string s (pp_list1 pp_string ",") sl
  | Zigdecl_struct (s, fl) ->
      let pp_field fmt (s, zigty) =
        fprintf fmt "@ %a;" pp_vardecl (s,zigty) in
      fprintf fmt "@[<v>@[<v 2>const %a = struct {"  pp_string s;
      List.iter (pp_field fmt) fl;
      fprintf fmt "@]@ } %a;@ @]@\n"  pp_string s
  | Zigdecl_constant (n, zigty, ce) ->
      fprintf fmt "@[<v>static const %a = %a;@ @]@\n"
        pp_vardecl (n, zigty)  pp_zigconst_expr ce

let pp_zigdef fmt zigdef = match zigdef with
| Zigfundef zigfd ->
    fprintf fmt
      "@[<v>@[<v 2>pub fn %a(@[<hov>%a@]) -> %a {%a@]@ }@ @]@\n"
      pp_string zigfd.f_name  pp_zigty zigfd.f_retty  pp_param_list zigfd.f_args
      pp_zigblock zigfd.f_body
| Zigvardef (s, zigty) -> fprintf fmt "var %a: %a = undefined;@\n" pp_string s pp_zigty zigty  

let pp_zigfile_desc fmt filen zigfile =
  (* [filen_wo_ext] is the file's name without the extension. *)
  let filen_wo_ext = String.sub filen 0 (String.length filen - 2) in
  let (deps, zigdecls) = zigfile in
  iter (fun d -> fprintf fmt "const %s = @include(\"%s.zig\");@\n" d d) deps;
  iter (pp_zigdecl fmt) zigdecls;;


let output_zigfile dir (filen, zigfile_desc) =
  if !Compiler_options.verbose then
    Format.printf "ZIG generating %s/%s@." dir filen;
  let oc = open_out (Filename.concat dir filen) in
  let fmt = Format.formatter_of_out_channel oc in
  pp_zigfile_desc fmt filen zigfile_desc;
  pp_print_flush fmt ();
  close_out oc
  
let output dir zigprog =
  List.iter (output_zigfile dir) zigprog

let is_pointer_type = function
  | Zigty_ptr _ -> true
  | _ -> false

let rec ziglhs_of_zigexpr zigexpr =
  match zigexpr with
  | Zigvar v -> ZigLvar v
  | Zigderef e -> ZigLderef (ziglhs_of_zigexpr e)
  | Zigfield (e,qn) -> ZigLfield (ziglhs_of_zigexpr e, qn)
  | Zigarray (e1,e2) -> ZigLarray (ziglhs_of_zigexpr e1, e2)
  | _ -> failwith("Zig expression not translatable to LHS")

let rec array_base_zigtype ty idx_list =
  match ty, idx_list with
    | Zigty_arr (_, ty), [_] -> ty
    | Zigty_arr (_, ty), _::idx_list -> array_base_zigtype ty idx_list
    | _ ->
      assert false