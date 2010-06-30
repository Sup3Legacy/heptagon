(** {1 VHDL Backend}

    This is an experimental VHDL backend for MiniLS. It targets VHDL'87, as it
    is the best revision implemented in GHDL. It translates MiniLS programs to
    VHDL programs, and associates a VHDL component to each class.

    Floating-point numbers or unsupported. *)

open Names
open Misc
open Obc
open Types

exception Unimplemented of string

let unimplemented s = raise (Unimplemented s)

(** {2 Preliminaries and utilities} *)

let map_c f (l, r) = (f l, f r)

let map_o f o = match o with None -> None | Some x -> Some (f x)

type ('a, 'b) either =
  | Left of 'a
  | Right of 'b

module S = Set.Make(struct type t = string let compare = Pervasives.compare end)
module M = Map.Make(struct type t = string let compare = Pervasives.compare end)

let unionl = List.fold_left S.union S.empty

(** [modname] is used in translation of longnames. *)
let modname = ref ""

(** {2 VHDL abstract-syntax tree}

    Taking example from the C-NG backend, we implement only the restricted
    subset of VHDL'87 suited for our needs. *)

type name = string

type vhdl_type =
  | Vt_bit
  | Vt_ulogic
  | Vt_boolean
  | Vt_int
  | Vt_id of qualname
  | Vt_array of int * vhdl_type

type polarity =
  | Vp_in
  | Vp_out
  | Vp_inout

type signal_decl = { vs_name : name;
                     vs_polarity : polarity option;
                     vs_type : vhdl_type; }

type vty_decl = { vty_name : name;
                  vty_desc : vty_desc; }
and vty_desc =
  | Vty_opaque
  | Vty_enum of qualname list
  | Vty_record of (name * vhdl_type) list
  | Vty_vector of vhdl_type

type decl =
  | Vd_signal of signal_decl
  | Vd_type of vty_decl
  | Vd_component of name * signal_decl list
  | Vd_bind of name * name * qualname

type const = Types.static_exp

type expr =
  | Ve_var of name
  | Ve_const of const
  | Ve_uop of string * expr
  | Ve_bop of string * expr * expr
  | Ve_event of name
  | Ve_when of expr * expr * expr
  | Ve_funcall of name * expr list
  | Ve_record of (qualname * expr) list
  | Ve_field of expr * qualname
  | Ve_array of expr list
  | Ve_concat of expr * expr
  | Ve_slice of int * int * expr

type instr =
  | Vi_null
  | Vi_wait of expr
  | Vi_wait_ns of int (** /!\ Non-synthetizable construct. Time in ns. *)
  | Vi_if of expr * instr * (expr * instr) list * instr option
  | Vi_loop of instr
  | Vi_seq of instr list
  | Vi_assgn of name * expr (* signals *)
  | Vi_assgn_guarded of name * (expr * expr) list (* guard * body *)
  | Vi_affect of name * expr (* variables *)
  | Vi_case of expr * (const * instr) list

type process_def = { vp_name : name option;
                     vp_sensitivity_list : name list;
                     vp_vars : (name * vhdl_type) list;
                     vp_body : instr; }

type procedure_def = { vpdr_name : name;
                       vpdr_params : signal_decl list;
                       vpdr_vars : (name * vhdl_type) list;
                       vpdr_body : instr; }

type def =
  | Vdef_eq of name * expr
  | Vdef_guarded_eq of name * (expr * expr) list
  | Vdef_comp_inst of name * name * (name * name) list
  | Vdef_process of process_def
  | Vdef_procedure of procedure_def

type architecture_decl = { va_name : name;
                           va_component : name;
                           va_decls : decl list;
                           va_body : def list }

type entity_decl = { ve_name : name;
                     ve_port : signal_decl list;
                     ve_tydecls : vty_decl list; }

type component = { vc_name : name;
                   vc_entity : entity_decl;
                   vc_architecture : architecture_decl; }

type package = { vpack_name : name;
                 vpack_decls : decl list; }

type program = (component, package) either list


(** {2 Pretty-printing of VHDL AST} *)

open Format

let pp_name fmt name =
  let real_name =
    if String.length name > 0 && name.[0] = '_' then "h" ^ name else name in
  fprintf fmt "%s" real_name

let pp_qualname fmt ({ qual = modn; name = id; } as qn) =
  if modn <> !modname
  then fprintf fmt "work.types.%a" pp_name id
  else Global_printer.print_qualname fmt qn

let rec pp_list f fmt l = match l with
  | [] -> ()
  | [x] -> f fmt x
  | h :: t -> fprintf fmt "%a@ %a" f h (pp_list f) t

let rec pp_list_sep f sep fmt l = match l with
  | [] -> ()
  | [x] -> f fmt x
  | h :: t -> fprintf fmt "%a%s@ %a" f h sep (pp_list_sep f sep) t

let pp_list_end f ends fmt l =
  let f fmt a = fprintf fmt "%a%s" f a ends in
  pp_list f fmt l

let rec pp_type fmt ty = match ty with
  | Vt_bit -> fprintf fmt "bit"
  | Vt_boolean -> fprintf fmt "boolean"
  | Vt_ulogic -> fprintf fmt "std_ulogic"
  | Vt_int -> fprintf fmt "integer"
      (* TODO: real longname *)
  | Vt_id ln -> pp_qualname fmt ln
  | Vt_array (size, ty) -> fprintf fmt "%a_vector (0 to %d)" pp_type ty size

let pp_polarity fmt pol = match pol with
  | Vp_in -> fprintf fmt "in"
  | Vp_out -> fprintf fmt "out"
  | Vp_inout -> fprintf fmt "inout"

let pp_signal fmt s =
  let pp_polo fmt polo = match polo with
    | None -> ()
    | Some pol -> fprintf fmt "%a " pp_polarity pol in
  fprintf fmt "signal %a : %a%a"
    pp_name s.vs_name pp_polo s.vs_polarity pp_type s.vs_type

let pp_signals = pp_list_sep pp_signal ";"

let pp_ty_desc fmt desc = match desc with
  | Vty_opaque -> ()
  | Vty_enum nl -> fprintf fmt "( @[%a@] )" (pp_list_sep pp_qualname ",") nl
  | Vty_record ntyl ->
      let pp fmt (n, ty) = fprintf fmt "%a : %a;" pp_name n pp_type ty in
      fprintf fmt "@\n@[<v 2>record@\n%a@]@\nend record" (pp_list pp) ntyl
  | Vty_vector ty ->
      fprintf fmt "@\n@[<v 2>array (integer range <>) of %a@]" pp_type ty

let pp_ty_decl fmt { vty_name = name; vty_desc = desc; } =
  fprintf fmt "@[<v 2>type %a is %a@]" pp_name name pp_ty_desc desc

let pp_decl fmt decl = match decl with
  | Vd_signal sd -> pp_signal fmt sd
  | Vd_type td -> pp_ty_decl fmt td
  | Vd_component (compname, sigs) ->
      fprintf fmt "@[@[<v 2>component %a@\nport (@[" pp_name compname;
      pp_signals fmt sigs;
      fprintf fmt "@]);@]@\nend component@]"
  | Vd_bind (name, compname, entname) ->
      fprintf fmt "@[for %a: %a use entity@ %s.%s@]"
        pp_name name pp_name compname entname.qual entname.name

let pp_decls fmt decls = pp_list_end pp_decl ";" fmt decls

let rec pp_const fmt c = match c.se_desc with
  | Svar n -> fprintf fmt "%s" (fullname n)
  | Sbool false | Sconstructor { qual = "Pervasives"; name = "false"; }
      -> fprintf fmt "'0'"
  | Sbool true | Sconstructor { qual = "Pervasives"; name = "true"; }
      -> fprintf fmt "'1'"
  | Sint i -> fprintf fmt "%d" i
  | Sfield _ -> assert false
  | Sconstructor ln -> pp_qualname fmt ln
  | Sarray_power (c, _) -> fprintf fmt "(others => %a)" pp_const c
  | Sarray cl ->
      fprintf fmt "@[(";
      let rec pp i fmt l = match l with
        | [] -> assert false
        | [c] -> fprintf fmt "%d => %a" i pp_const c
        | c :: l -> fprintf fmt "%d => %a, %a" i pp_const c (pp (i + 1)) l in
      pp 0 fmt cl;
      fprintf fmt ")@]"
  | Srecord fcl ->
      let pp fmt (n, c) = fprintf fmt "%a => %a" pp_qualname n pp_const c in
      fprintf fmt "(@[%a@])" (pp_list_sep pp ",") fcl
  | Sop (fn, cl) ->
      let s = match fn with
        | { qual = "Pervasives"; name = id; } -> id
        | _ -> fullname fn in
      fprintf fmt "(@[%a@])" (pp_list_sep pp_const s) cl
  | Sfloat _ | Stuple _
    ->
      Format.eprintf "VHDL: unsupported constant type: %a@."
        Global_printer.print_static_exp c;
      assert false

let rec pp_expr fmt e = match e with
  | Ve_var vn -> pp_name fmt vn
  | Ve_const c -> pp_const fmt c
  | Ve_uop (op, e) -> fprintf fmt "(%s %a)" op pp_expr e
  | Ve_bop (op, l, r) -> fprintf fmt "(%a %s %a)" pp_expr l op pp_expr r
  | Ve_event n -> fprintf fmt "%a'event" pp_name n
  | Ve_when (t, c, e) ->
      fprintf fmt "%a @[when %a@ else %a@]" pp_expr t pp_expr c pp_expr e
  | Ve_funcall (n, el) ->
      fprintf fmt "%a(@[%a@])" pp_name n (pp_list_sep pp_expr ",") el
  | Ve_field (e, n) ->
      fprintf fmt "%a.%a" pp_expr e pp_qualname n
  | Ve_record fel ->
      let pp fmt (n, e) = fprintf fmt "%a => %a" pp_qualname n pp_expr e in
      fprintf fmt "(@[%a@])" (pp_list_sep pp ",") fel
  | Ve_array el ->
      let rec pp i fmt el = match el with
        | [] -> ()
        | [x] -> fprintf fmt "%d => %a" i pp_expr x
        | h :: t -> fprintf fmt "%d => %a,@ %a" i pp_expr h (pp (i + 1)) t in
      fprintf fmt "(@[%a@])" (pp 0) el
  | Ve_concat (l, r) -> fprintf fmt "@[%a & %a@]" pp_expr l pp_expr r
  | Ve_slice (low, high, e) -> fprintf fmt "%a(%d to %d)" pp_expr e low high

let rec pp_instr fmt instr = match instr with
  | Vi_null -> fprintf fmt "null"
  | Vi_if (c, t, il, Some e) ->
      let pp fmt (e, i) =
        fprintf fmt "@[<v 2>elsif %a then@\n%a;@]@\n" pp_expr e pp_instr i in
      fprintf fmt "@[@[<v 2>if %a then@ %a;@]@\n%a@[<v 2>else@ %a;@]@\nend if@]"
        pp_expr c pp_instr t (pp_list pp) il pp_instr e
  | Vi_if (c, t, il, None) ->
      let pp fmt (e, i) =
        fprintf fmt "@[<v 2>elsif %a then@\n%a;@]@\n" pp_expr e pp_instr i in
      fprintf fmt "@[@[<v 2>if %a then@ %a;@]@\n%aend if@]"
        pp_expr c pp_instr t (pp_list pp) il
  | Vi_wait e -> fprintf fmt "wait until @[%a@]" pp_expr e
  | Vi_assgn (n, e) -> fprintf fmt "%a <= %a" pp_name n pp_expr e
  | Vi_affect (n, e) -> fprintf fmt "%a := %a" pp_name n pp_expr e
  | Vi_assgn_guarded (vn, []) ->
      Printf.eprintf "Ill-formed guarded assignment to %s\n" vn;
      assert false
  | Vi_assgn_guarded (n, clauses) ->
      let pp_guard fmt (exp, guard) =
        fprintf fmt "%a when @[(%a)@]" pp_expr guard pp_expr exp in

      fprintf fmt "@[%a <= @[" pp_name n;
      pp_list_sep pp_guard " else" fmt clauses;
      fprintf fmt "@]@]"
  | Vi_case (e, cll) ->
      let pp_cl fmt (c, i) =
        fprintf fmt "when %a => %a;" pp_const c pp_instr i in
      fprintf fmt "@[@[<v 2>case %a is@\n" pp_expr e;
      pp_list pp_cl fmt cll;
      fprintf fmt "@\nwhen others => null;";
      fprintf fmt "@]@\nend case@]"
  | Vi_seq il -> pp_list_sep pp_instr ";" fmt il;
  | Vi_loop i -> fprintf fmt "@[@[<v 2>loop@\n%a;@]@\nend loop@]" pp_instr i
  | Vi_wait_ns ns -> fprintf fmt "wait for %d ns" ns

let pp_def fmt stm =
  let pp_var fmt (vn, bty) =
    fprintf fmt "@ variable %a : %a;" pp_name vn pp_type bty in
  match stm with
    | Vdef_process { vp_name = nameo; vp_sensitivity_list = sens;
                     vp_vars = vars; vp_body = instr; } ->
        let pp_sensitivity_list fmt list = match list with
          | [] -> ()
          | _ -> fprintf fmt " (%a)" (pp_list_sep pp_name ",") list in
        let pp_label fmt nameo = match nameo with
          | None -> () | Some s -> fprintf fmt "%a : " pp_name s
        and pp_end fmt nameo = match nameo with
          | None -> ()  | Some s -> fprintf fmt " %a" pp_name s in
        fprintf fmt "@[@[<v 2>%aprocess@[%a@]"
          pp_label nameo pp_sensitivity_list sens;

        List.iter (pp_var fmt) vars;

        fprintf fmt "@]@\n@[<v 2>begin@\n";

        pp_instr fmt instr;
        fprintf fmt ";@]@\nend process%a@]" pp_end nameo
    | Vdef_eq (name, e) ->
        fprintf fmt "%a <= @[%a@]" pp_name name pp_expr e
    | Vdef_guarded_eq (n, clauses) ->
        let pp_guard fmt (exp, guard) =
          fprintf fmt "%a when @[(%a)@]" pp_expr guard pp_expr exp in
        fprintf fmt "@[%a <= @[" pp_name n;
        pp_list_sep pp_guard " else" fmt clauses;
        fprintf fmt "@]@]"
    | Vdef_comp_inst (name, compname, bindl) ->
        let pp_bind fmt (f, t) =
          fprintf fmt "%a => %a" pp_name f pp_name t in
        fprintf fmt "@[%a: %a port map (@[%a@])@]"
          pp_name name pp_name compname (pp_list_sep pp_bind ",") bindl
    | Vdef_procedure { vpdr_name = n; vpdr_params = params;
                       vpdr_vars = vars; vpdr_body = body; } ->
        fprintf fmt "@[@[<v 2>procedure %a(%a) is@\n%a"
          pp_name n pp_signals params (pp_list pp_var) vars;
        fprintf fmt "@]@\n@[<v 2>begin@\n%a@]end procedure %a@]"
          pp_instr body pp_name n

let pp_entity fmt e =
  (* fprintf fmt "@[@[<v 2>entity %a is@ port (@[" pp_name e.ve_name; *)
  fprintf fmt "@[@[<v 2>entity %a is" pp_name e.ve_name;
  begin match e.ve_port with
    | _ :: _ ->
        fprintf fmt "@ port (@[";
        pp_signals fmt e.ve_port;
        fprintf fmt "@]);@]"
    | [] -> ()
  end;
  List.iter (fun tyd -> fprintf fmt "%a@\n" pp_ty_decl tyd) e.ve_tydecls;
  fprintf fmt "@ end entity %a;@]@\n" pp_name e.ve_name

let pp_architecture fmt a =
  fprintf fmt "@[@[<v 2>architecture %a of %a is@ "
    pp_name a.va_name pp_name a.va_component;

  (* Hack: we'll need this function in all cases, and we cannot use our own
     AST because of implicit boolean->bit conversions. *)
  let arr = ["function to_bit(b : boolean) return bit is";
             "begin";
             "  if b then";
             "    return '1';";
             "  else";
             "    return '0';";
             "  end if;";
             "end to_bit;";
             "";
             "function to_logic(b : boolean) return std_ulogic is";
             "begin";
             "  if b then";
             "    return '1';";
             "  else";
             "    return '0';";
             "  end if;";
             "end to_logic;"] in
  List.iter (fprintf fmt "%s@\n") arr;

  pp_decls fmt a.va_decls;
  fprintf fmt "@]@\n@[<v 2>begin@\n";
  pp_list_sep pp_def ";" fmt a.va_body;
  fprintf fmt "@];@\nend architecture %a;@]@\n" pp_name a.va_name

let pp_component fmt c =
  fprintf fmt "use work.types.all;@\n@\n";
  fprintf fmt "library ieee;@\n";
  fprintf fmt "use ieee.std_logic_1164.all;@\n@\n";
  pp_entity fmt c.vc_entity;
  fprintf fmt "@\n";
  pp_architecture fmt c.vc_architecture;
  fprintf fmt "@."

let pp_package fmt p =
  fprintf fmt "@[@[<v 2>package %a is@\n%a@]@\nend package %a;@]"
    pp_name p.vpack_name pp_decls p.vpack_decls pp_name p.vpack_name;
  fprintf fmt "@."

let print_component f c = f (c.vc_name ^ ".vhd") pp_component c

let print_package f p = f (p.vpack_name ^ ".vhd") pp_package p

let with_formatter_of dir file func arg =
  let fn = Filename.concat dir file in
  if !Compiler_options.verbose then Printf.printf "VHDL: outputting to %s\n" fn;
  let oc = open_out fn in
  let fmt = formatter_of_out_channel oc in
  func fmt arg;
  close_out oc

let print dir p =
  let print_item e = match e with
    | Left c -> print_component (with_formatter_of dir) c
    | Right p -> print_package (with_formatter_of dir) p in
  List.iter print_item p

(** {3 Conventions regarding translations to VHDL} *)

let bench_name n = n ^ "_tb"

(** [period] is the clock's period in nanoseconds. It should always be > 1. *)
let period = 2

let ck_n = Idents.fresh "clk"
and rs_n = Idents.fresh "rst"
and hr_n = Idents.fresh "hw_rst"

let clock_signal = { vs_name = Idents.name ck_n; vs_polarity = Some Vp_in;
                     vs_type = Vt_ulogic; }

let hwrst_signal = { vs_name = Idents.name hr_n; vs_polarity = Some Vp_in;
                     vs_type = Vt_bit; }

let native_signals =
  [
    clock_signal;
    hwrst_signal;
  ]

let base_signals =
  native_signals @ [{ vs_name = Idents.name rs_n; vs_polarity = Some Vp_in;
                      vs_type = Vt_bit; };]
