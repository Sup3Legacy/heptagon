(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

open List
open Misc
open Names
open Idents
open Obc
open Obc_utils
open Signature

open Modules
open C
open Location
open Format



let load_conf () =
  Compiler_options.enforce_callgraph := true

module Error =
struct
  type error =
    | Evar of string
    | Enode of string
    | Eno_unnamed_output
    | Ederef_not_pointer
    | Estatic_exp_compute_failed
    | Eunknown_method of string

  let message loc kind = (match kind with
    | Evar name ->
        eprintf "%aCode generation : The variable name '%s' is unbound.@."
          print_location loc name
    | Enode name ->
        eprintf "%aCode generation : The node name '%s' is unbound.@."
          print_location loc name
    | Eno_unnamed_output ->
        eprintf "%aCode generation : Unnamed outputs are not supported.@."
          print_location loc
    | Ederef_not_pointer ->
        eprintf "%aCode generation : Trying to deference a non pointer type.@."
          print_location loc
    | Estatic_exp_compute_failed ->
        eprintf "%aCode generation : Computation of the value of the static \
                 expression failed.@."
          print_location loc
    | Eunknown_method s ->
        eprintf "%aCode generation : Methods other than step and \
                    reset are not supported (found '%s').@."
          print_location loc
          s);
    raise Errors.Error
end

let struct_name ty =
  match ty with
  | Cty_id n -> n
  | _ -> assert false

let int_of_static_exp se = Static.int_of_static_exp se


let output_names_list sig_info =
  let remove_option ad = match ad.a_name with
    | Some n -> n
    | None -> Error.message (no_location ()) Error.Eno_unnamed_output
  in
  let outputs = List.filter
    (fun ad -> not (Linearity.is_linear ad.a_linearity)) sig_info.node_outputs in
    List.map remove_option outputs

let is_stateful n =
  try
    let sig_info = find_value n in
      sig_info.node_stateful
  with
      Not_found -> Error.message (no_location ()) (Error.Enode (fullname n))

let rec is_lhs_mem l = match l with
  | CLvar "self" -> true
  | CLvar _ -> false
  | CLderef l -> is_lhs_mem l
  | CLfield (l,_) -> is_lhs_mem l
  | CLarray (l,_) -> is_lhs_mem l

(******************************)

(** {2 Translation from Obc to C using our AST.} *)

(** [ctype_of_type mods oty] translates the Obc type [oty] to a C
    type. We assume that identified types have already been defined
    before use. [mods] is an accumulator for modules to be opened for
    each function (i.e., not opened by an "open" declaration).
    We have to make a difference between function args and local vars
    because of arrays (when used as args, we use a pointer).
*)
let rec ctype_of_otype oty =
  match oty with
    | Signature.Tid id when id = Initial.pint -> Cty_int
    | Signature.Tid id when id = Initial.pfloat -> Cty_float
    | Signature.Tid id when id = Initial.pbool -> Cty_int
    | Tid id -> Cty_id id
    | Tarray(ty, n) -> Cty_arr(int_of_static_exp n, ctype_of_otype ty)
    | Tprod _ -> assert false
    | Tinvalid -> assert false
    | Tfuture ((),ty) -> Cty_future (ctype_of_otype ty)
    | Tbounded _ -> Cty_int

let copname = function
  | "="  -> "==" | "<>" -> "!=" | "&"  -> "&&" | "or" -> "||" | "+" -> "+"
  | "-" -> "-" | "*" -> "*" | "/" -> "/" | "*." -> "*" | "/." -> "/"
  | "+." -> "+" | "-." -> "-" | "<"  -> "<" | ">"  -> ">" | "<=" -> "<="
  | ">=" -> ">=" | "<=." -> "<=" | "<." -> "<" | ">=." -> ">=" | ">." -> ">"
  | "~-" -> "-" | "not" -> "!" | "%" -> "%"
  | ">>>" -> ">>" | "<<<" -> "<<" | "&&&" -> "&" | "|||" -> "|"
  | op   -> op


let cformat_of_format s =
  let aux m = match m with
    | "b" -> "d" (*no booleans in C*)
    | _ -> m
  in
  match s with
    | Cconst (Cstrlit s) -> Cconst (Cstrlit (Printf_parser.tr_format aux s))
    | _ -> assert false

(** Translates an Obc var_dec to a tuple (name, cty). *)
let cvar_of_vd vd =
  name vd.v_ident,
  ctype_of_otype vd.v_type

(** Returns the type of a pointer to a type, except for
    types which are already pointers. *)
let pointer_type ty =
  match Modules.unalias_type ty with
    | Tarray _ -> ctype_of_otype ty
    | Tfuture _ -> ctype_of_otype ty
    | _ -> Cty_ptr (ctype_of_otype ty)

(** Returns the expression to use e as an argument of
    a function expecting a pointer as argument. *)
let address_of ty e =
  match Modules.unalias_type ty with
    | Tarray _ -> e
    | Tfuture _ -> e
    | _ -> Caddrof e


let inputlist_of_ovarlist vl =
  let cvar_of_ovar vd =
    let ty = ctype_of_otype vd.v_type in
    let ty = if vd.v_mutable then pointer_type vd.v_type else ty in
    name vd.v_ident, ty
  in
  List.map cvar_of_ovar vl

(** @return the unaliased version of a type. *)
let rec unalias_ctype cty = match cty with
  | Cty_id ty_name ->
    (try match find_type ty_name with
    | Type_alias ty -> unalias_ctype (ctype_of_otype ty)
    | _ -> Cty_id ty_name
     with Not_found -> Cty_id ty_name)
  | Cty_arr (n, cty) -> Cty_arr (n, unalias_ctype cty)
  | Cty_ptr cty -> Cty_ptr (unalias_ctype cty)
  | cty -> cty

(** Returns the type associated with the name [n]
    in the environnement [var_env] (which is an association list
    mapping strings to cty). *)
and assoc_type n var_env =
  try unalias_ctype (List.assoc n var_env)
  with Not_found -> Error.message (no_location ()) (Error.Evar n)


module Stock = struct
  include (Map.Make(struct type t = cty let compare = compare end))
  let add_stock cty x stock =
    let cty = unalias_ctype cty in
    let old_x =
      try find cty stock
      with Not_found -> Int32.zero
    in
    add cty (Int32.add old_x x) stock
  let name_stock =
    Misc.memoize
      (fun cty ->
        let t = sanitize_string (print_pp_to_string pp_cty cty) in
        Idents.local_qn ("__stock_"^t)
      )
  let stock_of cty =
    Cfield(Cderef (Cvar "self"), name_stock cty)
  let stock_method_call cty m args =
    Cmethod (stock_of cty, m, args)
end

let current_stock = ref Stock.empty
let init_stock () = current_stock := Stock.empty
let add_stock cty x =
  current_stock := Stock.add_stock cty x !current_stock
let get_free_future cty =
  Stock.stock_method_call cty "get_free" []
let reset_store cty mem v =
  Stock.stock_method_call cty "reset_store" [Clhs mem; v]
let store_in cty v mem =
  Stock.stock_method_call cty "store_in" [v; Clhs mem]
let add_stores_tick acc =
  Stock.fold
    (fun cty _ acc -> (Csexpr (Stock.stock_method_call cty "tick" []))::acc)
    !current_stock
    acc
let stores_def acc =
  Stock.fold
    (fun cty n acc ->
      ((cname_of_qn (Stock.name_stock cty), Cty_stock (cty,n)))::acc)
    !current_stock
    acc

(** Returns the type associated with the lhs [lhs]
    in the environnement [var_env] (which is an association list
    mapping strings to cty).*)
let rec assoc_type_lhs lhs var_env = match lhs with
  | CLvar x -> unalias_ctype (assoc_type x var_env)
  | CLarray (lhs, _) ->
    let ty = assoc_type_lhs lhs var_env in
    array_base_ctype ty [1]
  | CLderef lhs ->
    (match assoc_type_lhs lhs var_env with
    | Cty_ptr ty -> ty
    | _ -> Error.message (no_location ()) Error.Ederef_not_pointer)
  | CLfield(CLderef (CLvar "self"), { name = x }) -> assoc_type x var_env
  | CLfield(CLderef (CLvar "_out"), { name = x }) -> assoc_type x var_env
  | CLfield(x, f) ->
    let ty = assoc_type_lhs x var_env in
    let n = struct_name ty in
    let fields = find_struct n in
    ctype_of_otype (field_assoc f fields)

(** Creates the statement a = [e_1, e_2, ..], which gives a list
    a[i] = e_i.*)
let rec create_affect_lit dest l ty =
  let rec _create_affect_lit dest i = function
    | [] -> []
    | v::l ->
        let stm = create_affect_stm (CLarray (dest, Cconst (Ccint i))) v ty in
        stm@(_create_affect_lit dest (Int32.succ i) l)
  in
  _create_affect_lit dest 0l l

(** Creates the expression dest <- src (copying arrays if necessary). *)
and create_affect_stm dest src ty =
  match ty with
    | Cty_arr (n, bty) ->
        (match src with
           | Carraylit (_,l) -> create_affect_lit dest l bty
           | src ->
             let x = gen_symbol () in
             [Cfor(x,
                   Cconst (Ccint 0l), Cconst (Ccint n),
                   create_affect_stm
                     (CLarray (dest, Cvar x))
                     (Carray (src, Cvar x)) bty)]
        )
    | Cty_id ln ->
        (match src with
          | Cstructlit (_, ce_list) ->
              let create_affect { f_name = f_name;
                                  Signature.f_type = f_type; } e stm_list =
                let cty = ctype_of_otype f_type in
                create_affect_stm (CLfield (dest, f_name)) e cty @ stm_list in
              List.fold_right2 create_affect (find_struct ln) ce_list []
          | _ -> [Caffect (dest, src)])
    | Cty_future t when is_lhs_mem dest ->
        [Csexpr (store_in t src dest)]
    | _ ->
        [Caffect (dest, src)]

let string_of_static_exp se =
  Name_utils.print_pp_to_name Global_printer.print_static_exp se

let cconst_of_static_exp se =
  match (Static.simplify se).se_desc with
    | Sint i -> Ccint i
    | Sfloat f -> Ccfloat f
    | Sbool b -> Ctag (if b then "true" else "false")
    | Sstring s -> Cstrlit s
    | Sconstructor c -> Ctag (cname_of_qn c)
    | _ -> Error.message se.se_loc Error.Estatic_exp_compute_failed


let rec cexpr_of_static_exp se =
  match (Static.simplify se).se_desc with
    | Sint i -> Cconst (Ccint i)
    | Sfloat f -> Cconst (Ccfloat f)
    | Sbool b -> Cconst (Ctag (if b then "true" else "false"))
    | Sstring s -> Cconst (Cstrlit s)
    | Sconstructor c -> Cconst (Ctag (cname_of_qn c))
    | Sarray sl -> Carraylit (ctype_of_otype se.se_ty, List.map cexpr_of_static_exp sl)
    | Srecord fl ->
       (* let ty_name =
          match Modules.unalias_type se.se_ty with
            | Signature.Tid n -> cname_of_qn n
            | _ -> assert false
        in*)
          Cstructlit (ctype_of_otype se.se_ty,
                     List.map (fun (_, se) -> cexpr_of_static_exp se) fl)
    | Sarray_power(c,n_list) ->
          (List.fold_left (fun cc n -> Carraylit (ctype_of_otype se.se_ty, repeat_list cc (Int32.to_int (int_of_static_exp n))))
                     (cexpr_of_static_exp c) n_list)
    | Svar ln ->
        if !Compiler_options.unroll_loops && se.se_ty = Initial.tint
        then cexpr_of_static_exp (Static.simplify (find_const ln).c_value)
        else Cvar (cname_of_qn ln)
    | Sfun _
    | Sop _ -> Error.message se.se_loc Error.Estatic_exp_compute_failed
    | Sfield _ -> Misc.internal_error "cgen: sfield found"
    | Stuple _ -> Misc.internal_error "cgen: static tuple found"
    | Sasync s ->
        let cs = cexpr_of_static_exp s in
        let cty = ctype_of_otype s.se_ty in
        add_stock cty Int32.one;
        let future = get_free_future cty in
        Cmethod(Cderef future, "set2", [cs])

(** [cexpr_of_exp exp] translates the Obj action [exp] to a C expression. *)
let rec cexpr_of_exp out_env var_env exp =
  match exp.e_desc with
    | Eextvalue w  -> cexpr_of_ext_value out_env var_env w
    (** Operators *)
    | Eop(op, exps) -> cop_of_op out_env var_env op exps
    (** Structure literals. *)
    | Estruct fl ->
        let cexps = List.map (fun (_,e) -> cexpr_of_exp out_env var_env e) fl in
        Cstructlit (ctype_of_otype exp.e_ty, cexps)
    | Earray e_list ->
        Carraylit (ctype_of_otype exp.e_ty, cexprs_of_exps out_env var_env e_list)
    | Ebang e ->
        Cmethod(Cderef (cexpr_of_exp out_env var_env e), "get", [])

and cexprs_of_exps out_env var_env exps =
  List.map (cexpr_of_exp out_env var_env) exps

and cop_of_op_aux op_name cexps = match op_name with
    | { qual = Pervasives; name = op } ->
        begin match op,cexps with
          | ("~-" | "~-."), [e] -> Cuop ("-", e)
          | ("~~"), [e] -> Cuop ("~", e)
          | "not", [e] -> Cuop ("!", e)
          | (
              "=" | "<>"
            | "&" | "or"
            | "+" | "-" | "*" | "/"
            | "*." | "/." | "+." | "-." | "%" | "<<<" | ">>>" | "&&&" | "|||"
            | "<" | ">" | "<=" | ">=" | "<=." | "<." | ">=." | ">."), [el;er] ->
              Cbop (copname op, el, er)
          | _ -> Cfun_call(op, cexps)
        end
    | { qual = Module "Iostream"; name = "printf" } ->
      let s, args = assert_1min cexps in
      let s = cformat_of_format s in
      Cfun_call("printf", s::args)
    | { qual = Module "Iostream"; name = "fprintf" } ->
      let file, s, args = assert_2min cexps in
      let s = cformat_of_format s in
      Cfun_call("fprintf", file::s::args)
    | { name = op } -> Cfun_call(op,cexps)

and cop_of_op out_env var_env op_name exps =
  let cexps = cexprs_of_exps out_env var_env exps in
  cop_of_op_aux op_name cexps

and clhs_of_pattern out_env var_env l = match l.pat_desc with
  (** Each Obc variable corresponds to a real local C variable. *)
  | Lvar v ->
      let n = name v in
      let n_lhs =
        if IdentSet.mem v out_env
        then CLfield (CLderef (CLvar "_out"), local_qn n)
        else CLvar n
      in

      if List.mem_assoc n var_env then
        let ty = assoc_type n var_env in
        (match ty with
           | Cty_ptr _ -> CLderef n_lhs
           | _ -> n_lhs
        )
      else
        n_lhs
  (** Dereference our [self] struct holding the node's memory. *)
  | Lmem v -> CLfield (CLderef (CLvar "self"), local_qn (name v))
  (** Field access. /!\ Indexed Obj expression should be a valid lhs!  *)
  | Lfield (l, fn) -> CLfield(clhs_of_pattern out_env var_env l, fn)
  | Larray (l, idx) ->
      CLarray(clhs_of_pattern out_env var_env l,
              cexpr_of_exp out_env var_env idx)

and clhs_list_of_pattern_list out_env var_env lhss =
  List.map (clhs_of_pattern out_env var_env) lhss

and cexpr_of_pattern out_env var_env l = match l.pat_desc with
  (** Each Obc variable corresponds to a real local C variable. *)
  | Lvar v ->
      let n = name v in
      let n_lhs =
        if IdentSet.mem v out_env
        then Cfield (Cderef (Cvar "_out"), local_qn n)
        else Cvar n
      in

      if List.mem_assoc n var_env then
        let ty = assoc_type n var_env in
        (match ty with
           | Cty_ptr _ -> Cderef n_lhs
           | _ -> n_lhs
        )
      else
        n_lhs
  (** Dereference our [self] struct holding the node's memory. *)
  | Lmem v -> Cfield (Cderef (Cvar "self"), local_qn (name v))
  (** Field access. /!\ Indexed Obj expression should be a valid lhs!  *)
  | Lfield (l, fn) -> Cfield(cexpr_of_pattern out_env var_env l, fn)
  | Larray (l, idx) ->
      Carray(cexpr_of_pattern out_env var_env l,
             cexpr_of_exp out_env var_env idx)

and cexpr_of_ext_value out_env var_env w = match w.w_desc with
  | Wconst c -> cexpr_of_static_exp c
  (** Each Obc variable corresponds to a plain local C variable. *)
  | Wvar v ->
    let n = name v in
    let n_lhs =
      if IdentSet.mem v out_env
      then Cfield (Cderef (Cvar "_out"), local_qn n)
      else Cvar n
    in

    if List.mem_assoc n var_env then
      let ty = assoc_type n var_env in
      (match ty with
      | Cty_ptr _ -> Cderef n_lhs
      | _ -> n_lhs)
    else
      n_lhs
  (** Dereference our [self] struct holding the node's memory. *)
  | Wmem v -> Cfield (Cderef (Cvar "self"), local_qn (name v))
  (** Field access. /!\ Indexed Obj expression should be a valid lhs!  *)
  | Wfield (l, fn) -> Cfield(cexpr_of_ext_value out_env var_env l, fn)
  | Warray (l, idx) ->
    Carray(cexpr_of_ext_value out_env var_env l,
           cexpr_of_exp out_env var_env idx)
  | Wbang l ->
      Cmethod(Cderef (cexpr_of_ext_value out_env var_env l), "get", [])

let rec assoc_obj instance obj_env =
  match obj_env with
    | [] -> raise Not_found
    | od :: t ->
        if od.o_ident = instance
        then od
        else assoc_obj instance t

let assoc_cn instance obj_env =
  (assoc_obj (obj_ref_name instance) obj_env).o_class

let is_op = function
  | { qual = Pervasives; name = _ } -> true
  | { qual = Module "Iostream"; name = "printf" } -> true
  | { qual = Module "Iostream"; name = "fprintf" } -> true
  | _ -> false

let out_var_name_of_objn o =
   o ^"_out_st"

(** Creates the list of arguments to call a node. [targeting] is the targeting
    of the called node, [mem] represents the node context and [args] the
    argument list.*)
let step_fun_call out_env var_env sig_info objn out args =
  let rec add_targeting l ads = match l, ads with
    | [], [] -> []
    | e::l, ad::ads ->
        (*this arg is targeted, use a pointer*)
        let e =
          if Linearity.is_linear ad.a_linearity
          then address_of ad.a_type e
          else e
        in
        e::(add_targeting l ads)
    | _, _ -> assert false
  in
  let args = (add_targeting args sig_info.node_inputs) in
  let amem =
    if sig_info.node_stateful
    then (
      let mem = match objn with
      | Oobj o -> Cfield (Cderef (Cvar "self"), local_qn (name o))
      | Oarray (o, l) ->
         let f = Cfield (Cderef (Cvar "self"), local_qn (name o)) in
         let rec mk_idx pl = match pl with
         | [] -> f
         | p::pl -> Carray (mk_idx pl, cexpr_of_pattern out_env var_env p)
         in
         mk_idx l
      in
      [Caddrof mem] )
    else []
  in
  match out with
  | None -> args@amem
  | Some out -> args@(out::amem)

(** Generate the statement to call [objn].
    [outvl] is a list of lhs where to put the results.
    [args] is the list of expressions to use as arguments.
    [mem] is the lhs where is stored the node's context.*)
let generate_function_call async out_env var_env obj_env outvl objn args =
  (** Class name for the object to step. *)
  let classln = assoc_cn objn obj_env in
  let classn = cname_of_qn classln in
  let sig_info = find_value classln in
  let is_async = not (async = None) in

  let fun_call out =
    if is_op classln then
      cop_of_op_aux classln args
    else
      (** The step function takes scalar arguments and its own internal memory
          holding structure. *)
      let args = step_fun_call out_env var_env sig_info objn out args in
      let step = if is_async then "_Astep" else "_step" in
      Cfun_call (classn ^ step, args)
  in

  (** Act according to the length of our list. Step functions with
      multiple return values will return a structure, and we care of
      assigning each field to the corresponding local variable. *)
  match outvl with
    | [] -> [Csexpr (fun_call None)]
    | [outv] when is_op classln ->
        let ty = assoc_type_lhs outv var_env in
        create_affect_stm outv (fun_call None) ty
    | [outv] ->
        let ty = assoc_type_lhs outv var_env in
        let (e,t) = match ty with
        | Cty_arr _ -> Clhs outv, None
        | Cty_future t -> Clhs outv, Some t
        | _ -> Caddrof (Clhs outv), None
        in
        let step_call = Csexpr (fun_call (Some e)) in
        if is_async
        then
          match t with
          | Some t -> [Caffect (outv, get_free_future t);step_call]
          | _ -> Misc.internal_error "Async call should have future return type"
        else
          [step_call]
    | _ ->
        if is_async then
          Misc.unsupported "C backend allows only async of node \
            returning one value";
        (* Remove options *)
        let out = Cvar (out_var_name_of_objn classn) in
        let out_sig = output_names_list sig_info in
        let create_affect outv out_name =
          let ty = assoc_type_lhs outv var_env in
          create_affect_stm outv (Cfield (out, local_qn out_name)) ty
        in
        (Csexpr (fun_call (Some (Caddrof out))))
        ::(List.flatten (map2 create_affect outvl out_sig))

(** Create the statement dest = c where c = v^n^m... *)
let rec create_affect_const var_env (dest : clhs) c =
  match c.se_desc with
    | Svar ln ->
        let se = Static.simplify (find_const ln).c_value in
        create_affect_const var_env dest se
    | Sarray_power(c, n_list) ->
        let rec make_loop power_list replace = match power_list with
        | [] -> dest, replace
        | p :: power_list ->
          let x = gen_symbol () in
          let e, replace =
            make_loop power_list
              (fun y ->
                [Cfor(x, Cconst (Ccint 0l), cexpr_of_static_exp p, replace y)])
          in
          let e =  (CLarray (e, Cvar x)) in
          e, replace
        in
        let e, b = make_loop n_list (fun y -> y) in
        b (create_affect_const var_env e c)
    | Sarray cl ->
        let create_affect_idx c (i, affl) =
          let dest = CLarray (dest, Cconst (Ccint i)) in
            (Int32.pred i, create_affect_const var_env dest c @ affl)
        in
          snd (List.fold_right create_affect_idx cl (Int32.of_int (List.length cl - 1), []))
    | Srecord f_se_list ->
        let affect_field affl (f, se) =
          let dest_f = CLfield (dest, f) in
            (create_affect_const var_env dest_f se) @ affl
        in
          List.fold_left affect_field [] f_se_list
    | Sasync s when is_lhs_mem dest ->
        let cs = cexpr_of_static_exp s in
        let cty = ctype_of_otype s.se_ty in
        [Csexpr (reset_store cty dest cs)]
    | _ ->
        [Caffect (dest, cexpr_of_static_exp c)]

(** [cstm_of_act obj_env mods act] translates the Obj action [act] to a list of
    C statements, using the association list [obj_env] to map object names to
    class names.  *)
let rec cstm_of_act out_env var_env obj_env act =
  match act with
    (** Translation of case into a C switch statement is simple enough: we
        just recursively translate obj expressions and statements to
        corresponding C constructs, and cautiously "shortnamize"
        constructor names. *)
    | Acase (e, cl) ->
        (** [ccl_of_obccl] translates an Obc clause to a C clause. *)
        let cc = cexpr_of_exp out_env var_env e in
        let ccl =
          List.map (fun (c,act) -> cconst_of_static_exp c,
                      cstm_of_act_list out_env var_env obj_env act) cl
        in
        (match ccl with (** Cosmetic : convert to if statements. *)
        | [Ctag "true", cte; Ctag "false", cfe]
        | [Ctag "false", cfe; Ctag "true", cte] ->
            [Cif (cc, cfe, cte)]
        | [Ctag "true", cte] ->
          let cfe = [] in
            [Cif (cc, cte, cfe)]
        | [Ctag "false", cfe] ->
          let cc = Cuop ("!", cc) in
          let cte = [] in
            [Cif (cc, cte, cfe)]
        | _ ->
            [Cswitch (cc, ccl)])
    | Ablock b ->
        cstm_of_act_list out_env var_env obj_env b

    (** For composition of statements, just recursively apply our
        translation function on sub-statements. *)
    | Afor ({ v_ident = x }, i1, i2, act) ->
        [Cfor(name x, cexpr_of_exp out_env var_env i1,
              cexpr_of_exp out_env var_env i2,
              cstm_of_act_list out_env var_env obj_env act)]

    | Awhile (o, e, act) ->
        [Cwhile (o, cexpr_of_exp out_env var_env e,
                 cstm_of_act_list out_env var_env obj_env act)]

    (** Translate constant assignment *)
    | Aassgn (vn, { e_desc = Eextvalue { w_desc = Wconst c }; }) ->
        let vn = clhs_of_pattern out_env var_env vn in
        create_affect_const var_env vn c

    (** Purely syntactic translation from an Obc local variable to a C
        local one, with recursive translation of the rhs expression. *)
    | Aassgn (vn, e) ->
        let vn = clhs_of_pattern out_env var_env vn in
        let ty = assoc_type_lhs vn var_env in
        let ce = cexpr_of_exp out_env var_env e in
        create_affect_stm vn ce ty

    (** Our Aop marks an operator invocation that will perform side effects. Just
        translate to a simple C statement. *)
    | Acall_fun (p, op_name, args) ->
        let call = cop_of_op out_env var_env op_name args in
        begin match p with
          | [] -> [Csexpr call]
          | [vn] ->
              let vn = clhs_of_pattern out_env var_env vn in
              [Caffect(vn, call)]
          | _ -> assert false
        end

    (** Reinitialization of an object variable, extracting the reset
        function's name from our environment [obj_env]. *)
    | Acall (_, name_list, o, Mreset, args) ->
        assert_empty name_list;
        assert_empty args;
        let on = obj_ref_name o in
        let obj = assoc_obj on obj_env in
        let classn = cname_of_qn obj.o_class in
        let field = Cfield (Cderef (Cvar "self"), local_qn (name on)) in
        let reset = if obj.o_async = None then "_reset" else "_Areset" in
        (match o with
          | Oobj _ ->
              [Csexpr (Cfun_call (classn ^ reset, [Caddrof field]))]
          | Oarray (_, pl) ->
              let rec mk_loop pl field = match pl with
              | [] ->
                  [Csexpr (Cfun_call (classn ^ reset, [Caddrof field]))]
              | p::pl ->
                  mk_loop pl (Carray(field, cexpr_of_pattern out_env var_env p))
              in
              mk_loop pl field
        )
    (** Step functions applications can return multiple values, so we use a
        local structure to hold the results, before allocating to our
        variables. *)
    | Acall (async, outvl, objn, Mstep, el) ->
        let args = cexprs_of_exps out_env var_env el in
        let outvl = clhs_list_of_pattern_list out_env var_env outvl in
        generate_function_call async out_env var_env obj_env outvl objn args


and cstm_of_act_list out_env var_env obj_env b =
  let l = List.map cvar_of_vd b.b_locals in
  let var_env = l @ var_env in
  let cstm = List.flatten (List.map (cstm_of_act out_env var_env obj_env) b.b_body) in
    match l with
      | [] -> cstm
      | _ ->
            [Csblock { var_decls = l; block_body = cstm }]

(* TODO needed only because of renaming phase *)
let global_name = ref "";;



(** {2 step() and reset() functions generation *)

let qn_append q suffix =
  { qual = q.qual; name = q.name ^ suffix }

(** Builds the argument list of step function*)
let step_fun_args n md =
  let args = inputlist_of_ovarlist md.m_inputs in
  let out_arg = match md.m_outputs with
  | [] -> []
  | [od] ->
    let n = name od.v_ident in
    let t = pointer_type od.v_type in
    [(n, t)]
  | _ -> [("_out", Cty_ptr (Cty_id (qn_append n "_out")))]
  in
  let context_arg =
    if is_stateful n then
      [("self", Cty_ptr (Cty_id (qn_append n "_mem")))]
    else
      []
  in
    args @ out_arg @ context_arg


(** [fun_def_of_step_fun name obj_env mods sf] returns a C function definition
    [name ^ "_out"] corresponding to the Obc step function [sf]. The object name
    <-> class name mapping [obj_env] is needed to translate internal steps and
    reset calls. A step function can have multiple return values, whereas C does
    not allow such functions. When it is the case, we declare a structure with a
    field by return value. *)
let fun_def_of_step_fun n obj_env mem objs md =
  let fun_name = (cname_of_qn n) ^ "_step" in
  (** Its arguments, translating Obc types to C types and adding our internal
      memory structure. *)
  let args = step_fun_args n md in

  (** Out vars for function calls *)
  let out_vars =
    let add_out_var out_vars obj =
      if is_op obj.o_class
      then out_vars (* no need for output var *)
      else
        let s = Modules.find_value obj.o_class in
        match s.node_outputs with
        | [] -> out_vars
        | _::[] -> out_vars (*
          let t = ctype_of_otype a.a_type in
          let n = out_var_name_of_objn (cname_of_qn obj.o_class) in
          (n,t)::out_vars *)
        | _ ->
          let t = Cty_id (qn_append obj.o_class "_out") in
          let n = out_var_name_of_objn (cname_of_qn obj.o_class) in
          (n,t)::out_vars
    in
    unique (List.fold_left add_out_var [] objs)
  in
  (** The body *)
  let mems = List.map cvar_of_vd (mem@md.m_outputs) in
  let var_env = args @ mems @ out_vars in
  let out_env =
    if List.length md.m_outputs > 1
    then
      List.fold_left
        (fun out_env vd -> IdentSet.add vd.v_ident out_env)
        IdentSet.empty
        md.m_outputs
   else IdentSet.empty
  in
  let body = cstm_of_act_list out_env var_env obj_env md.m_body in
  let body = add_stores_tick body in
  Cfundef {
    f_name = fun_name;
    f_retty = Cty_void;
    f_args = args;
    f_body = {
      var_decls = out_vars;
      block_body = body
    }
  }

(** [mem_decl_of_class_def cd] returns a declaration for a C structure holding
    internal variables and objects of the Obc class definition [cd]. *)
let mem_decls_defs_of_class_def cd =
  if not (is_stateful cd.cd_name)
  then ([],[]),None
  else (
    (** Translate the class name to a struct name following the
      convention we described above. *)
    (* naw stands for needed async wrapper, maps to list of params *)
    let struct_field_of_obj_dec (naw,l) od =
      if not (is_stateful od.o_class)
      then naw, l
      else (
        let naw,ty = match od.o_async with
        | None -> naw, Cty_id (qn_append od.o_class "_mem")
        | Some(params) ->
            let naw =
              let old_param_l =
                try QualEnv.find od.o_class naw
                with Not_found -> []
              in
              QualEnv.add od.o_class (params::old_param_l) naw
            in
            let string_params =
              let open Format in
              fprintf str_formatter "_Amem<@[%a@]>"
                (Pp_tools.print_list_r Global_printer.print_static_exp """,""")
                params;
              flush_str_formatter ()
            in
            naw, Cty_macro (cname_of_qn(qn_append od.o_class string_params))
        in
        let ty = match od.o_size with
          | Some nl ->
            let rec mk_idx nl = match nl with
              | [] -> ty
              | n::nl -> Cty_arr (int_of_static_exp n, mk_idx nl)
            in
              mk_idx nl
          | None -> ty
        in
        naw, ((name od.o_ident, ty)::l)
      )
    in
    (** Fields corresponding to normal memory variables. *)
    let mem_fields = List.map cvar_of_vd cd.cd_mems in
    begin (* Add mems of type future to the stock *)
      let rec cty_walk cty n = match unalias_ctype cty with
      | Cty_arr (size, acty) -> cty_walk acty (Int32.mul size n)
      | Cty_future t -> add_stock t n
      | _ -> () (*TODO futures inside structures are not handeled !*)
      in
      let add_mem_to_stock (_,cty) = cty_walk cty Int32.one in
      List.iter add_mem_to_stock mem_fields
    end;
    (** Fields corresponding to object variables. *)
    let naw, obj_fields =
      List.fold_left struct_field_of_obj_dec (QualEnv.empty,[]) cd.cd_objs
    in
    let thisdecl = Cdecl_struct ((cname_of_qn cd.cd_name) ^ "_mem",
                     mem_fields @ obj_fields)
    in
    let decl_def_of_naw q params_l (decls,defs) =
      let sis_q = Modules.find_value q in
      let out = Misc.assert_1 sis_q.node_outputs in
      let out_ty = ctype_of_otype out.a_type in
      begin (* Add queues to stock *)
        let add_param params =
          let queue_size,_ = Misc.assert_1min params in
          let queue_size = int_of_static_exp queue_size in
          add_stock out_ty (Int32.succ queue_size)
        in
        List.iter add_param params_l
      end;
      let inputs =
        let arg_to_cvar a =
          let ty = ctype_of_otype a.a_type in
          let n = match a.a_name with
          | None -> Idents.name (Idents.gen_var "Cgen" "__unnamed_arg__")
          | Some(n) -> n
          in
          n, ty
        in
        List.map arg_to_cvar sis_q.node_inputs
      in
      let (ins_name, ins_ty) = List.split inputs in
      let open Format in
      (*WRAPPER_MEM_DEC(Simple__f,int,(int,int))*)
      let macro_dec =
        fprintf str_formatter "WRAPPER_MEM_DEC(%a,%a,@[%a@])"
          pp_qualname q
          C.pp_cty out_ty
          (Pp_tools.print_list_r C.pp_cty "("","")") ins_ty
        ;
        flush_str_formatter ()
      in
      (*WRAPPER_FUN_DEFS(Simple__f,int,(int x, int y),(x, y))*)
      let macro_def =
        fprintf str_formatter "WRAPPER_FUN_DEFS(%a,%a,@[%a@],@[%a@])"
          pp_qualname q
          C.pp_cty out_ty
          (Pp_tools.print_list_r C.pp_vardecl "("","")") inputs
          (Pp_tools.print_list_r C.pp_string "("","")") ins_name
        ;
        flush_str_formatter ()
      in
      (Cdecl_macro macro_dec)::decls, (Cdef_macro macro_def)::defs
    in
    let (decls,defs) = QualEnv.fold decl_def_of_naw naw ([],[]) in
    (decls,defs), Some thisdecl
  )

let out_decl_of_class_def cd =
  (** Fields corresponding to output variables. *)
  let step_m = find_step_method cd in
  if (List.length step_m.m_outputs > 1)
  then
    let out_fields = List.map cvar_of_vd step_m.m_outputs in
    [Cdecl_struct ((cname_of_qn cd.cd_name) ^ "_out", out_fields)]
  else
    []

(** [reset_fun_def_of_class_def cd] returns the defintion of the C function
    tasked to reset the class [cd]. *)
let reset_fun_def_of_class_def cd =
  let body =
    if cd.cd_stateful then
      let var_env = List.map cvar_of_vd cd.cd_mems in
      let reset = find_reset_method cd in
      cstm_of_act_list IdentSet.empty var_env cd.cd_objs reset.m_body
    else
      []
  in
  Cfundef {
    f_name = (cname_of_qn cd.cd_name) ^ "_reset";
    f_retty = Cty_void;
    f_args = [("self", Cty_ptr (Cty_id (qn_append cd.cd_name "_mem")))];
    f_body = {
      var_decls = [];
      block_body = body;
    }
  }


(** [cdecl_and_cfun_of_class_def cd] translates the class definition [cd] to
    a C program. *)
let cdefs_and_cdecls_of_class_def cd =
  (** We keep the state of our class in a structure, holding both internal
      variables and the state of other nodes. For a class named ["cname"], the
      structure will be called ["cname_mem"]. *)
  let step_m = find_step_method cd in
  Idents.push_node cd.cd_name;
  init_stock ();
  let (memdecls, memdefs), thisdecl = mem_decls_defs_of_class_def cd in
  let out_struct_decl = out_decl_of_class_def cd in
  let step_fun_def = fun_def_of_step_fun cd.cd_name
    cd.cd_objs cd.cd_mems cd.cd_objs step_m in
  (** C function for resetting our memory structure. *)
  let reset_fun_def = reset_fun_def_of_class_def cd in
  let res_fun_decl = cdecl_of_cfundef reset_fun_def in
  let step_fun_decl = cdecl_of_cfundef step_fun_def in
  let (decls, defs) =
    if is_stateful cd.cd_name then
      ([res_fun_decl; step_fun_decl], [reset_fun_def; step_fun_def])
    else
      ([step_fun_decl], [step_fun_def]) in
  let thisdecl = match thisdecl with
  | Some (Cdecl_struct(name,vars)) ->
    [Cdecl_struct (name, stores_def vars)]
  | _ -> []
  in
  let _ = Idents.pop_node () in
  memdecls @ thisdecl @ out_struct_decl @ decls,
  memdefs @ defs


(** {2 Type translation} *)

(** Translates an Obc type declaration to its C counterpart. *)
let cdefs_and_cdecls_of_type_decl otd =
  let name = cname_of_qn otd.t_name in
  match otd.t_desc with
    | Type_abstract -> [], [] (*assert false*)
    | Type_alias ty ->
      [], [Cdecl_typedef (ctype_of_otype ty, name)]
    | Type_enum nl ->
        let of_string_fun = Cfundef
          { f_name = name ^ "_of_string";
            f_retty = Cty_id otd.t_name;
            f_args = [("s", Cty_ptr Cty_char)];
            f_body =
              { var_decls = [];
                block_body =
                  let gen_if t =
                    let t = cname_of_qn t in
                    let funcall = Cfun_call ("strcmp", [Cvar "s";
                                                        Cconst (Cstrlit t)]) in
                    let cond = Cbop ("==", funcall, Cconst (Ccint 0l)) in
                    Cif (cond, [Creturn (Cconst (Ctag t))], []) in
                  map gen_if nl; }
          }
        and to_string_fun = Cfundef
          { f_name = "string_of_" ^ name;
            f_retty = Cty_ptr Cty_char;
            f_args = [("x", Cty_id otd.t_name); ("buf", Cty_ptr Cty_char)];
            f_body =
              { var_decls = [];
                block_body =
                  let gen_clause t =
                    let t = cname_of_qn t in
                    let fun_call =
                      Cfun_call ("strcpy", [Cvar "buf";
                                            Cconst (Cstrlit t)]) in
                    (Ctag t, [Csexpr fun_call]) in
                  [Cswitch (Cvar "x", map gen_clause nl);
                   Creturn (Cvar "buf")]; }
          } in
        ([of_string_fun; to_string_fun],
         [Cdecl_enum (name, List.map cname_of_qn nl);
          cdecl_of_cfundef of_string_fun;
          cdecl_of_cfundef to_string_fun])
    | Type_struct fl ->
        let decls = List.map (fun f -> cname_of_name f.Signature.f_name.name,
                                ctype_of_otype f.Signature.f_type) fl in
        let decl = Cdecl_struct (name, decls) in
        ([], [decl])

let cdefs_and_cdecls_of_const_decl cd =
  let name = cname_of_qn cd.c_name in
  let v = cexpr_of_static_exp cd.Obc.c_value in
  let cty = ctype_of_otype cd.Obc.c_type in
  [], [Cdecl_constant (name, cty, v)]

let cdefs_and_cdecls_of_interface_decl id = match id with
  | Itypedef td -> cdefs_and_cdecls_of_type_decl td
  | Iconstdef cd -> cdefs_and_cdecls_of_const_decl cd
  | _ -> [], []

let cdefs_and_cdecls_of_program_decl id = match id with
  | Ptype td -> cdefs_and_cdecls_of_type_decl td
  | Pconst cd -> cdefs_and_cdecls_of_const_decl cd
  | _ -> [], []

let header_of_module m = match m with
  | Module "Iostream" -> "stdio"
  | _ -> String.uncapitalize (modul_to_string m)

let global_file_header name prog =
  let dependencies = ModulSet.elements (Obc_utils.Deps.deps_program prog) in
  let dependencies = List.map header_of_module dependencies in

  let classes = program_classes prog in
  let (decls, defs) =
    List.split (List.map cdefs_and_cdecls_of_class_def classes) in
  let decls = List.concat decls
  and defs = List.concat defs in

  let filename_types = name ^ "_types" in
  let cdefs_and_cdecls = List.map cdefs_and_cdecls_of_program_decl prog.p_desc in

  let (cty_defs, cty_decls) = List.split cdefs_and_cdecls in
  let types_h =
    (filename_types ^ ".h",
      Cheader ("stdbool"::"assert"::"pervasives"::"async"::dependencies
              , List.concat cty_decls))
  in
  let types_c = (filename_types ^ ".cpp", Csource (concat cty_defs)) in

  let header =
    (name ^ ".h", Cheader (filename_types :: dependencies, decls))
  and source =
    (name ^ ".cpp", Csource defs) in
  [header; source; types_h; types_c]


let interface_header name i =
  let dependencies = ModulSet.elements (Obc_utils.Deps.deps_interface i) in
  let dependencies = List.map header_of_module dependencies in

  let cdefs_and_cdecls = List.map cdefs_and_cdecls_of_interface_decl i.i_desc in

  let (cty_defs, cty_decls) = List.split cdefs_and_cdecls in
  let types_h = (name ^ ".h",
                 Cheader ("stdbool"::"assert"::"pervasives"::dependencies,
                          List.concat cty_decls)) in
  let types_c = (name ^ ".cpp", Csource (concat cty_defs)) in

  [types_h; types_c]
