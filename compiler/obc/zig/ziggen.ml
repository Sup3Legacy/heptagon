
open List
open Misc
open Names
open Idents
open Obc
open Obc_utils
open Types

open Modules
open Signature
open Zig
open Location
open Format

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
  | Zigty_id n -> n
  | _ -> assert false

let int_of_static_exp se =
  Static.int_of_static_exp QualEnv.empty se


let output_names_list sig_info =
  let remove_option ad = match ad.a_name with
    | Some n -> n
    | None -> Error.message no_location Error.Eno_unnamed_output
  in
  let outputs = List.filter
    (fun ad -> not (Linearity.is_linear ad.a_linearity)) sig_info.node_outputs in
    List.map remove_option outputs

let is_stateful n =
  try
    let sig_info = find_value n in
      sig_info.node_stateful
  with
      Not_found -> Error.message no_location (Error.Enode (fullname n))

(******************************)

(** {2 Translation from Obc to Zig using our AST.} *)

(** [zigtype_of_type mods oty] translates the Obc type [oty] to a Zig
    type. We assume that identified types have already been defined
    before use. [mods] is an accumulator for modules to be opened for
    each function (i.e., not opened by an "open" declaration).
    We have to make a difference between function args and local vars
    because of arrays (when used as args, we use a pointer).
*)
let rec zigtype_of_otype oty =
  match oty with
    | Types.Tid id when id = Initial.pint -> Zigty_int
    | Types.Tid id when id = Initial.pfloat -> Zigty_float
    | Types.Tid id when id = Initial.pbool -> Zigty_int
    | Tid id -> Zigty_id id
    | Tarray(ty, n) -> Zigty_arr(int_of_static_exp n, zigtype_of_otype ty)
    | Tprod _ -> assert false
    | Tinvalid -> assert false

let (has_native_zig_op, native_zig_op_of) =
  let assl =
    [
      (["~-"; "~-."], "-");
      (["~~"], "~");
      (["not"], "!");

      (["="], "==");
      (["<>"], "!=");
      (["&"], "&&");
      (["or"], "||");
      (["xor"], "^");

      (["+"; "+."], "+");
      (["-"; "-."], "-");
      (["*"; "*."], "*");
      (["/"; "/."], "/");
      (["%"], "%");

      (["<"; "<."], "<");
      (["<="; "<=."], "<=");
      ([">"; ">."], ">");
      ([">="; ">=."], ">=");

      ([">>>"], ">>");
      (["<<<"], "<<");
      (["&&&"], "&");
      (["|||"], "|");
    ]
  in
  let ht = Hashtbl.create (List.length assl) in
  List.iter (fun (xl, y) -> List.iter (fun x -> Hashtbl.add ht x y) xl) assl;
  Hashtbl.mem ht, Hashtbl.find ht

let zigformat_of_format s =
  let aux m = match m with
    | "b" -> "b" (*no booleans in Zig*)
    | _ -> m
  in
  match s with
    | Zigconst (Zigstrlit s) -> Zigconst (Zigstrlit (Printf_parser.tr_format aux s))
    | _ -> assert false

(** Translates an Obc var_dec to a tuple (name, cty). *)
let zigvar_of_vd vd =
  name vd.v_ident, zigtype_of_otype vd.v_type

(** Returns the type of a pointer to a type, except for
    types which are already pointers. *)
let pointer_type ty zigty =
  match Modules.unalias_type ty with
    | Tarray _ -> zigty
    | _ -> Zigty_ptr zigty

(** Returns the expression to use e as an argument of
    a function expecting a pointer as argument. *)
let address_of ty e =
  match Modules.unalias_type ty with
    | Tarray _ -> e
    | _ -> Zigaddrof e

let inputlist_of_ovarlist vl =
  let zigvar_of_ovar vd =
    let ty = zigtype_of_otype vd.v_type in
    let ty = if vd.v_mutable then pointer_type vd.v_type ty else ty in
    name vd.v_ident, ty
  in
  List.map zigvar_of_ovar vl

(** @return the unaliased version of a type. *)
let rec unalias_zigtype zigty = match zigty with
  | Zigty_id ty_name ->
    (try match find_type ty_name with
    | Talias ty -> unalias_zigtype (zigtype_of_otype ty)
    | _ -> Zigty_id ty_name
     with Not_found -> Zigty_id ty_name)
  | Zigty_arr (n, zigty) -> Zigty_arr (n, unalias_zigtype zigty)
  | Zigty_ptr zigty -> Zigty_ptr (unalias_zigtype zigty)
  | zigty -> zigty

(** Returns the type associated with the name [n]
    in the environnement [var_env] (which is an association list
    mapping strings to cty). *)
and assoc_type n var_env =
  try unalias_zigtype (List.assoc n var_env)
  with Not_found -> Error.message no_location (Error.Evar n)

(** Returns the type associated with the lhs [lhs]
    in the environnement [var_env] (which is an association list
    mapping strings to cty).*)
let rec assoc_type_lhs lhs var_env = match lhs with
  | ZigLvar x -> unalias_zigtype (assoc_type x var_env)
  | ZigLarray (lhs, _) ->
    let ty = assoc_type_lhs lhs var_env in
    array_base_zigtype ty [1]
  | ZigLderef lhs ->
    (match assoc_type_lhs lhs var_env with
    | Zigty_ptr ty -> ty
    | _ -> Error.message no_location Error.Ederef_not_pointer)
  | ZigLfield(ZigLderef (ZigLvar "self"), { name = x }) -> assoc_type x var_env
  | ZigLfield(ZigLderef (ZigLvar "_out"), { name = x }) -> assoc_type x var_env
  | ZigLfield(x, f) ->
    let ty = assoc_type_lhs x var_env in
    let n = struct_name ty in
    let fields = find_struct n in
    zigtype_of_otype (field_assoc f fields)

(** Creates the statement a = [e_1, e_2, ..], which gives a list
    a[i] = e_i.*)
let rec create_affect_lit dest l ty =
  let rec _create_affect_lit dest i = function
    | [] -> []
    | v::l ->
        let stm = create_affect_stm (ZigLarray (dest, Zigconst (Zigint i))) v ty in
        stm@(_create_affect_lit dest (i+1) l)
  in
  _create_affect_lit dest 0 l

(** Creates the expression dest <- src (copying arrays if necessary). *)
and create_affect_stm dest src ty =
  match unalias_zigtype ty with
    | Zigty_arr (n, bty) ->
        (match src with
           | Zigarraylit l -> create_affect_lit dest l bty
           | src ->
             let x = gen_symbol () in
             [Zigfor(x,
                   Zigconst (Zigint 0), Zigconst (Zigint n),
                   create_affect_stm
                     (ZigLarray (dest, Zigvar x))
                     (Zigarray (src, Zigvar x)) bty)]
        )
    | Zigty_id ln ->
        (match src with
          | Zigstructlit (_, ce_list) ->
              let create_affect { Signature.f_name = f_name;
                                  Signature.f_type = f_type; } e stm_list =
                let cty = zigtype_of_otype f_type in
                create_affect_stm (ZigLfield (dest, f_name)) e cty @ stm_list in
              List.fold_right2 create_affect (find_struct ln) ce_list []
          | _ -> [Zigaffect (dest, src)])
    | _ -> [Zigaffect (dest, src)]

let rec zigexpr_of_static_exp se =
  match se.se_desc with
    | Sint i -> Zigconst (Zigint i)
    | Sfloat f -> Zigconst (Zigfloat f)
    | Sbool b -> Zigconst (Zigtag (if b then "true" else "false"))
    | Sstring s -> Zigconst (Zigstrlit s)
    | Sfield _ -> assert false
    | Sconstructor c -> Zigconst (Zigtag (zigname_of_qn c))
    | Sarray sl -> Zigarraylit (List.map zigexpr_of_static_exp sl)
    | Srecord fl ->
        let ty_name =
          match Modules.unalias_type se.se_ty with
            | Types.Tid n -> n
            | _ -> assert false
        in
        let cexps_assoc = List.rev_map (fun (f, e) -> f, zigexpr_of_static_exp e) fl in
        zigexpr_of_struct ty_name cexps_assoc
    | Sarray_power(c,n_list) ->
          (List.fold_left (fun cc n -> Zigarraylit (repeat_list cc (int_of_static_exp n)))
                     (zigexpr_of_static_exp c) n_list)
    | Svar ln ->
      if !Compiler_options.unroll_loops && se.se_ty = Initial.tint
      then zigexpr_of_static_exp
        (Static.simplify QualEnv.empty (find_const ln).Signature.c_value)
      else Zigvar (zigname_of_qn ln)
    | Sop _ ->
        let se' = Static.simplify QualEnv.empty se in
          if se = se' then
            Error.message se.se_loc Error.Estatic_exp_compute_failed
          else
            zigexpr_of_static_exp se'
    | Stuple _ -> Misc.internal_error "cgen: static tuple"

(** [zigexpr_of_exp exp] translates the Obj action [exp] to a Zig expression. *)
and zigexpr_of_exp out_env var_env exp =
  match exp.e_desc with
    | Eextvalue w  -> zigexpr_of_ext_value out_env var_env w
    (* Operators *)
    | Eop(op, exps) -> cop_of_op out_env var_env op exps
    (* Structure literals. *)
    | Estruct (tyn, fl) ->
        let zigexpr = zigexpr_of_exp out_env var_env in
        let cexps_assoc = List.rev_map (fun (f, e) -> f, zigexpr e) fl in
        zigexpr_of_struct tyn cexps_assoc
    | Earray e_list ->
        Zigarraylit (zigexprs_of_exps out_env var_env e_list)

and zigexpr_of_struct tyn cexps_assoc =
  let cexps = List.fold_left
    (fun cexps { Signature.f_name = f } -> List.assoc f cexps_assoc :: cexps)
    [] (find_struct tyn) in
  (* Reverse `cexps' here because of the previous use of `List.fold_left'. *)
  Zigstructlit (zigname_of_qn tyn, List.rev cexps)

and zigexprs_of_exps out_env var_env exps =
  List.map (zigexpr_of_exp out_env var_env) exps

and cop_of_op_aux op_name cexps = match op_name with
    | { qual = Pervasives; name = op } ->
        begin match op,cexps with
          | "=>", [el;er] ->
             Zigbop ("||", (Ziguop("!",el)), er)
          | uop, [e] when has_native_zig_op op ->
             Ziguop (native_zig_op_of uop, e)
          | bop, [el;er] when has_native_zig_op op ->
             Zigbop (native_zig_op_of bop, el, er)
          | _ ->
             Zigfun_call (op, cexps)
        end
    | { qual = Module "Iostream"; name = "printf" } ->
      let s, args = assert_1min cexps in
      let s = zigformat_of_format s in
      Zigfun_call("printf", s::args)
    | { qual = Module "Iostream"; name = "fprintf" } ->
      let file, s, args = assert_2min cexps in
      let s = zigformat_of_format s in
      Zigfun_call("fprintf", file::s::args)
    | { name = op } -> Zigfun_call(op,cexps)

and cop_of_op out_env var_env op_name exps =
  let cexps = zigexprs_of_exps out_env var_env exps in
  cop_of_op_aux op_name cexps

and ziglhs_of_pattern out_env var_env l = match l.pat_desc with
  (* Each Obc variable corresponds to a real local Zig variable. *)
  | Lvar v ->
      let n = name v in
      let n_lhs =
        if IdentSet.mem v out_env
        then ZigLfield (ZigLderef (ZigLvar "_out"), local_qn n)
        else ZigLvar n
      in

      if List.mem_assoc n var_env then
        let ty = assoc_type n var_env in
        (match ty with
           | Zigty_ptr _ -> ZigLderef n_lhs
           | _ -> n_lhs
        )
      else
        n_lhs
  (* Dereference our [self] struct holding the node's memory. *)
  | Lmem v -> ZigLfield (ZigLderef (ZigLvar "self"), local_qn (name v))
  (* Field access. /!\ Indexed Obj expression should be a valid lhs!  *)
  | Lfield (l, fn) -> ZigLfield(ziglhs_of_pattern out_env var_env l, fn)
  | Larray (l, idx) ->
      ZigLarray(ziglhs_of_pattern out_env var_env l,
              zigexpr_of_exp out_env var_env idx)

and ziglhs_list_of_pattern_list out_env var_env lhss =
  List.map (ziglhs_of_pattern out_env var_env) lhss

and zigexpr_of_pattern out_env var_env l = match l.pat_desc with
  (* Each Obc variable corresponds to a real local Zig variable. *)
  | Lvar v ->
      let n = name v in
      let n_lhs =
        if IdentSet.mem v out_env
        then Zigfield (Zigderef (Zigvar "_out"), local_qn n)
        else Zigvar n
      in

      if List.mem_assoc n var_env then
        let ty = assoc_type n var_env in
        (match ty with
           | Zigty_ptr _ -> Zigderef n_lhs
           | _ -> n_lhs
        )
      else
        n_lhs
  (* Dereference our [self] struct holding the node's memory. *)
  | Lmem v -> Zigfield (Zigderef (Zigvar "self"), local_qn (name v))
  (* Field access. /!\ Indexed Obj expression should be a valid lhs!  *)
  | Lfield (l, fn) -> Zigfield(zigexpr_of_pattern out_env var_env l, fn)
  | Larray (l, idx) ->
      Zigarray(zigexpr_of_pattern out_env var_env l,
             zigexpr_of_exp out_env var_env idx)

and zigexpr_of_ext_value out_env var_env w = match w.w_desc with
  | Wconst c -> zigexpr_of_static_exp c
  (* Each Obc variable corresponds to a plain local Zig variable. *)
  | Wvar v ->
    let n = name v in
    let n_lhs =
      if IdentSet.mem v out_env
      then Zigfield (Zigderef (Zigvar "_out"), local_qn n)
      else Zigvar n
    in

    if List.mem_assoc n var_env then
      let ty = assoc_type n var_env in
      (match ty with
      | Zigty_ptr _ -> Zigderef n_lhs
      | _ -> n_lhs)
    else
      n_lhs
  (* Dereference our [self] struct holding the node's memory. *)
  | Wmem v -> Zigfield (Zigderef (Zigvar "self"), local_qn (name v))
  (* Field access. /!\ Indexed Obj expression should be a valid lhs!  *)
  | Wfield (l, fn) -> Zigfield(zigexpr_of_ext_value out_env var_env l, fn)
  | Warray (l, idx) ->
    Zigarray(zigexpr_of_ext_value out_env var_env l,
           zigexpr_of_exp out_env var_env idx)

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
        let e = if Linearity.is_linear ad.a_linearity then address_of ad.a_type e else e in
          e::(add_targeting l ads)
    | _, _ -> assert false
  in
  let args = (add_targeting args sig_info.node_inputs) in
  if sig_info.node_stateful then (
    let mem =
      (match objn with
         | Oobj o -> Zigfield (Zigderef (Zigvar "self"), local_qn (name o))
         | Oarray (o, l) ->
             let f = Zigfield (Zigderef (Zigvar "self"), local_qn (name o)) in
             let rec mk_idx pl = match pl with
              | [] -> f
              | p::pl -> Zigarray (mk_idx pl, zigexpr_of_pattern out_env var_env p)
             in
             mk_idx l
      ) in
      args@[Zigaddrof out; Zigaddrof mem]
  ) else
    args@[Zigaddrof out]

(** Generate the statement to call [objn].
    [outvl] is a list of lhs where to put the results.
    [args] is the list of expressions to use as arguments.
    [mem] is the lhs where is stored the node's context.*)
let generate_function_call out_env var_env obj_env outvl objn args =
  (* Class name for the object to step. *)
  let classln = assoc_cn objn obj_env in
  let classn = zigname_of_qn classln in
  let sig_info = find_value classln in
  let out = Zigvar (out_var_name_of_objn classn) in

  let fun_call =
    if is_op classln then
      cop_of_op_aux classln args
    else
      (* The step function takes scalar arguments and its own internal memory
          holding structure. *)
      let args = step_fun_call out_env var_env sig_info objn out args in
      (* Our Zig expression for the function call. *)
      Zigfun_call (classn ^ "_step", args)
  in

  (* Act according to the length of our list. Step functions with
     multiple return values will return a structure, and we care of
     assigning each field to the corresponding local variable. *)
  match outvl with
    | [] -> [Zigsexpr fun_call]
    | [outv] when is_op classln ->
        let ty = assoc_type_lhs outv var_env in
          create_affect_stm outv fun_call ty
    | _ ->
        (* Remove options *)
        let out_sig = output_names_list sig_info in
        let create_affect outv out_name =
          let ty = assoc_type_lhs outv var_env in
            create_affect_stm outv (Zigfield (out, local_qn out_name)) ty
        in
          (Zigsexpr fun_call)::(List.flatten (map2 create_affect outvl out_sig))

(** Create the statement dest = c where c = v^n^m... *)
let rec create_affect_const var_env (dest : ziglhs) c =
  match c.se_desc with
    | Svar ln ->
        let se = Static.simplify QualEnv.empty (find_const ln).Signature.c_value in
        create_affect_const var_env dest se
    | Sarray_power(c, n_list) ->
        let rec make_loop power_list replace = match power_list with
          | [] -> dest, replace
          | p :: power_list ->
            let x = gen_symbol () in
            let e, replace =
              make_loop power_list
                        (fun y -> [Zigfor(x, Zigconst (Zigint 0), zigexpr_of_static_exp p, replace y)]) in
            let e =  (ZigLarray (e, Zigvar x)) in
            e, replace
        in
        let e, b = make_loop n_list (fun y -> y) in
        b (create_affect_const var_env e c)
    | Sarray cl ->
        let create_affect_idx c (i, affl) =
          let dest = ZigLarray (dest, Zigconst (Zigint i)) in
            (i - 1, create_affect_const var_env dest c @ affl)
        in
          snd (List.fold_right create_affect_idx cl (List.length cl - 1, []))
    | Srecord f_se_list ->
        let affect_field affl (f, se) =
          let dest_f = ZigLfield (dest, f) in
            (create_affect_const var_env dest_f se) @ affl
        in
          List.fold_left affect_field [] f_se_list
    | _ -> [Zigaffect (dest, zigexpr_of_static_exp c)]

(** [cstm_of_act obj_env mods act] translates the Obj action [act] to a list of
    Zig statements, using the association list [obj_env] to map object names to
    class names.  *)
let rec cstm_of_act out_env var_env obj_env act =
  match act with
      (* Cosmetic : cases on boolean values are converted to if statements. *)
    | Acase (c, [({name = "true"}, te); ({ name = "false" }, fe)])
    | Acase (c, [({name = "false"}, fe); ({ name = "true"}, te)]) ->
        let cc = zigexpr_of_exp out_env var_env c in
        let cte = cstm_of_act_list out_env var_env obj_env te in
        let cfe = cstm_of_act_list out_env var_env obj_env fe in
        [Zigif (cc, cte, cfe)]
    | Acase (c, [({name = "true"}, te)]) ->
        let cc = zigexpr_of_exp out_env var_env c in
        let cte = cstm_of_act_list out_env var_env obj_env te in
        let cfe = [] in
        [Zigif (cc, cte, cfe)]
    | Acase (c, [({name = "false"}, fe)]) ->
        let cc = Ziguop ("!", (zigexpr_of_exp out_env var_env c)) in
        let cte = cstm_of_act_list out_env var_env obj_env fe in
        let cfe = [] in
        [Zigif (cc, cte, cfe)]


    (* Translation of case into a Zig switch statement is simple enough: we
       just recursively translate obj expressions and statements to
       corresponding Zig constructs, and cautiously "shortnamize"
       constructor names. *)
    | Acase (e, cl) ->
        (* [ccl_of_obccl] translates an Obc clause to a Zig clause. *)
        let ccl =
          List.map
            (fun (c,act) -> zigname_of_qn c,
               cstm_of_act_list out_env var_env obj_env act) cl in
        [Zigswitch (zigexpr_of_exp out_env var_env e, ccl)]

    | Ablock b ->
        cstm_of_act_list out_env var_env obj_env b

    (* For composition of statements, just recursively apply our
       translation function on sub-statements. *)
    | Afor ({ v_ident = x }, i1, i2, act) ->
        [Zigfor(name x, zigexpr_of_exp out_env var_env i1,
              zigexpr_of_exp out_env var_env i2,
              cstm_of_act_list out_env var_env obj_env act)]

    (* Translate constant assignment *)
    | Aassgn (vn, { e_desc = Eextvalue { w_desc = Wconst c }; }) ->
        let vn = ziglhs_of_pattern out_env var_env vn in
        create_affect_const var_env vn c

    (* Purely syntactic translation from an Obc local variable to a Zig
       local one, with recursive translation of the rhs expression. *)
    | Aassgn (vn, e) ->
        let vn = ziglhs_of_pattern out_env var_env vn in
        let ty = assoc_type_lhs vn var_env in
        let ce = zigexpr_of_exp out_env var_env e in
        create_affect_stm vn ce ty

    (* Our Aop marks an operator invocation that will perform side effects. Just
       translate to a simple Zig statement. *)
    | Aop (op_name, args) ->
        [Zigsexpr (cop_of_op out_env var_env op_name args)]

    (* Reinitialization of an object variable, extracting the reset
       function's name from our environment [obj_env]. *)
    | Acall (name_list, o, Mreset, args) ->
        assert_empty name_list;
        assert_empty args;
        let on = obj_ref_name o in
        let obj = assoc_obj on obj_env in
        let classn = zigname_of_qn obj.o_class in
        let field = Zigfield (Zigderef (Zigvar "self"), local_qn (name on)) in
        (match o with
          | Oobj _ ->
              [Zigsexpr (Zigfun_call (classn ^ "_reset", [Zigaddrof field]))]
          | Oarray (_, pl) ->
              let rec mk_loop pl field = match pl with
                | [] ->
                    [Zigsexpr (Zigfun_call (classn ^ "_reset", [Zigaddrof field]))]
                | p::pl ->
                    mk_loop pl (Zigarray(field, zigexpr_of_pattern out_env var_env p))
              in
                 mk_loop pl field
        )

    (* Step functions applications can return multiple values, so we use a
       local structure to hold the results, before allocating to our
       variables. *)
    | Acall (outvl, objn, Mstep, el) ->
        let args = zigexprs_of_exps out_env var_env el in
        let outvl = ziglhs_list_of_pattern_list out_env var_env outvl in
        generate_function_call out_env var_env obj_env outvl objn args


and cstm_of_act_list out_env var_env obj_env b =
  let l = List.map zigvar_of_vd b.b_locals in
  let var_env = l @ var_env in
  let cstm = List.flatten (List.map (cstm_of_act out_env var_env obj_env) b.b_body) in
    match l with
      | [] -> cstm
      | _ ->
            [Zigsblock { var_decls = l; block_body = cstm }]

(* TODO needed only because of renaming phase *)
let global_name = ref "";;



(** {2 step() and reset() functions generation} *)

let qn_append q suffix =
  { qual = q.qual; name = q.name ^ suffix }

(** Builds the argument list of step function*)
let step_fun_args n md =
  let args = inputlist_of_ovarlist md.m_inputs in
  let out_arg = [("_out", Zigty_ptr (Zigty_id (qn_append n "_out")))] in
  let context_arg =
    if is_stateful n then
      [("self", Zigty_ptr (Zigty_id (qn_append n "_mem")))]
    else
      []
  in
    args @ out_arg @ context_arg


(** [fun_def_of_step_fun name obj_env mods sf] returns a Zig function definition
    [name ^ "_out"] corresponding to the Obc step function [sf]. The object name
    <-> class name mapping [obj_env] is needed to translate internal steps and
    reset calls. A step function can have multiple return values, whereas Zig does
    not allow such functions. When it is the case, we declare a structure with a
    field by return value. *)
let fun_def_of_step_fun n obj_env mem objs md =
  let fun_name = (zigname_of_qn n) ^ "_step" in
  (* Its arguments, translating Obc types to Zig types and adding our internal
      memory structure. *)
  let args = step_fun_args n md in

  (* Out vars for function calls *)
  let out_vars =
    unique
      (List.map (fun obj -> out_var_name_of_objn (zigname_of_qn obj.o_class),
                   Zigty_id (qn_append obj.o_class "_out"))
         (List.filter (fun obj -> not (is_op obj.o_class)) objs)) in

  (* The body *)
  let mems = List.map zigvar_of_vd (mem@md.m_outputs) in
  let var_env = args @ mems @ out_vars in
  let out_env =
    List.fold_left
      (fun out_env vd -> IdentSet.add vd.v_ident out_env)
      IdentSet.empty
      md.m_outputs
  in
  let body = cstm_of_act_list out_env var_env obj_env md.m_body in

  Zigfundef {
    Zig.f_name = fun_name;
    f_retty = Zigty_void;
    f_args = args;
    f_body = {
      var_decls = out_vars;
      block_body = body
    }
  }

(** [mem_decl_of_class_def cd] returns a declaration for a Zig structure holding
    internal variables and objects of the Obc class definition [cd]. *)
let mem_decl_of_class_def cd =
  (* This one just translates the class name to a struct name following the
     convention we described above. *)
  let struct_field_of_obj_dec l od =
    if is_stateful od.o_class then
      let ty = Zigty_id (qn_append od.o_class "_mem") in
      let ty = match od.o_size with
        | Some nl ->
          let rec mk_idx nl = match nl with
            | [] -> ty
            | n::nl -> Zigty_arr (int_of_static_exp n, mk_idx nl)
          in
            mk_idx nl
        | None -> ty in
        (name od.o_ident, ty)::l
    else
      l
  in
    if is_stateful cd.cd_name then (
      (* Fields corresponding to normal memory variables. *)
      let mem_fields = List.map zigvar_of_vd cd.cd_mems in
      (* Fields corresponding to object variables. *)
      let obj_fields = List.fold_left struct_field_of_obj_dec [] cd.cd_objs in
        [Zigdecl_struct ((zigname_of_qn cd.cd_name) ^ "_mem",
                       mem_fields @ obj_fields)]
    ) else
      []

let out_decl_of_class_def cd =
  (* Fields corresponding to output variables. *)
  let step_m = find_step_method cd in
  let out_fields = List.map zigvar_of_vd step_m.m_outputs in
    [Zigdecl_struct ((zigname_of_qn cd.cd_name) ^ "_out", out_fields)]

(** [reset_fun_def_of_class_def cd] returns the defintion of the Zig function
    tasked to reset the class [cd]. *)
let reset_fun_def_of_class_def cd =
  let body =
    if cd.cd_stateful then
      let var_env = List.map zigvar_of_vd cd.cd_mems in
      let reset = find_reset_method cd in
      cstm_of_act_list IdentSet.empty var_env cd.cd_objs reset.m_body
    else
      []
  in
  Zigfundef {
    Zig.f_name = (zigname_of_qn cd.cd_name) ^ "_reset";
    f_retty = Zigty_void;
    f_args = [("self", Zigty_ptr (Zigty_id (qn_append cd.cd_name "_mem")))];
    f_body = {
      var_decls = [];
      block_body = body;
    }
  }


(** [zigdecl_and_cfun_of_class_def cd] translates the class definition [cd] to
    a Zig program. *)
let zigdefs_and_zigdecls_of_class_def cd =
  (* We keep the state of our class in a structure, holding both internal
     variables and the state of other nodes. For a class named ["zigname"], the
     structure will be called ["zigname_mem"]. *)
  Idents.enter_node cd.cd_name;
  let step_m = find_step_method cd in
  let memory_struct_decl = mem_decl_of_class_def cd in
  let out_struct_decl = out_decl_of_class_def cd in
  let step_fun_def = fun_def_of_step_fun cd.cd_name
    cd.cd_objs cd.cd_mems cd.cd_objs step_m in
  (* Zig function for resetting our memory structure. *)
  let reset_fun_def = reset_fun_def_of_class_def cd in
(**  let res_fun_decl = zigdecl_of_zigfundef reset_fun_def in
  let step_fun_decl = zigdecl_of_zigfundef step_fun_def in*)
  let (decls, defs) =
    if is_stateful cd.cd_name then
      ([], [reset_fun_def; step_fun_def])
    else
      ([], [step_fun_def]) in

  memory_struct_decl @ out_struct_decl @ decls,
  defs

(** {2 Type translation} *)

(** Translates an Obc type declaration to its Zig counterpart. *)
let zigdefs_and_zigdecls_of_type_decl otd =
  let name = zigname_of_qn otd.t_name in
  match otd.t_desc with
    | Type_abs -> [], [] (*assert false*)
    | Type_alias ty ->
      [], [] (* Zigdecl_typedef (zigtype_of_otype ty, name) *)
    | Type_enum nl ->
        let of_string_fun = Zigfundef
          { Zig.f_name = name ^ "_of_string";
            f_retty = Zigty_id otd.t_name;
            f_args = [("s", Zigty_ptr Zigty_char)];
            f_body =
              { var_decls = [];
                block_body =
                  let gen_if t =
                    let t = zigname_of_qn t and t' = t.name in
                    let funcall = Zigfun_call ("strcmp", [Zigvar "s";
                                                        Zigconst (Zigstrlit t')]) in
                    let cond = Zigbop ("==", funcall, Zigconst (Zigint 0)) in
                    Zigif (cond, [Zigreturn (Zigconst (Zigtag t))], []) in
                  map gen_if nl; }
          }
        and to_string_fun = Zigfundef
          { Zig.f_name = "string_of_" ^ name;
            f_retty = Zigty_ptr Zigty_char;
            f_args = [("x", Zigty_id otd.t_name); ("buf", Zigty_ptr Zigty_char)];
            f_body =
              { var_decls = [];
                block_body =
                  let gen_clause t =
                    let t = zigname_of_qn t and t' = t.name in
                    let fun_call =
                      Zigfun_call ("strcpy", [Zigvar "buf";
                                            Zigconst (Zigstrlit t')]) in
                    (t, [Zigsexpr fun_call]) in
                  [Zigswitch (Zigvar "x", map gen_clause nl);
                   Zigreturn (Zigvar "buf")]; }
          } in
        ([of_string_fun; to_string_fun],
         [Zigdecl_enum (name, List.map zigname_of_qn nl)])
    | Type_struct fl ->
        let decls = List.map (fun f -> zigname_of_name f.Signature.f_name.name,
                                zigtype_of_otype f.Signature.f_type) fl in
        let decl = Zigdecl_struct (name, decls) in
        ([], [decl])

let zigdefs_and_zigdecls_of_const_decl cd =
  let name = zigname_of_qn cd.c_name in
  let v = zigexpr_of_static_exp cd.Obc.c_value in
  let cty = zigtype_of_otype cd.Obc.c_type in
  [], [Zigdecl_constant (name, cty, v)]

let zigdefs_and_zigdecls_of_interface_decl id = match id with
  | Itypedef td -> zigdefs_and_zigdecls_of_type_decl td
  | Iconstdef cd -> zigdefs_and_zigdecls_of_const_decl cd
  | _ -> [], []

let zigdefs_and_zigdecls_of_program_decl id = match id with
  | Ptype td -> zigdefs_and_zigdecls_of_type_decl td
  | Pconst cd -> zigdefs_and_zigdecls_of_const_decl cd
  | _ -> [], []

let header_of_module m = match m with
  | Module "Iostream" -> "stdio"
  | _ -> String.uncapitalize_ascii (modul_to_string m)

(* Header files included in all generated XXX_types.h headers.  *)
let common_types_c_headers = ["stdbool"; "assert"; "pervasives"]

let global_file_header name prog =
  let dependencies = ModulSet.elements (Obc_utils.Deps.deps_program prog) in
  let dependencies = List.map header_of_module dependencies in

  let dependencies_types =
    List.map
      (function
          "stdio" as s -> s
        | s -> s ^ "_types")
      dependencies in

  let classes = program_classes prog in
  let (decls, defs) =
    List.split (List.map zigdefs_and_zigdecls_of_class_def classes) in
  let decls = List.concat decls
  and defs = List.concat defs in

  let filename_types = name ^ "_types" in
  let zigdefs_and_zigdecls = List.map zigdefs_and_zigdecls_of_program_decl prog.p_desc in

  let (cty_defs, cty_decls) = List.split zigdefs_and_zigdecls in
  let types_zig = (filename_types ^ ".zig", (concat cty_defs)) in

  let source =
    (name ^ ".zig", defs) in
  [source; types_zig]


let interface_header name i =
  let dependencies = ModulSet.elements (Obc_utils.Deps.deps_interface i) in
  let dependencies = List.map header_of_module dependencies in

  let zigdefs_and_zigdecls = List.map zigdefs_and_zigdecls_of_interface_decl i.i_desc in

  let (cty_defs, cty_decls) = List.split zigdefs_and_zigdecls in
  let filename_types = name ^ "_types" in
  let types_c = (filename_types ^ ".zig", (concat cty_defs)) in
  let source = (name ^ ".zig", []) in
  [source; types_c]
