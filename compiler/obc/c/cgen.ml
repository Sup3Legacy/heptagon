(***********************************************************************)
(*                                                                     *)
(*                             Heptagon                                *)
(*                                                                     *)
(* Gwenael Delaval, LIG/INRIA, UJF                                     *)
(* Leonard Gerard, Parkas, ENS                                         *)
(* Adrien Guatto, Parkas, ENS                                          *)
(* Cedric Pasteur, Parkas, ENS                                         *)
(* Marc Pouzet, Parkas, ENS                                            *)
(*                                                                     *)
(* Copyright 2012 ENS, INRIA, UJF                                      *)
(*                                                                     *)
(* This file is part of the Heptagon compiler.                         *)
(*                                                                     *)
(* Heptagon is free software: you can redistribute it and/or modify it *)
(* under the terms of the GNU General Public License as published by   *)
(* the Free Software Foundation, either version 3 of the License, or   *)
(* (at your option) any later version.                                 *)
(*                                                                     *)
(* Heptagon is distributed in the hope that it will be useful,         *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of      *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the       *)
(* GNU General Public License for more details.                        *)
(*                                                                     *)
(* You should have received a copy of the GNU General Public License   *)
(* along with Heptagon.  If not, see <http://www.gnu.org/licenses/>    *)
(*                                                                     *)
(***********************************************************************)

open List
open Containers
open Misc
open Names
open Idents
open Obc
open Obc_utils
open Types

open Modules
open Signature
open C
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
    | Eunsupportedkindofoutput of clhs

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
          s
    | Eunsupportedkindofoutput outv ->
        eprintf "%aCgen::step_fun_call : unsupported kind of outputs\
                    when no output structure is generated (outv = %a).@."
          print_location loc
          C.pp_clhs outv
    );
    raise Errors.Error
end

let struct_name ty =
  match ty with
  | Cty_id n -> n
  | _ -> assert false

let int_of_static_exp se =
  Static.int_of_static_exp QualEnv.empty se


(* Datatype to string conversion
let rec tostring_static_exp_desc sedesc = match sedesc with
  | Sint i -> (string_of_int i)
  | Svar id -> id.name
  | Sop (op, se_list) ->
      if is_infix (shortname op)
      then
        let e1,e2 = Misc.assert_2 se_list in
        let s1 = tostring_static_exp_desc e1.se_desc in
        let s2 = tostring_static_exp_desc e2.se_desc in
        (s1 ^ " " ^ (shortname op) ^ " " ^ s2)
      else
        let lstr = List.fold_left
          (fun acc se -> acc ^ (tostring_static_exp_desc se.se_desc))
          "" se_list
        in
        (shortname op) ^ " " ^ lstr
  | _ -> failwith "tostring_static_exp_desc : static expression should not appear as an array size"
*)


let output_names_list sig_info =
  let remove_option ad = match ad.a_name with
    | Some n -> n
    | None -> Error.message no_location Error.Eno_unnamed_output
  in
  let outputs = List.filter
    (fun ad -> not (Linearity.is_linear ad.a_linearity)) sig_info.node_outputs in
    List.map remove_option outputs

let is_stateful n =
  (* OpenCL kernel are not stateful... *)
  if (check_kernel n) then false else
  try
    let sig_info = find_value n in
      sig_info.node_stateful
  with
    Not_found ->Error.message no_location (Error.Enode (fullname n))

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
    | Types.Tid id when id = Initial.pint -> Cty_int
    | Types.Tid id when id = Initial.pfloat -> Cty_float
    | Types.Tid id when id = Initial.pbool -> Cty_int
    | Tid id -> Cty_id id
    | Tarray(ty, n) -> Cty_arr(int_of_static_exp n, ctype_of_otype ty)
    | Tprod _ -> assert false
    | Tclasstype _ -> assert false
    | Tinvalid -> assert false

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
  name vd.v_ident, ctype_of_otype vd.v_type

let rec clhs_to_var_conversion outv = match outv with
  | CLvar s -> Cvar s
  | CLderef d -> Cderef (clhs_to_var_conversion d)
  | CLfield (cl, name) -> Cfield ((clhs_to_var_conversion cl), name)
  | _ -> Error.message no_location (Error.Eunsupportedkindofoutput outv)

(** Returns the type of a pointer to a type, except for
    types which are already pointers. *)
let pointer_type ty cty =
  match Modules.unalias_type ty with
    | Tarray _ -> cty
    | _ -> Cty_ptr cty

(** Returns the expression to use e as an argument of
    a function expecting a pointer as argument. *)
let address_of ty e =
  match Modules.unalias_type ty with
    | Tarray _ -> e
    | _ -> Caddrof e

let inputlist_of_ovarlist vl =
  let cvar_of_ovar vd =
    let ty = ctype_of_otype vd.v_type in
    let ty = if vd.v_mutable then pointer_type vd.v_type ty else ty in
    name vd.v_ident, ty
  in
  List.map cvar_of_ovar vl

let outputlist_of_ovarlist vl =
  let cvar_of_ovar vd =
    let ty = ctype_of_otype vd.v_type in
    let ty = pointer_type vd.v_type ty in (* Always pointer, because output *)
    name vd.v_ident, ty
  in
  List.map cvar_of_ovar vl

(** @return the unaliased version of a type. *)
let rec unalias_ctype cty = match cty with
  | Cty_id ty_name ->
    (try match find_type ty_name with
    | Talias ty -> unalias_ctype (ctype_of_otype ty)
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
  with Not_found -> Error.message no_location (Error.Evar n)

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
    | _ -> Error.message no_location Error.Ederef_not_pointer)
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
        stm@(_create_affect_lit dest (i+1) l)
  in
  _create_affect_lit dest 0 l

(** Creates the expression dest <- src (copying arrays if necessary). *)
and create_affect_stm dest src ty =
  match unalias_ctype ty with
    | Cty_arr (n, bty) ->
        (match src with
           | Carraylit l -> create_affect_lit dest l bty
           | src ->
             let x = gen_symbol () in
             [Cfor(x,
                   Cconst (Ccint 0), Cconst (Ccint n),
                   create_affect_stm
                     (CLarray (dest, Cvar x))
                     (Carray (src, Cvar x)) bty)]
        )
    | Cty_id ln ->
        (match src with
          | Cstructlit (_, ce_list) ->
              let create_affect { Signature.f_name = f_name;
                                  Signature.f_type = f_type; } e stm_list =
                let cty = ctype_of_otype f_type in
                create_affect_stm (CLfield (dest, f_name)) e cty @ stm_list in
              List.fold_right2 create_affect (find_struct ln) ce_list []
          | _ -> [Caffect (dest, src)])
    | _ -> [Caffect (dest, src)]

let rec cexpr_of_static_exp se =
  match se.se_desc with
    | Sint i -> Cconst (Ccint i)
    | Sfloat f -> Cconst (Ccfloat f)
    | Sbool b -> Cconst (Ctag (if b then "true" else "false"))
    | Sstring s -> Cconst (Cstrlit s)
    | Sfield _ -> assert false
    | Sconstructor c -> Cconst (Ctag (cname_of_qn c))
    | Sarray sl -> Carraylit (List.map cexpr_of_static_exp sl)
    | Srecord fl ->
        let ty_name =
          match Modules.unalias_type se.se_ty with
            | Types.Tid n -> n
            | _ -> assert false
        in
        let cexps_assoc = List.rev_map (fun (f, e) -> f, cexpr_of_static_exp e) fl in
        cexpr_of_struct ty_name cexps_assoc
    | Sarray_power(c,n_list) ->
          (List.fold_left (fun cc n -> Carraylit (repeat_list cc (int_of_static_exp n)))
                     (cexpr_of_static_exp c) n_list)
    | Svar ln ->
      if !Compiler_options.unroll_loops && se.se_ty = Initial.tint
      then
        begin
        let cDec = find_const ln in
        match cDec.Signature.c_value with
          | None -> cexpr_of_static_exp (Types.mk_static_exp cDec.Signature.c_type (Svar ln))
          | Some cval -> cexpr_of_static_exp (Static.simplify QualEnv.empty cval)
        end
      else Cvar (cname_of_qn ln)
    | Sop _ ->
        let se' = Static.simplify QualEnv.empty se in
          if se = se' then
            Error.message se.se_loc Error.Estatic_exp_compute_failed
          else
            cexpr_of_static_exp se'
    | Stuple _ -> Misc.internal_error "cgen: static tuple"

(** [cexpr_of_exp exp] translates the Obj action [exp] to a C expression. *)
and cexpr_of_exp out_env var_env exp =
  match exp.e_desc with
    | Eextvalue w  -> cexpr_of_ext_value out_env var_env w
    (* Operators *)
    | Eop(op, exps) -> cop_of_op out_env var_env op exps
    (* Structure literals. *)
    | Estruct (tyn, fl) ->
        let cexpr = cexpr_of_exp out_env var_env in
        let cexps_assoc = List.rev_map (fun (f, e) -> f, cexpr e) fl in
        cexpr_of_struct tyn cexps_assoc
    | Earray e_list ->
        Carraylit (cexprs_of_exps out_env var_env e_list)

and cexpr_of_struct tyn cexps_assoc =
  let cexps = List.fold_left
    (fun cexps { Signature.f_name = f } -> List.assoc f cexps_assoc :: cexps)
    [] (find_struct tyn) in
  (* Reverse `cexps' here because of the previous use of `List.fold_left'. *)
  Cstructlit (cname_of_qn tyn, List.rev cexps)

and cexprs_of_exps out_env var_env exps =
  List.map (cexpr_of_exp out_env var_env) exps

and cop_of_op_aux op_name cexps = match op_name with
    | { qual = Pervasives; name = op } ->
        begin match op,cexps with
          | ("~-" | "~-."), [e] -> Cuop ("-", e)
          | ("~~"), [e] -> Cuop ("~", e)
          | "not", [e] -> Cuop ("!", e)
          | ("&"), [e] -> Cuop ("&", e)
          | (
              "=" | "<>"
            | "&" | "or"
            | "+" | "-" | "*" | "/"
            | "*." | "/." | "+." | "-." | "%" | "<<<" | ">>>" | "&&&" | "|||"
            | "<" | ">" | "<=" | ">=" | "<=." | "<." | ">=." | ">."), [el;er] ->
             Cbop (copname op, el, er)
          | "=>", [el;er] ->
             Cbop ("||", (Cuop("!",el)), er)
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
  (* Each Obc variable corresponds to a real local C variable. *)
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
  (* Dereference our [self] struct holding the node's memory. *)
  | Lmem v -> CLfield (CLderef (CLvar "self"), local_qn (name v))
  (* Field access. /!\ Indexed Obj expression should be a valid lhs!  *)
  | Lfield (l, fn) -> CLfield(clhs_of_pattern out_env var_env l, fn)
  | Larray (l, idx) ->
      CLarray(clhs_of_pattern out_env var_env l,
              cexpr_of_exp out_env var_env idx)

and clhs_list_of_pattern_list out_env var_env lhss =
  List.map (clhs_of_pattern out_env var_env) lhss

and cexpr_of_pattern out_env var_env l = match l.pat_desc with
  (* Each Obc variable corresponds to a real local C variable. *)
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
  (* Dereference our [self] struct holding the node's memory. *)
  | Lmem v -> Cfield (Cderef (Cvar "self"), local_qn (name v))
  (* Field access. /!\ Indexed Obj expression should be a valid lhs!  *)
  | Lfield (l, fn) -> Cfield(cexpr_of_pattern out_env var_env l, fn)
  | Larray (l, idx) ->
      Carray(cexpr_of_pattern out_env var_env l,
             cexpr_of_exp out_env var_env idx)

and cexpr_of_ext_value out_env var_env w = match w.w_desc with
  | Wconst c -> cexpr_of_static_exp c
  (* Each Obc variable corresponds to a plain local C variable. *)
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
  (* Dereference our [self] struct holding the node's memory. *)
  | Wmem v -> Cfield (Cderef (Cvar "self"), local_qn (name v))
  (* Field access. /!\ Indexed Obj expression should be a valid lhs!  *)
  | Wfield (l, fn) -> Cfield(cexpr_of_ext_value out_env var_env l, fn)
  | Warray (l, idx) ->
    Carray(cexpr_of_ext_value out_env var_env l,
           cexpr_of_exp out_env var_env idx)

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
let step_fun_call out_env var_env sig_info outvl objn out args =
  let rec add_targeting l ads = match l, ads with
    | [], [] -> []
    | e::l, ad::ads ->
        (*this arg is targeted, use a pointer*)
        let e = if Linearity.is_linear ad.a_linearity then address_of ad.a_type e else e in
          e::(add_targeting l ads)
    | _, _ -> assert false
  in
  let rec add_targeting_out l ads = match l, ads with
    | [], [] -> []
    | e::l, ad::ads ->
        (* Always use a pointer for outputs *)
        let e = address_of ad.a_type e in
          e::(add_targeting_out l ads)
    | _, _ -> assert false
  in
  
  (* DEBUG
  List.iter (fun outv ->
    Format.fprintf (Format.formatter_of_out_channel stdout) "outv = %a\n@?"
      C.pp_clhs outv
  ) outvl; *)
  
  let args = (add_targeting args sig_info.node_inputs) in
  let args = if (!Compiler_options.cg_outlist) then (

      let args_out = List.map clhs_to_var_conversion outvl in

      let l_lin_in = List.fold_left (fun acc arg_in -> match arg_in.a_linearity with
        | Linearity.Lat vlin -> vlin::acc
        | _ -> acc
      ) [] sig_info.node_inputs in
      let sig_info_out_filtered = List.filter (fun arg_out -> match arg_out.a_linearity with
          | Linearity.Lat vlin_out -> not (List.exists (fun vlin_in -> vlin_in=vlin_out) l_lin_in)
          | _ -> true
      ) sig_info.node_outputs in


      (* DEBUG
      Format.fprintf (Format.formatter_of_out_channel stdout) "args_out.size = %i | node_outputs.size = %i\n@?"
        (List.length args_out) (List.length sig_info.node_outputs);
      Format.fprintf (Format.formatter_of_out_channel stdout) "l_lin_in.size = %i\n@?"
        (List.length l_lin_in);
      Format.fprintf (Format.formatter_of_out_channel stdout) "sig_info_out_filtered.size = %i\n@?"
        (List.length sig_info_out_filtered); *)

      let args_out = add_targeting_out args_out sig_info_out_filtered in
      args @ args_out
    ) else args
  in
  let caddrout = if (!Compiler_options.cg_outlist) then [] else [Caddrof out] in
  if sig_info.node_stateful then (
    let mem =
      (match objn with
         | Oobj o -> Cfield (Cderef (Cvar "self"), local_qn (name o))
         | Oarray (o, l) ->
             let f = Cfield (Cderef (Cvar "self"), local_qn (name o)) in
             let rec mk_idx pl = match pl with
              | [] -> f
              | p::pl -> Carray (mk_idx pl, cexpr_of_pattern out_env var_env p)
             in
             mk_idx l
      ) in
    if (!Compiler_options.cg_memfirst) then
      (Caddrof mem) :: (args@caddrout)
    else
      args @ caddrout @ [Caddrof mem]
  ) else
    args@caddrout

(** Generate the statement to call [objn].
    [outvl] is a list of lhs where to put the results.
    [args] is the list of expressions to use as arguments.
    [mem] is the lhs where is stored the node's context.*)
let generate_function_call out_env var_env obj_env oname_fun outvl objn args =
  (* Class name for the object to step. *)
  let classln = assoc_cn objn obj_env in
  let classn = cname_of_qn classln in
  let sig_info = find_value classln in
  let out = Cvar (out_var_name_of_objn classn) in

  let fun_call =
    if is_op classln then
      cop_of_op_aux classln args
    else
      (* The step function takes scalar arguments and its own internal memory
          holding structure. *)
      let args = step_fun_call out_env var_env sig_info outvl objn out args in
      (* Our C expression for the function call. *)
      let name_fun = match oname_fun with
        | None -> classn ^ "_step"    (* Default case*)
        | Some name -> name           (* Only happens when Mother *)
      in
      Cfun_call (name_fun, args)
  in

  (* Act according to the length of our list. Step functions with
     multiple return values will return a structure, and we care of
     assigning each field to the corresponding local variable. *)
  if (!Compiler_options.cg_outlist) then [Csexpr fun_call] else
  match outvl with
    | [] -> [Csexpr fun_call]
    | [outv] when is_op classln ->
        let ty = assoc_type_lhs outv var_env in
          create_affect_stm outv fun_call ty
    | _ ->
        (* Remove options *)
        let out_sig = output_names_list sig_info in
        let create_affect outv out_name =
          let ty = assoc_type_lhs outv var_env in
            create_affect_stm outv (Cfield (out, local_qn out_name)) ty
        in
          (Csexpr fun_call)::(List.flatten (map2 create_affect outvl out_sig))



(* Get the "sizeof cexpr" from a type *)
let rec type_to_sizeof ty = match ty with
  | Tprod tl ->
    List.fold_left (fun acc t ->
      Cbop ("+", (type_to_sizeof t), acc)
    ) (Cconst (Ccint 0)) tl 
  | Tid name ->
    Cfun_call ("sizeof", (Cconst (Ctag (shortname name)))::[])
  | Tarray (ty, se) ->
    Cbop ("*", (type_to_sizeof ty), cexpr_of_static_exp se)
  | Tclasstype _ | Tinvalid -> failwith "Invalid types - should not be present on CG level"


(** generate the statements to call the kernel [objn]
    [outvl] is a list of lhs where to put the results.
    [args] is the list of expressions to use as arguments.
    [mem] is the lhs where is stored the node's context.*)
let generate_kernel_call out_env var_env obj_env ocl outvl objn args =
  (* Default behavior if the option to generate OpenCL code is disabled *)
  if (not (!Compiler_options.opencl_cg)) then
    generate_function_call out_env var_env obj_env None outvl objn args
  else

  (* Info on the kernel *)
  let idkernel = ocl.copt_id in
  let (_, sig_info_kernel, _) = try
      IntMap.find idkernel !Openclprep.mKernelCL
    with Not_found -> failwith ("OpenCL kernel number " ^ (string_of_int idkernel) ^ " was not found")
  in
  
  (* Retrieving infos on the buffers *)
  let (_, _, bufferinfos) = IntMap.find idkernel !Openclprep.mBufferCL in

  (* Retrieving info on queue *)
  let queue_num = StringMap.find ocl.copt_device_id !Openclprep.mQueueCL in

  (* For preparing the inputs *)
  let rec add_targeting l ads = match l, ads with
    | [], [] -> []
    | e::l, ad::ads ->
        (*this arg is targeted, use a pointer*)
        let e = if Linearity.is_linear ad.a_linearity then address_of ad.a_type e else e in
          e::(add_targeting l ads)
    | _, _ -> assert false
  in

  if (ocl.copt_is_launch) then begin
    (* Offloading - launch part *)

    let bufferInput = Openclprep.BoolIntMap.fold (fun (isIn, pos) (v,_) acc ->
      if (isIn) then (pos,v)::acc else acc
    ) bufferinfos [] in
    let args = add_targeting args sig_info_kernel.k_input in
    
    (* Step A - Enqueue write buffer *)
    let lcstm_stepA = List.fold_left (fun acc (posIn, bufferId) ->
      let argIn = List.nth sig_info_kernel.k_input posIn in
      let sexprIn = List.nth args posIn in
      let lcexp_buffIn =
        (* Queue *)
        (Carray (
          (Cfield (Cconst (Ctag Openclprep.icl_data_struct_string), (Modules.current_qual "queues")))
          ,
          (Cconst (Ccint queue_num))
        ))::
        (* Buffer *)
        (Carray (
          (Cfield (Cconst (Ctag Openclprep.icl_data_struct_string), (Modules.current_qual "buffers")))
          ,
          (Cconst (Ccint bufferId))
        ))::
        (* Blocking write *)
        (Cconst (Ctag "CL_TRUE"))::
        (* Position as input *)
        (* (Cconst (Ccint posIn)):: *)
        (Cconst (Ccint 0))::
        (* Size of the data transfered *)
        (type_to_sizeof argIn.a_type)::
        (* Input : always need pointers (even if integer) *)
        (address_of argIn.a_type sexprIn)::
        (* Disabled options *)
        (Cconst (Ccint 0))::(Cconst (Ctag "NULL"))::(Cconst (Ctag "NULL"))::[]
      in
      let fun_call_buffIn = Cfun_call ("clEnqueueWriteBuffer", lcexp_buffIn) in
      let cstm_bufIn = Csexpr fun_call_buffIn in
      cstm_bufIn::acc
    ) [] bufferInput in

    (* Step B - Enqueue computation *)
    let lcexp_comput =
      (* Queue *)
      (Carray (
        (Cfield (Cconst (Ctag Openclprep.icl_data_struct_string), (Modules.current_qual "queues")))
        ,
        (Cconst (Ccint queue_num))
      ))::
      (* Kernel *)
      (Carray (
          (Cfield (Cconst (Ctag Openclprep.icl_data_struct_string), (Modules.current_qual "kernels")))
          ,
          (Cconst (Ccint idkernel))
        ))::
      (* Dimension of the kernel *)
      (Cconst (Ccint sig_info_kernel.k_dim))::
      (* Disabled alignment option *)
      (Cconst (Ctag "NULL"))::
      (* Info on local_worksize *)
      (Cstructlitraw ("size_t[1]", [Cconst (Ccint ocl.copt_gl_worksize)]))::
      (* Info on global_worksize *)
      (Cstructlitraw ("size_t[1]", [Cconst (Ccint ocl.copt_loc_worksize)]))::
      (Cconst (Ccint 0))::(Cconst (Ctag "NULL"))::(Cconst (Ctag "NULL"))::[]    (* Disabled options *)
    in
    (* Note for eventual debug: if Cstructlit does not work, do with Ctag "{" ^ ... ^ "}" *)
    let fun_call_comput = Cfun_call ("clEnqueueNDRangeKernel", lcexp_comput) in
    let cstm_stepB = Csexpr fun_call_comput in

    (* Output: list of statements, the order matters *)
    lcstm_stepA @ [cstm_stepB]
  
  end else begin
    (* Offloading - recover part *)

    let bufferOutput = Openclprep.BoolIntMap.fold (fun (isIn, pos) (v,_) acc ->
      if (not isIn) then (pos,v)::acc else acc
    ) bufferinfos [] in
    let args_out = List.map clhs_to_var_conversion outvl in

    (* Step C - Waiting for completion *)
    let lcexp_completion =
      (* Queue *)
      (Carray (
        (Cfield (Cconst (Ctag Openclprep.icl_data_struct_string), (Modules.current_qual "queues")))
        ,
        (Cconst (Ccint queue_num))
      ))::[]
    in
    let fun_call_completion = Cfun_call ("clFinish", lcexp_completion) in
    let cstm_stepC = Csexpr fun_call_completion in

    (* Step D - Retrieve data *)
    let lcstm_stepD = List.fold_left (fun acc (posOut, bufferId) ->
      let argOut = List.nth sig_info_kernel.k_input posOut in
      let sexprOut = List.nth args_out posOut in
      let lcexp_buffOut =
        (* Queue *)
        (Carray (
          (Cfield (Cconst (Ctag Openclprep.icl_data_struct_string), (Modules.current_qual "queues")))
          ,
          (Cconst (Ccint queue_num))
        ))::
        (* Buffer *)
        (Carray (
          (Cfield (Cconst (Ctag Openclprep.icl_data_struct_string), (Modules.current_qual "buffers")))
          ,
          (Cconst (Ccint bufferId))
        ))::
        (* Blocking read *)
        (Cconst (Ctag "CL_TRUE"))::
        (Cconst (Ccint posOut))::
        (type_to_sizeof argOut.a_type)::
        (* Output : always need pointers (even if integer) *)
        (address_of argOut.a_type sexprOut)::
        (Cconst (Ccint 0))::(Cconst (Ctag "NULL"))::(Cconst (Ctag "NULL"))::[]    (* Disabled options *)
      in
      let fun_call_buffOut = Cfun_call ("clEnqueueReadBuffer", lcexp_buffOut) in
      let cstm_bufOut = Csexpr fun_call_buffOut in
      cstm_bufOut::acc
    ) [] bufferOutput in

    (* Output: list of statements, the order matters *)
    [cstm_stepC] @ lcstm_stepD
  end


(** Create the statement dest = c where c = v^n^m... *)
let rec create_affect_const var_env (dest : clhs) c =
  match c.se_desc with
    | Svar ln ->
        let se = begin
          let cDec = find_const ln in
          match cDec.Signature.c_value with
            | None -> Types.mk_static_exp cDec.Signature.c_type (Svar ln)
            | Some cval -> Static.simplify QualEnv.empty cval
        end in
        create_affect_const var_env dest se
    | Sarray_power(c, n_list) ->
        let rec make_loop power_list replace = match power_list with
          | [] -> dest, replace
          | p :: power_list ->
            let x = gen_symbol () in
            let e, replace =
              make_loop power_list
                        (fun y -> [Cfor(x, Cconst (Ccint 0), cexpr_of_static_exp p, replace y)]) in
            let e =  (CLarray (e, Cvar x)) in
            e, replace
        in
        let e, b = make_loop n_list (fun y -> y) in
        b (create_affect_const var_env e c)
    | Sarray cl ->
        let create_affect_idx c (i, affl) =
          let dest = CLarray (dest, Cconst (Ccint i)) in
            (i - 1, create_affect_const var_env dest c @ affl)
        in
          snd (List.fold_right create_affect_idx cl (List.length cl - 1, []))
    | Srecord f_se_list ->
        let affect_field affl (f, se) =
          let dest_f = CLfield (dest, f) in
            (create_affect_const var_env dest_f se) @ affl
        in
          List.fold_left affect_field [] f_se_list
    | _ -> [Caffect (dest, cexpr_of_static_exp c)]

(** [cstm_of_act obj_env mods act] translates the Obj action [act] to a list of
    C statements, using the association list [obj_env] to map object names to
    class names.  *)
let rec cstm_of_act out_env var_env obj_env act =
  match act with
      (* Cosmetic : cases on boolean values are converted to if statements. *)
    | Acase (c, [({name = "true"}, te); ({ name = "false" }, fe)])
    | Acase (c, [({name = "false"}, fe); ({ name = "true"}, te)]) ->
        let cc = cexpr_of_exp out_env var_env c in
        let cte = cstm_of_act_list out_env var_env obj_env te in
        let cfe = cstm_of_act_list out_env var_env obj_env fe in
        [Cif (cc, cte, cfe)]
    | Acase (c, [({name = "true"}, te)]) ->
        let cc = cexpr_of_exp out_env var_env c in
        let cte = cstm_of_act_list out_env var_env obj_env te in
        let cfe = [] in
        [Cif (cc, cte, cfe)]
    | Acase (c, [({name = "false"}, fe)]) ->
        let cc = Cuop ("!", (cexpr_of_exp out_env var_env c)) in
        let cte = cstm_of_act_list out_env var_env obj_env fe in
        let cfe = [] in
        [Cif (cc, cte, cfe)]


    (* Translation of case into a C switch statement is simple enough: we
       just recursively translate obj expressions and statements to
       corresponding C constructs, and cautiously "shortnamize"
       constructor names. *)
    | Acase (e, cl) ->
        (* [ccl_of_obccl] translates an Obc clause to a C clause. *)
        let ccl =
          List.map
            (fun (c,act) -> cname_of_qn c,
               cstm_of_act_list out_env var_env obj_env act) cl in
        [Cswitch (cexpr_of_exp out_env var_env e, ccl)]

    | Ablock b ->
        cstm_of_act_list out_env var_env obj_env b

    (* For composition of statements, just recursively apply our
       translation function on sub-statements. *)
    | Afor ({ v_ident = x }, i1, i2, act) ->
        [Cfor(name x, cexpr_of_exp out_env var_env i1,
              cexpr_of_exp out_env var_env i2,
              cstm_of_act_list out_env var_env obj_env act)]

    (* Translate constant assignment *)
    | Aassgn (vn, { e_desc = Eextvalue { w_desc = Wconst c }; }) ->
        let vn = clhs_of_pattern out_env var_env vn in
        create_affect_const var_env vn c

    (* Purely syntactic translation from an Obc local variable to a C
       local one, with recursive translation of the rhs expression. *)
    | Aassgn (vn, e) ->
        let vn = clhs_of_pattern out_env var_env vn in
        let ty = assoc_type_lhs vn var_env in
        let ce = cexpr_of_exp out_env var_env e in
        create_affect_stm vn ce ty

    (* Our Aop marks an operator invocation that will perform side effects. Just
       translate to a simple C statement. *)
    | Aop (op_name, args) ->
        [Csexpr (cop_of_op out_env var_env op_name args)]

    (* Reinitialization of an object variable, extracting the reset
       function's name from our environment [obj_env]. *)
    | Acall (name_list, o, Mreset, args) ->
        assert_empty name_list;
        assert_empty args;
        let on = obj_ref_name o in
        let obj = assoc_obj on obj_env in
        let classn = cname_of_qn obj.o_class in
        let field = Cfield (Cderef (Cvar "self"), local_qn (name on)) in
        (match o with
          | Oobj _ ->
              [Csexpr (Cfun_call (classn ^ "_reset", [Caddrof field]))]
          | Oarray (_, pl) ->
              let rec mk_loop pl field = match pl with
                | [] ->
                    [Csexpr (Cfun_call (classn ^ "_reset", [Caddrof field]))]
                | p::pl ->
                    mk_loop pl (Carray(field, cexpr_of_pattern out_env var_env p))
              in
                 mk_loop pl field
        )

    (* Step functions applications can return multiple values, so we use a
       local structure to hold the results, before allocating to our
       variables. *)
    | Acall (outvl, objn, Mstep, el) ->
      let args = cexprs_of_exps out_env var_env el in
      let outvl = clhs_list_of_pattern_list out_env var_env outvl in
      generate_function_call out_env var_env obj_env None outvl objn args

    | Acall (outvl, objn, Mkernel ocl, el) ->
      let args = cexprs_of_exps out_env var_env el in
      let outvl = clhs_list_of_pattern_list out_env var_env outvl in
      generate_kernel_call out_env var_env obj_env ocl outvl objn args

    | Acall (_, _, Mthread _, _) ->
      failwith "cgen::cstm_of_act : there should not have any direct call to a thread function."

    | Acall (outvl, objn, Mother name, el) ->
      let args = cexprs_of_exps out_env var_env el in
      let outvl = clhs_list_of_pattern_list out_env var_env outvl in
      generate_function_call out_env var_env obj_env (Some name) outvl objn args

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



(** {2 step() and reset() functions generation} *)

let qn_append q suffix =
  { qual = q.qual; name = q.name ^ suffix }

let build_init_mutex_decl_def cd md_init_mut =
  let var_env = [] in  (* Method only contains Aop and extval mem => no need for var env here? *)
  let body_init_mut = cstm_of_act_list IdentSet.empty var_env cd.cd_objs md_init_mut.m_body in

  let init_mut_def = Cfundef {
    C.f_name = Posixprep.name_init_mutex_func;
    f_retty = Cty_void;
    f_args = [("self", Cty_ptr (Cty_id (qn_append cd.cd_name "_mem")))];
    f_body = {
      var_decls = [];
      block_body = body_init_mut;
    }
  } in
  let init_mut_decl = C.cdecl_of_cfundef init_mut_def in
  (init_mut_decl, init_mut_def)

let build_init_sync_decl_def cd md_init_sync =
  let var_env = [] in  (* Method only contains Aop and extval mem => no need for var env here? *)
  let body_init_mut = cstm_of_act_list IdentSet.empty var_env cd.cd_objs md_init_sync.m_body in
  
  let init_sync_def = Cfundef {
    C.f_name = Posixprep.name_init_sync_counter_func;
    f_retty = Cty_void;
    f_args = [("self", Cty_ptr (Cty_id (qn_append cd.cd_name "_mem")))];
    f_body = {
      var_decls = [];
      block_body = body_init_mut;
    }
  } in
  let init_sync_decl = C.cdecl_of_cfundef init_sync_def in
  (init_sync_decl, init_sync_def)

let build_thread_decl_def cd mdthr =
  let numthr = match mdthr.Obc.m_name with
    | Mthread num -> num
    | _ -> failwith "Internal error: non-thread method given to build_thread_decl_def"
  in

  let var_env = List.map cvar_of_vd cd.cd_mems in
  let (body_thr : C.cstm list) = cstm_of_act_list IdentSet.empty var_env cd.cd_objs mdthr.m_body in

  (* Adding the final return statement *)
  let (ret_stm : C.cstm) = Creturn (Cconst (Ctag "NULL")) in
  let body_thr = body_thr @ [ret_stm] in

  let thr_def = Cfundef {
    C.f_name = Posixprep.get_name_thread numthr;
    f_retty = Cty_ptr Cty_void;
    f_args = [ ("self", Cty_ptr (Cty_id (qn_append cd.cd_name "_mem"))) ];
    f_body = {
      var_decls = [];                 (* All variables are shared and outside *)
      block_body = body_thr;
    }
  } in
  let thr_decl = C.cdecl_of_cfundef thr_def in
  (thr_decl, thr_def)



(** Builds the argument list of step function*)
let step_fun_args n md =
  let args = inputlist_of_ovarlist md.m_inputs in
  let out_arg =
    if (!Compiler_options.cg_outlist) then
      outputlist_of_ovarlist md.m_outputs
    else
      [("_out", Cty_ptr (Cty_id (qn_append n "_out")))] in
  let context_arg =
    if is_stateful n then
      [("self", Cty_ptr (Cty_id (qn_append n "_mem")))]
    else
      []
  in
    if (!Compiler_options.cg_memfirst) then
      context_arg @ args @ out_arg
    else
      args @ out_arg @ context_arg


(** [fun_def_of_step_fun name obj_env mods sf] returns a C function definition
    [name ^ "_out"] corresponding to the Obc step function [sf]. The object name
    <-> class name mapping [obj_env] is needed to translate internal steps and
    reset calls. A step function can have multiple return values, whereas C does
    not allow such functions. When it is the case, we declare a structure with a
    field by return value. *)
let fun_def_of_step_fun n obj_env mem objs md =
  let fun_name = (cname_of_qn n) ^ "_step" in
  (* Its arguments, translating Obc types to C types and adding our internal
      memory structure. *)
  let args = step_fun_args n md in

  (* Out vars for function calls *)
  let out_vars =
    if (!Compiler_options.cg_outlist) then
      [] (* No output structure => does not need to manage those of the called node *)
    else
      unique
        (List.map (fun obj -> out_var_name_of_objn (cname_of_qn obj.o_class),
                     Cty_id (qn_append obj.o_class "_out"))
          (List.filter (fun obj -> not (is_op obj.o_class)) 
          (List.filter (fun obj -> not (Modules.check_kernel obj.o_class))
          objs))) in

  (* The body *)
  let mems = List.map cvar_of_vd (mem@md.m_outputs) in
  let var_env = args @ mems @ out_vars in
  let out_env =
    if (!Compiler_options.cg_outlist) then
      IdentSet.empty (* No need for specialized output var inside the step function *)
    else
      List.fold_left
        (fun out_env vd -> IdentSet.add vd.v_ident out_env)
        IdentSet.empty
        md.m_outputs
  in
  let body = cstm_of_act_list out_env var_env obj_env md.m_body in

  Cfundef {
    C.f_name = fun_name;
    f_retty = Cty_void;
    f_args = args;
    f_body = {
      var_decls = out_vars;
      block_body = body
    }
  }


(* This one just translates the class name to a struct name following the
    convention we describe in mem_decl_of_class_def. *)
let struct_field_of_obj_dec l od =
  if is_stateful od.o_class then
    let ty = Cty_id (qn_append od.o_class "_mem") in
    let ty = match od.o_size with
      | Some nl ->
        let rec mk_idx nl = match nl with
          | [] -> ty
          | n::nl -> Cty_arr (int_of_static_exp n, mk_idx nl)
        in
          mk_idx nl
      | None -> ty in
      (name od.o_ident, ty)::l
  else
    l

(** [mem_decl_of_class_def cd] returns a declaration for a C structure holding
    internal variables and objects of the Obc class definition [cd]. *)
let mem_decl_of_class_def cd =
  if is_stateful cd.cd_name then (
    (* Fields corresponding to normal memory variables. *)
    let mem_fields = List.map cvar_of_vd cd.cd_mems in
    (* Fields corresponding to object variables. *)
    let obj_fields = List.fold_left struct_field_of_obj_dec [] cd.cd_objs in
      [Cdecl_struct ((cname_of_qn cd.cd_name) ^ "_mem",
                     mem_fields @ obj_fields)]
  ) else
    []

let out_decl_of_class_def cd =
  (* Fields corresponding to output variables. *)
  let step_m = find_step_method cd in
  let out_fields = List.map cvar_of_vd step_m.m_outputs in
    [Cdecl_struct ((cname_of_qn cd.cd_name) ^ "_out", out_fields)]

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
    C.f_name = (cname_of_qn cd.cd_name) ^ "_reset";
    f_retty = Cty_void;
    f_args = [("self", Cty_ptr (Cty_id (qn_append cd.cd_name "_mem")))];
    f_body = {
      var_decls = [];
      block_body = body;
    }
  }


let debug_pthread = false

(* Generation of the main class for pthread parallel CG *)
let cdefs_and_cdecls_of_class_def_pthread (cd:Obc.class_def) =

  (* DEBUG *)
  if (debug_pthread) then
    Format.fprintf (Format.formatter_of_out_channel stdout)
      "~> Entering cdefs_and_cdecls_of_class_def_pthread\n@?";

  Idents.enter_node cd.cd_name;

  (* Get the different methods of cd
    (reset not needed, there is already a fun in Obc_utils that works) *)
  let extract_methods_pthread cd =
    let md_init_mut = try
      List.find (fun md -> match md.Obc.m_name with
        | Obc.Mother str -> (str=Posixprep.name_init_mutex_func)
        | _ -> false
      ) cd.cd_methods
      with Not_found -> failwith "Cgen : method for init_mutex not found in main class."
    in
    let md_init_sync = try
      List.find (fun md -> match md.Obc.m_name with
        | Mother str -> (str=Posixprep.name_init_sync_counter_func)
        | _ -> false
      ) cd.cd_methods
      with Not_found -> failwith "Cgen : method for init_mutex not found in main class."
    in
    let lmd_thread = List.filter (fun md -> match md.Obc.m_name with
      | Mthread _ -> true
      | _ -> false
    ) cd.cd_methods in
    (md_init_mut, md_init_sync, lmd_thread)
  in
  let (md_init_mut, md_init_sync, lmd_thread) = extract_methods_pthread cd in

  let mem_fields = List.map cvar_of_vd cd.cd_mems in
  let obj_fields = List.fold_left struct_field_of_obj_dec [] cd.cd_objs in
  let memvardecl = [Cdecl_struct ((cname_of_qn cd.cd_name) ^ "_mem",
                       mem_fields @ obj_fields)] in

  (* DEBUG *)
  if (debug_pthread) then
    Format.fprintf (Format.formatter_of_out_channel stdout)
      "~> cdefs_and_cdecls_of_class_def_pthread : memory structure done!\n@?";

  (* Building declarations/definitions *)
  let (init_mut_decl, init_mut_def) = build_init_mutex_decl_def cd md_init_mut in
  let (init_sync_decl, init_sync_def) = build_init_sync_decl_def cd md_init_sync in

  (* DEBUG *)
  if (debug_pthread) then
    Format.fprintf (Format.formatter_of_out_channel stdout)
      "~> cdefs_and_cdecls_of_class_def_pthread : init functions done!\n@?";


  let reset_def = reset_fun_def_of_class_def cd in
  let reset_decl = C.cdecl_of_cfundef reset_def in

  (* DEBUG *)
  if (debug_pthread) then
    Format.fprintf (Format.formatter_of_out_channel stdout)
      "~> cdefs_and_cdecls_of_class_def_pthread : reset function done!\n@?";

  let (lpthread_decl, lpthread_def) = List.fold_left (fun (ldecl_acc, ldef_acc) mdthr ->
    let (ndecl, ndef) = build_thread_decl_def cd mdthr in
    (ndecl::ldecl_acc, ndef::ldef_acc)
  ) ([],[]) lmd_thread in

  (* DEBUG *)
  if (debug_pthread) then
    Format.fprintf (Format.formatter_of_out_channel stdout)
      "~> cdefs_and_cdecls_of_class_def_pthread : all built!\n@?";

  (* Assemble the result *)
  (* Note: reset always added, but if not stateful, it is empty *)
  let ldecl = init_mut_decl :: init_sync_decl :: reset_decl ::lpthread_decl in
  let ldef = init_mut_def :: init_sync_def :: reset_def :: lpthread_def in

  let ldecl = List.rev_append memvardecl ldecl in

  (* Return the list of function declaration (for .h) and definition (for .c) *)
  ldecl, ldef



(** [cdecl_and_cfun_of_class_def cd] translates the class definition [cd] to
    a C program. *)
let cdefs_and_cdecls_of_class_def cd =
  let b_pthread_CG = if (!Posixprep.rnum_thread>0) then
      (* Is it the main class? *)
      let n = (Misc.assert_1 !Compiler_options.mainnode).name in
      (cd.cd_name.name = n)
    else
      false
  in

  if (b_pthread_CG) then
    (* Posix parallel CG for the main system has a different structure (pthread-based) *)
    cdefs_and_cdecls_of_class_def_pthread cd
  else begin
    (* We keep the state of our class in a structure, holding both internal
       variables and the state of other nodes. For a class named ["cname"], the
       structure will be called ["cname_mem"]. *)
    Idents.enter_node cd.cd_name;

    let step_m = find_step_method cd in
    let memory_struct_decl = mem_decl_of_class_def cd in
    let out_struct_decl =
      if (!Compiler_options.cg_memfirst) then [] else
        out_decl_of_class_def cd
    in
    let step_fun_def = fun_def_of_step_fun cd.cd_name
      cd.cd_objs cd.cd_mems cd.cd_objs step_m in
    (* C function for resetting our memory structure. *)
    let reset_fun_def = reset_fun_def_of_class_def cd in
    let res_fun_decl = cdecl_of_cfundef reset_fun_def in
    let step_fun_decl = cdecl_of_cfundef step_fun_def in
    let (decls, defs) =
      if is_stateful cd.cd_name then
        ([res_fun_decl; step_fun_decl], [reset_fun_def; step_fun_def])
      else
        ([step_fun_decl], [step_fun_def]) in

    memory_struct_decl @ out_struct_decl @ decls, defs
  end

(** {2 Type translation} *)

(** Translates an Obc type declaration to its C counterpart. *)
let cdefs_and_cdecls_of_type_decl otd =
  let name = cname_of_qn otd.t_name in
  match otd.t_desc with
    | Type_abs -> [], [] (*assert false*)
    | Type_alias ty ->
      [], [Cdecl_typedef (ctype_of_otype ty, name)]
    | Type_enum nl ->
        let of_string_fun = Cfundef
          { C.f_name = name ^ "_of_string";
            f_retty = Cty_id otd.t_name;
            f_args = [("s", Cty_ptr Cty_char)];
            f_body =
              { var_decls = [];
                block_body =
                  let gen_if t =
                    let t = cname_of_qn t and t' = t.name in
                    let funcall = Cfun_call ("strcmp", [Cvar "s";
                                                        Cconst (Cstrlit t')]) in
                    let cond = Cbop ("==", funcall, Cconst (Ccint 0)) in
                    Cif (cond, [Creturn (Cconst (Ctag t))], []) in
                  map gen_if nl; }
          }
        and to_string_fun = Cfundef
          { C.f_name = "string_of_" ^ name;
            f_retty = Cty_ptr Cty_char;
            f_args = [("x", Cty_id otd.t_name); ("buf", Cty_ptr Cty_char)];
            f_body =
              { var_decls = [];
                block_body =
                  let gen_clause t =
                    let t = cname_of_qn t and t' = t.name in
                    let fun_call =
                      Cfun_call ("strcpy", [Cvar "buf";
                                            Cconst (Cstrlit t')]) in
                    (t, [Csexpr fun_call]) in
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
  let v = match cd.Obc.c_value with
    | None -> None
    | Some v -> Some (cexpr_of_static_exp v)
  in
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
  | _ -> String.uncapitalize_ascii (modul_to_string m)

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
    List.split (List.map cdefs_and_cdecls_of_class_def classes) in
  let decls = List.concat decls
  and defs = List.concat defs in

  let filename_types = name ^ "_types" in
  let cdefs_and_cdecls = List.map cdefs_and_cdecls_of_program_decl prog.p_desc in

  let (cty_defs, cty_decls) = List.split cdefs_and_cdecls in
  let ldefaultheader = "stdbool"::"assert"::"pervasives"::[] in
  let ldefaultheader = if (!Compiler_options.opencl_cg) then
      ldefaultheader @ ["hept_opencl"]
    else
      ldefaultheader
  in
  let types_h = (filename_types ^ ".h",
                 Cheader (ldefaultheader @ dependencies_types,
                          List.concat cty_decls)) in
  let types_c = (filename_types ^ ".c", Csource (concat cty_defs)) in

  let header =
    (name ^ ".h", Cheader (filename_types :: dependencies, decls))
  and source =
    (name ^ ".c", Csource defs) in
  [header; source; types_h; types_c]


let interface_header name i =
  let dependencies = ModulSet.elements (Obc_utils.Deps.deps_interface i) in
  let dependencies = List.map header_of_module dependencies in

  let cdefs_and_cdecls = List.map cdefs_and_cdecls_of_interface_decl i.i_desc in

  let (cty_defs, cty_decls) = List.split cdefs_and_cdecls in
  let ldefaultheader = "stdbool"::"assert"::"pervasives"::[] in
  let ldefaultheader = if (!Compiler_options.opencl_cg) then
      ldefaultheader @ ["hept_opencl"]
    else
      ldefaultheader
  in
  let types_h = (name ^ ".h",
                 Cheader (ldefaultheader @ dependencies,
                          List.concat cty_decls)) in
  let types_c = (name ^ ".c", Csource (concat cty_defs)) in

  [types_h; types_c]
