(*******************************************************************************
 * Fiabilité et Sûreté de Fonctionnement
 * Copyright (c) 2013, 2014 Institut de Recherche Technologique SystemX
 * All rights reserved.
 *******************************************************************************)


(* TODO list
   1/ ensure that there is a correct mapping between the C function names
   wheter they are generated with lopth target or c target.
   2/ transform constant function application into LoPhT equivalent.
   3/ ensure that the produced file is correct, even if it implies to
   generate dummy symbols (function, variable, etc. since these table must
   not be empty) or raise exceptions.
   4/ check int, float and string coding
   *)


(* Overall description of the compilation from MiniLS to CG (Clocked Graphs)
 * 
 * This algorithm translate a MiniLS program to CG. One node without inputs
 * must be given as the root of the program. We could generate some function
 * to fetch input, but it's probably best to let the programmer choose how
 * these inputs are provided. This way, the program can be run and not
 * necessarily simulated with user inputs.
 *
 * There is no annotation yet to choose which nodes are the tasks to be
 * scheduled. (I hope there will be one some day) We inline all node calls
 * where there is the "inlined" key word. These may have already been
 * inlined in the heptagon pass, but not if they come from different
 * files. (Cross file inlining is not supported right now) At the end, the
 * remaining non-inlined calls are the tasks we keep. For each call, we
 * build a cg "block", and the cg "function" it instanciate. (If there are
 * two calls to the same function, we generate it only once) We also extract
 * the dataflow graph between these tasks, with all the clock information.
 * 
 * The compilation is separated in two passes. During the first pass, we
 * convert the MiniLS program to its CG equivalent, but without binding
 * inputs to the block, or assigning clocks. Instead, we collect a set of
 * variable "bindings" which are structures with a mutable field telling
 * to which variable each input port or clock expression is bound.
 * Initially, all those bindings have the value "Unbound". At the end
 * of the first pass, all the bindings must have changed to either
 * Alias, Merge or Defined_variable. This forms a DAG which will be
 * traversed during the second pass. To build this, we use a
 * "local environnement" which associate heptagon local variables and
 * parameters to a binding. 
 *
 * The second pass will resolve input and clock bindings. (i.e. It will
 * complete the clock graph such that each block has the appropriate
 * input variables and clocks. All the complexity is concentrated in the
 * two functions "resolve_clock" and "resolve_binding". These two function
 * are mutually recursive. The first one takes a "clock binding" and
 * resolves it, creating the corresponding lopht clock expression and adding
 * it to the clocked graph if necessary. The second function takes a
 * "variable binging" and resolves it and the associated clock.
 *)



open Minils
open Cg
open Cg_cwrapper


exception Not_implemented

let qname_to_id = C.cname_of_qn
let name_to_id = C.cname_of_name
let ident_to_id ident = C.cname_of_name (Idents.name ident)


module StringSet = Set.Make (struct type t = string let compare = Pervasives.compare end)
module StringMap = Map.Make (struct type t = string let compare = Pervasives.compare end)
module TyEnv = Map.Make (struct type t = Types.ty let compare = Pervasives.compare end)
module QualEnv = Names.QualEnv
module VarEnv = Idents.Env

(* Intermediate representation of variables between the first and the second pass *)
type intermediate_variable = {
  iv_ident : Idents.var_ident;
  mutable iv_binding : variable_binding;
}
and variable_binding =
  | Unbound
  | Alias of intermediate_variable
  | Merge of intermediate_variable * (Names.constructor_name * variable_binding) list
  | MultiMerge of intermediate_variable list * (Names.constructor_name * variable_binding) list
  | Defined_Variable of variable

(* Intermediate representation of clocks *)
and clock_binding =
  | PrimitiveClock
  | DerivedClock of clock_binding * Names.constructor_name * intermediate_variable
  | UnionClock of clock_binding list
  | InterClock of clock_binding list


(* Local environments associating an intermediate variable to each heptagon local variable and input and output parameter *)
type local_environment = intermediate_variable VarEnv.t


module ClEnv = Map.Make (struct
    type t = clk_exp
    let lex_compare f1 f2 (a1, a2) (b1, b2) =
      let c = f1 a1 b1 in
      if c = 0 then f2 a2 b2 else c
  
    let compare_var v1 v2 =
      v2.var_index - v1.var_index 
   
    let compare_clk c1 c2 =
      c2.clk_index - c1.clk_index 
   
    let compare_val_exp ve1 ve2 = match ve1, ve2 with
      | Variable v1, Variable v2 -> compare_var v1 v2
      | _, _ -> assert false

    let rec compare_exp e1 e2 = match e1, e2 with
      | Predicate ve1, Predicate ve2 -> compare_val_exp ve1 ve2
      | Predicate _, _ -> 1
      | _, Predicate _ -> -1
      | Not e1, Not e2 -> compare_exp e1 e2
      | _, _ -> assert false

    let rec compare e1 e2 = match e1, e2 with
      | BaseClock c1, BaseClock c2 -> compare_clk c1 c2
      | BaseClock _, _ -> 1
      | _, BaseClock _ -> -1
      | Union (e1, f1), Union (e2, f2) -> lex_compare compare compare (e1, f1) (e2, f2)
      | Union _, _ -> 1
      | _, Union _ -> -1
      | Intersection (e1, f1), Intersection (e2, f2) -> lex_compare compare compare (e1, f1) (e2, f2)
      | Intersection _, _ -> 1
      | _, Intersection _ -> -1
      | Test (c1, e1), Test (c2, e2) -> lex_compare compare compare_exp (c1, e1) (c2, e2)  
      | _, _ -> assert false (* Any other case is not used in the current implementation *)
  end)


type cg_environment = {
  (* Association of Heptagon type expression and symbols to cg equivalent *)
  mutable type_bindings : ty TyEnv.t;
  mutable constant_bindings : const QualEnv.t;
  mutable function_bindings : (func*(func * ty * int ref) option) QualEnv.t;
  (* Bindings produced at the end of the first pass which must be resolved *)
  mutable input_bindings : (block * clock_binding * arg_list * variable_binding list) list;
  (* Associate cg clock expressions to cg clocks to detects double definitions *)
  mutable clock_definitions : clk ClEnv.t;
  (* Generated C functions *)
  mutable operators : func StringMap.t;
  (* Index used to generate unique name for constants *)
  mutable last_constant_index : int;
  (* Primitive Clock *)
  primitive_clock : clk;
  (* Clocked graph being produced (with all lists reversed) *)
  cg : clocked_graph; 
  (* Generated C files *)
  mutable cdependencies : string list;
  mutable cheader : C.cdecl list;
  mutable csource : C.cdef list;
}


(* Module handling through callgraph *)

(* .epo files can be handled by mls/callgraph. We don't need the full callgraph though.
   We'll just use the i/o functions and the database of loaded modules. For static
   parameters, we'll probably need a full callgraph anyway, so... it's only temporary  *)



let get_node_by_qname qname =
  let hnode = Callgraph.node_by_longname qname in
  (* Callgraph doesn't open all used interface, but in our case, we have to *)
  let p = Names.ModulEnv.find qname.Names.qual Callgraph.info.Callgraph.opened in 
  List.iter Modules.open_module p.p_opened;
  hnode


(* Output of C file, mostly like C.output_cfile but without dir *)

let output_cfile filename cfile_desc =
  if !Compiler_options.verbose then
    Format.printf "C-NG generating %s@." filename;
  let out = open_out filename in
  let fmt = Format.formatter_of_out_channel out in
  C.pp_cfile_desc fmt filename cfile_desc;
  Format.pp_print_flush fmt ();
  close_out out


(* First pass, neither bind input parameters nor clocks *)

let int_of_static_exp se = Static.int_of_static_exp QualEnv.empty se 

let rec find_structure_def = function
  | Types.Tid qn ->
      begin match Modules.find_type qn with
      | Signature.Talias ty -> find_structure_def ty
      | Signature.Tstruct structure -> structure
      | _ -> raise Not_found
      end
  | _ -> raise Not_found 


let rec translate_typename = function
  | Types.Tid type_name ->
      qname_to_id type_name
  | Types.Tarray (base_ty, size_exp) ->
      let size = int_of_static_exp size_exp in
      "array_" ^ translate_typename base_ty ^ "_" ^ (string_of_int size) 
  | Types.Tprod _ ->
      raise Not_implemented
  | Types.Tinvalid ->
      assert false


let translate_ty genv ty =
  let ty = Static.simplify_type QualEnv.empty ty in
  try
    TyEnv.find ty genv.type_bindings
  with Not_found ->
    let gty = add_ty genv.cg (translate_typename ty) SimpleType in
    genv.type_bindings <- TyEnv.add ty gty genv.type_bindings ;
    gty

let translate_const_ref genv const_name ty =
  try
    QualEnv.find const_name genv.constant_bindings
  with Not_found ->
    let cst_ty = translate_ty genv ty
    and cst_id = (qname_to_id const_name) in
    let gconst = add_constant genv.cg cst_id cst_ty ExternalConst in
    genv.constant_bindings <- QualEnv.add const_name gconst genv.constant_bindings ;
    gconst

let add_cdef genv cdef =
  genv.csource <- cdef :: genv.csource ;
  genv.cheader <- (C.cdecl_of_cfundef cdef) :: genv.cheader

let build_operator genv op_name fun_inputs fun_outputs cdef = 
  try
    StringMap.find op_name genv.operators
  with Not_found ->
    let gfunc = add_function genv.cg op_name fun_inputs fun_outputs in
    genv.operators <- StringMap.add op_name gfunc genv.operators ;
    add_cdef genv cdef ;
    gfunc

let build_array_power genv ty =
  let ty_elt, size = match ty with
  | Types.Tarray (ty_elt, size) -> ty_elt, int_of_static_exp size
  | _ -> assert false
  in 
  let op_name = ("fill_" ^ translate_typename ty)
  and fun_inputs = [("src", translate_ty genv ty_elt)] 
  and fun_outputs = [("dest", translate_ty genv ty)] in 
  let cdef = build_c_array_power ty ty_elt size op_name in
  let gfunc = build_operator genv op_name fun_inputs fun_outputs cdef in
  gfunc

let build_array_constructor genv ty =
  let ty_elt, size = match ty with
    | Types.Tarray (ty, size) -> ty, int_of_static_exp size
    | _ -> assert false
  in
  let rec build_args r = function
    | 0 -> r
    | i -> build_args (("i" ^ string_of_int i, translate_ty genv ty_elt) :: r) (i -1)
  in
  let op_name = ("construct_" ^ translate_typename ty)
  and fun_inputs = build_args [] size 
  and fun_outputs = [("o", translate_ty genv ty)] in
  let cdef = build_c_array_constructor ty ty_elt size op_name in
  let _gfunc = build_operator genv op_name fun_inputs fun_outputs cdef in
  raise Not_implemented (* Need to generated array initialisation in C *)

let build_struct_constructor genv ty =
  let structure_def = find_structure_def ty in
  let field_to_arg { Signature.f_name ; f_type } = qname_to_id f_name, translate_ty genv f_type in
  let op_name = ("construct_" ^ translate_typename ty)
  and fun_inputs = List.map field_to_arg structure_def
  and fun_outputs = [("o", translate_ty genv ty)] in
  let cdef = build_c_struct_constructor ty structure_def op_name in
  let gfunc = build_operator genv op_name fun_inputs fun_outputs cdef in
  gfunc

let add_anonymous_constant genv cst_ty cst_def =
  genv.last_constant_index <- genv.last_constant_index + 1;
  let cst_name = "const_" ^ string_of_int genv.last_constant_index in
  add_constant genv.cg cst_name cst_ty cst_def

let rec translate_static_exp genv static_exp =
  let ty = static_exp.Types.se_ty in
  match static_exp.Types.se_desc with
  | Types.Svar const_name -> 
      let const = translate_const_ref genv const_name ty in
      NamedConst const
  | Types.Sint i -> Integer i
  | Types.Sfloat f -> Float f
  | Types.Sbool b -> Boolean b
  | Types.Sstring s -> String s

  | Types.Sconstructor _e -> raise Not_implemented
  | Types.Sfield _field_name -> raise Not_implemented 
  | Types.Stuple _l -> raise Not_implemented
  | Types.Sop (_fun_name, _parameters) -> raise Not_implemented

  | Types.Sarray_power (value, _sizes) ->
      let gfunc = build_array_power genv ty
      and inputs = [ translate_static_exp genv value ] in
      let cst_desc = InitFunctionConst (gfunc, inputs)
      and cst_ty = snd (List.hd gfunc.fun_outputs) in
      NamedConst (add_anonymous_constant genv cst_ty cst_desc) 

  | Types.Sarray values ->
      let gfunc = build_array_constructor genv ty
      and inputs = List.map (translate_static_exp genv) values in
      let cst_desc = InitFunctionConst (gfunc, inputs)
      and cst_ty = snd (List.hd gfunc.fun_outputs) in
      NamedConst (add_anonymous_constant genv cst_ty cst_desc) 

  | Types.Srecord l ->
      let structure_def = find_structure_def ty in
      let fields, values = List.split l in
      let values = List.map (translate_static_exp genv) values in
      let definition = List.fold_right2 QualEnv.add fields values QualEnv.empty in
      let field_to_input { Signature.f_name } = QualEnv.find f_name definition in
      let inputs = List.map field_to_input structure_def
      and gfunc = build_struct_constructor genv ty in
      let cst_desc = InitFunctionConst (gfunc, inputs)
      and cst_ty = snd (List.hd gfunc.fun_outputs) in
      NamedConst (add_anonymous_constant genv cst_ty cst_desc) 


let build_block genv clkb block_id block_fun fun_inputs fun_outputs input_bindings =
  let block_clock = genv.primitive_clock in
  let gblock = add_block genv.cg block_clock block_id block_fun in
  let bind_output (port_id, var_type) =
    let gvar = add_variable genv.cg var_type port_id gblock
    in Defined_Variable gvar, {
      output_port_name = port_id;
      output_port_var = gvar;
    }
  in
  let targets, block_outputs = List.split (List.map bind_output fun_outputs) in 
  gblock.block_outputs <- block_outputs;
  genv.input_bindings <- (gblock, clkb, fun_inputs, input_bindings) :: genv.input_bindings;
  targets

let build_block_from_func gfunc genv clkb input_bindings =
    let block_fun = FunBlock gfunc
    and block_id = Some gfunc.fun_id
    and fun_outputs = gfunc.fun_outputs
    and fun_inputs = gfunc.fun_inputs in
    build_block genv clkb block_id block_fun fun_inputs fun_outputs input_bindings

let build_block_fom_const genv gconst gty =
  let block_id = match gconst with
    | NamedConst const -> Some const.cst_id
    | _ -> None
  and block_fun = ConstBlock gconst
  and fun_inputs = []
  and fun_outputs = [("c", gty)]
  and input_bindings = []
  in
  begin match build_block genv PrimitiveClock block_id block_fun fun_inputs fun_outputs input_bindings with
    | [ b ] -> b
    | _ -> assert false (* Only one output port is specified *)
  end

let translate_const genv static_exp =
  let gconst = translate_static_exp genv static_exp
  and gty = translate_ty genv static_exp.Types.se_ty
  in
  build_block_fom_const genv gconst gty

let translate_var lenv var_ident =
   VarEnv.find var_ident lenv

let rec translate_ck lenv = function
  | Clocks.Cbase -> PrimitiveClock
  | Clocks.Cvar _ -> raise Not_implemented
  | Clocks.Con (base_ck, constructor_name, var_ident) ->
      DerivedClock (translate_ck lenv base_ck, constructor_name, translate_var lenv var_ident)

let rec translate_extvalue genv lenv extvalue =
  match extvalue.w_desc with
    | Wconst static_exp -> translate_const genv static_exp
    | Wvar var_ident -> Alias (translate_var lenv var_ident )
    | Wfield (_extvalue, _field_name) -> raise Not_implemented (* Build a selector block *)
    | Wwhen (extvalue, _constructor_name, _var_ident) -> translate_extvalue genv lenv extvalue 
    | Wreinit (_extvalue1, _extvalue2) -> raise Not_implemented

let translate_arg genv param =
  let open Signature in
  if param.a_linearity <> Linearity.Ltop || param.a_clock <> Cbase then
    raise Not_implemented;
  let name = match param.a_name with
    | Some name -> name
    | None -> assert false
  in
  name_to_id name, translate_ty genv param.a_type

let translate_function genv name hnode =
  try
    QualEnv.find name genv.function_bindings
  with Not_found ->
    let open Signature in
    let fun_id = qname_to_id name in
    let fun_inputs = List.map (translate_arg genv) hnode.node_inputs
    and fun_outputs = List.map (translate_arg genv) hnode.node_outputs in
    let fun_step_id = fun_id ^ "_wstep"
    and fun_reset_id = fun_id ^ "_wreset" in
    let fun_inputs, stateful_objects =
      if hnode.node_stateful then begin
        let mem_ty = add_ty genv.cg (fun_id ^ "_state") SimpleType in
        let mem_param = ("mem", mem_ty)
        and dummy_param = ("dummy", translate_ty genv (Types.Tid Initial.pint)) in
        let fun_inputs = fun_inputs @ [mem_param ; dummy_param] in
        let gfunc_reset = add_function genv.cg fun_reset_id [mem_param] [dummy_param] in
        fun_inputs, Some (gfunc_reset, mem_ty, ref 0)
      end else
        fun_inputs, None
    in
    let gfunc_step = add_function genv.cg fun_step_id fun_inputs fun_outputs in
    genv.function_bindings <- QualEnv.add name (gfunc_step, stateful_objects) genv.function_bindings;
    let cdefs = build_c_wrappers fun_step_id fun_reset_id name hnode in
    List.iter (add_cdef genv) cdefs ;
    (gfunc_step, stateful_objects)


let translate_fby genv lenv ck init extvalue =
  let delay_ty = translate_ty genv extvalue.w_ty in
  let init_const = match init with
    | Some static_exp -> translate_static_exp genv static_exp
    | None -> raise Not_implemented
  in
  let gdelay = {
    delay_ty;
    delay_depth = 1;
    delay_init = [ init_const ];
  }
  in
  let block_fun = DelayBlock gdelay
  and block_id = None
  and fun_inputs = [("i", delay_ty)] 
  and fun_outputs = [("o", delay_ty)]
  and input_bindings = [translate_extvalue genv lenv extvalue]
  and clkb = translate_ck lenv ck
  in
  build_block genv clkb block_id block_fun fun_inputs fun_outputs input_bindings

let translate_merge genv lenv var_ident l =
  let var = translate_var lenv var_ident
  and l' = List.map (fun (n, e) -> n, translate_extvalue genv lenv e) l
  in [ Merge (var, l') ]

let rec translate_app genv lenv reset_vars ck app inputs =
  let static_params = app.a_params
  and fun_name = match app.a_op with
    | Efun fun_name
    | Enode fun_name -> fun_name
    | _ -> raise Not_implemented
  and input_bindings = List.map (translate_extvalue genv lenv) inputs
  in
  if app.a_inlined then begin
    let hnode = get_node_by_qname fun_name in
    translate_node genv reset_vars hnode input_bindings
  end else begin
    if static_params <> [] then
      raise Not_implemented;
    let hnode = Modules.find_value fun_name in
    let gfunc_step, stateful_objects =
      translate_function genv fun_name hnode
    and step_clkb = translate_ck lenv ck in
    let input_bindings = 
      match stateful_objects with
      | Some (gfunc_reset, mem_ty, instance_count) ->
          let mem_name = qname_to_id fun_name ^ "_mem" in
          let mem_name =
            if !instance_count = 0
            then mem_name
            else mem_name ^ string_of_int !instance_count
          in
          instance_count := !instance_count + 1;
          let mem_const = add_constant genv.cg mem_name mem_ty ExternalConst in
          let mem_binding = build_block_fom_const genv (NamedConst mem_const) mem_ty in
          let reset_clkbs = List.map (fun v -> DerivedClock (step_clkb, Initial.ptrue, v)) reset_vars in
          let reset_clkb = UnionClock reset_clkbs in
          let reset_targets = build_block_from_func gfunc_reset genv reset_clkb [mem_binding] in
          let dummy_binding = 
            MultiMerge (reset_vars, [
              (Initial.ptrue, List.hd (reset_targets));
              (Initial.pfalse, translate_const genv (Initial.mk_static_int 0))])
          in input_bindings @ [mem_binding ; dummy_binding]
      | None -> input_bindings
    in
    build_block_from_func gfunc_step genv step_clkb input_bindings
  end

and translate_exp genv lenv reset_vars exp =
  match exp.e_desc with
  | Eextvalue extvalue ->
      [ translate_extvalue genv lenv extvalue ]
  | Efby (static_exp_opt, extvalue) ->
      translate_fby genv lenv exp.e_level_ck static_exp_opt extvalue
  | Eapp (app, extvalue_list, None) ->
      translate_app genv lenv reset_vars exp.e_level_ck app extvalue_list
  | Eapp (app, extvalue_list, Some reset_ident) ->
      let reset_vars = translate_var lenv reset_ident :: reset_vars in
      translate_app genv lenv reset_vars exp.e_level_ck app extvalue_list
  | Ewhen (exp, _constructor_name, _var_ident) ->
      translate_exp genv lenv reset_vars exp
  | Emerge (var_ident, l) ->
      translate_merge genv lenv var_ident l
  | Estruct _
  | Eiterator (_, _, _, _, _, _) ->
      raise Not_implemented

and translate_eq genv lenv reset_vars eq =
  let destinations = match eq.eq_lhs with
    | Evarpat var_ident -> [ var_ident ]
    | Etuplepat l ->
        List.map (function Evarpat var_ident -> var_ident | Etuplepat _ -> raise Not_implemented) l
  and sources = translate_exp genv lenv reset_vars eq.eq_rhs
  in
  let add_binding dest source =
    (VarEnv.find dest lenv).iv_binding <- source
  in
  List.iter2 add_binding destinations sources 

and translate_node genv reset_vars hnode input_bindings =
  let add_var_to_lenv binding var_dec lenv =
    let iv_ident = var_dec.v_ident in
    VarEnv.add iv_ident { iv_ident; iv_binding = binding } lenv
  in
  let extract_var_from_lenv lenv var_dec =
    (VarEnv.find var_dec.v_ident lenv).iv_binding
  in
  let lenv = VarEnv.empty in
  let lenv = List.fold_right2 add_var_to_lenv input_bindings hnode.n_input lenv in 
  let lenv = List.fold_right (add_var_to_lenv Unbound) hnode.n_local lenv in
  let lenv = List.fold_right (add_var_to_lenv Unbound) hnode.n_output lenv in
  List.iter (translate_eq genv lenv reset_vars) hnode.n_equs ;
  List.map (extract_var_from_lenv lenv) hnode.n_output
  

(* Second pass, bind input parameters and clocks *)

let rec evaluate_ivar_in_cklb ivar = function
  | PrimitiveClock -> None
  | DerivedClock (base_clkb, constructor_name, ivar') ->
      if ivar' == ivar
      then Some constructor_name
      else evaluate_ivar_in_cklb ivar base_clkb
  | _ -> assert false

let build_clk_term constructor_name (var, clock) =
  let predicate = match constructor_name with  (* Test the value against a constructor *) 
  | { Names.qual = Names.Pervasives; name = "false" } -> Not (Predicate (Variable var))
  | { Names.qual = Names.Pervasives; name = "true" } -> Predicate (Variable var)
  | _ -> raise Not_implemented
  in
  Test (BaseClock clock, predicate)

let memo_clock_exp genv clk_exp clk_dependencies =
  try
    ClEnv.find clk_exp genv.clock_definitions
  with Not_found ->
    let gclock = add_clock genv.cg (Derived clk_exp) clk_dependencies in
    genv.clock_definitions <- ClEnv.add clk_exp gclock genv.clock_definitions;
    gclock


let rec resolve_clock genv = function
  | PrimitiveClock -> genv.primitive_clock
  | clkb ->
      let clk_exp, dependencies = resolve_clock_exp genv clkb in
      memo_clock_exp genv clk_exp dependencies

and resolve_clock_exp genv = function
  | PrimitiveClock -> assert false
  | DerivedClock (base_clkb, constructor_name, ivar) ->
      let clk_dependencies = resolve_binding genv base_clkb ivar.iv_binding in
      mk_union (List.map (build_clk_term constructor_name) clk_dependencies),
      clk_dependencies
  | UnionClock l ->
      let clk_exp, dependencies = List.split (List.map (resolve_clock_exp genv) l) in
      mk_union clk_exp,
      List.fold_left (@) [] dependencies
  | InterClock l ->
      let clk_exp, dependencies = List.split (List.map (resolve_clock_exp genv) l) in
      mk_inter clk_exp,
      List.fold_left (@) [] dependencies

and resolve_binding genv clkb binding =
  (* Recursively build a list of variables with clocks. *)
  (* Clocks are built during the recursion and solved at leaves. *)
  let rec resolve clkb r = function
    | Unbound -> assert false
    | Alias (ivar) ->
        resolve clkb r ivar.iv_binding
    | Merge (ivar, l) ->
        let merge r (constr, binding) =
          match evaluate_ivar_in_cklb ivar clkb with
            | Some constr' when constr' = constr -> (* The variable is already evaluated *)
                resolve clkb r binding
            | Some _ -> (* The path is unfeasible, ignore it *)
                r
            | None ->
                resolve (DerivedClock (clkb, constr, ivar)) r binding
        in
        List.fold_left merge r l
    | MultiMerge (ivars, l) ->
        let merge r (constr, binding) =
          let clkbs = List.map (fun iv -> DerivedClock (clkb, constr, iv)) ivars in
          let derived_clkb =
            if constr = Initial.ptrue
            then UnionClock clkbs
            else InterClock clkbs
          in
          resolve derived_clkb r binding
        in
        List.fold_left merge r l

    | Defined_Variable var ->
        (var, resolve_clock genv clkb) :: r
  in
  resolve clkb [] binding


let bind_input genv ck (input_port_name, _ty) binding =
  {
    input_port_name;
    input_port_arcs = resolve_binding genv ck binding;
  }

let bind_inputs genv (block, clkb, fun_inputs, bindings) =
  block.block_clk <- resolve_clock genv clkb;
  block.block_inputs <- List.map2 (bind_input genv clkb) fun_inputs bindings


(* Initial environment *)

let build_predef_genv () =
  (* Predefined clocks and types *)
  let primitive_clock = { clk_index = 0 ; clk_id = None ; clk_desc = Primitive ; clk_dependencies = []}
  and ty_bool = { ty_index = 0 ; ty_id = "bool" ; ty_desc = PredefinedType }
  and ty_int = { ty_index = 1 ; ty_id = "int" ; ty_desc = PredefinedType } in
  let type_list = [ (Initial.pint, ty_int) ; (Initial.pbool, ty_bool) ] in {
    type_bindings = List.fold_left (fun env (n, t) -> TyEnv.add (Types.Tid n) t env) TyEnv.empty type_list;
    constant_bindings = QualEnv.empty;
    function_bindings = QualEnv.empty;
    input_bindings = [];
    clock_definitions = ClEnv.empty;
    operators = StringMap.empty;
    last_constant_index = 0;
    primitive_clock;
    cg = {
      types = List.map snd type_list ;
      functions = [] ;
      constants = [] ;
      variables = [];
      clocks = [primitive_clock];
      relations = [];
      partitions = [];
      blocks = [];
    };
    cdependencies = [];
    cheader = [];
    csource = [];
  }

let build_init_var genv =
  let va_init = begin match translate_fby genv (VarEnv.empty) Clocks.Cbase
    (Some (Types.mk_static_exp Initial.tbool (Types.Sbool true)))
    (extvalue_false Clocks.Cbase)
  with 
  | [Defined_Variable va] -> va
  | _ -> assert false
  end in
  {iv_ident = Idents.ident_of_name "init"; iv_binding = Defined_Variable va_init}


(* Extraction of the clocked graph from environment *)
 
let extract_cg genv = {
  types = List.rev genv.cg.types ;
  functions = List.rev genv.cg.functions ;
  constants = List.rev genv.cg.constants ;
  variables = List.rev genv.cg.variables ;
  clocks = List.rev genv.cg.clocks ;
  relations = List.rev genv.cg.relations ;
  partitions = List.rev genv.cg.partitions ;
  blocks = List.rev genv.cg.blocks ;
}


(* Find target node *)

let find_target_node { p_desc } =
  let name = !Compiler_options.target_node in
  if name = "" then begin
    Format.eprintf "A top level node with no input arguments must be given.@.";
    raise Errors.Error
  end;
  let node =
    try
      let desc = List.find (function Pnode n -> Names.shortname n.n_name = name | _ -> false) p_desc in
      match desc with
      | Pnode n -> n
      | _ -> assert false
    with Not_found ->
        Format.eprintf "The node %s does not exists.@." name;
        raise Errors.Error
  in
  node


(* Entry point of the translation *)

let program p =
  (* Find the target node *)
  let target_node = find_target_node p in
  if target_node.n_input <> [] then
    begin
      Format.eprintf "The top-level node must not have inputs.@.";
      raise Errors.Error
    end;

  (* Init callgrpah environement for module opening *)
  Callgraph.info.Callgraph.opened <- Names.ModulEnv.add p.p_modname p Names.ModulEnv.empty;

  (* Build the clocked graph *)
  let genv = build_predef_genv () in
  ignore (translate_node genv [build_init_var genv] target_node []) ;
  List.iter (bind_inputs genv) genv.input_bindings ;
  let cg = extract_cg genv in

  (* Open output file *)
  let basename = Compiler_utils.filename_of_name (Names.modul_to_string p.p_modname) in
  let out = open_out (basename ^ ".gc") in
  let fmt = Format.formatter_of_out_channel out in

  (* Print results *)
  Cg_printer.print_clocked_graph fmt cg ;

  (* Output C glue *)
  output_cfile (basename ^ ".h") (C.Cheader (genv.cdependencies, genv.cheader)) ;
  output_cfile (basename ^ ".c") (C.Csource genv.csource)

