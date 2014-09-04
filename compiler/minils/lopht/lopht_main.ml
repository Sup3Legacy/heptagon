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
   5/ check clock for function call and clock dependencies *)


open Minils
open Lopht_input

exception Not_implemented

let qualname_to_lopht_id = C.cname_of_qn
let name_to_lopht_id = C.cname_of_name
let ident_to_lopht_id ident = C.cname_of_name (Idents.name ident)


module TyEnv = Map.Make (struct type t = Types.ty let compare = Pervasives.compare end)
module ClEnv = Map.Make (struct type t = Clocks.ck let compare = Pervasives.compare end)
module QualEnv = Names.QualEnv
module VarEnv = Idents.Env

type hept_environment = {
  mutable hnodes : node_dec QualEnv.t;
  mutable hconsts : const_dec QualEnv.t;
  mutable htypes : type_dec QualEnv.t;
  mutable hvars : var_dec VarEnv.t;
}

type variable_binding = Alias of Idents.var_ident | Merge of Idents.var_ident * (Names.constructor_name * variable_binding) list   | Lopht_Variable of variable

type cg_environment = {
  mutable function_bindings : func QualEnv.t;
  mutable type_bindings : ty TyEnv.t;
  mutable clock_bindings : clk ClEnv.t;
  mutable variable_bindings : variable_binding VarEnv.t;
  mutable input_bindings : (block * Clocks.ck * variable_binding list) list;
  primitive_clock : clk;
  cg : clocked_graph; (* with all lists reversed *)
}


(* Clocked Graph building *)

let add_clock cg clk_desc clk_dependencies =
  let clk_index = match cg.clocks with
    | { clk_index } :: _ -> clk_index + 1
    | [] -> 0
  in
  let gclock = {
    clk_index;
    clk_id = None;
    clk_desc;
    clk_dependencies;
  }
  in
  cg.clocks <- gclock :: cg.clocks;
  gclock

let add_function cg fun_id fun_inputs fun_outputs =
  let fun_index = match cg.functions with
    | { fun_index } :: _ -> fun_index + 1
    | [] -> 0
  in
  let gfunc = {
    fun_index;
    fun_id;
    fun_inputs;
    fun_outputs;
  }
  in
  cg.functions <- gfunc :: cg.functions;
  gfunc

let add_block cg block_clk block_function =
  let block_index = match cg.blocks with
    | { block_index } :: _ -> block_index + 1
    | [] -> 0
  in
  let gblock = {
    block_index;
    block_id = None;
    block_clk;
    block_inputs = [];
    block_outputs = [];
    block_function;
    block_preemptible = None;
    block_offset = None;
    block_deadline = None;
    block_partitions = [];
    block_schedule = None;
  }
  in
  cg.blocks <- gblock :: cg.blocks;
  gblock

let add_variable cg var_type port_id gblock =
  let var_index = match cg.variables with
    | { var_index } :: _ -> var_index + 1
    | [] -> 0
  in
  let gvar = {
    var_index;
    var_type;
    var_source_port = (port_id, gblock);
    var_allocation = None;
  }
  in
  cg.variables <- gvar :: cg.variables;
  gvar


(* First pass, don't bind input parameters nor clocks *)

let translate_ty henv genv ty =
  try
    TyEnv.find ty genv.type_bindings
  with
    Not_found -> raise Not_implemented

let rec translate_extvalue henv genv { w_desc } =
  match w_desc with
  | Wconst static_exp -> raise Not_implemented
  (* VarEnv.add dest env.variable_bindings *)
  | Wvar var_ident -> Alias var_ident
  | Wfield (_extvalue, _field_name) -> raise Not_implemented (* Build a selector block *)
  | Wwhen (extvalue, _constructor_name, _var_ident) -> translate_extvalue henv genv extvalue 
  | Wreinit (_extvalue1, _extvalue2) -> raise Not_implemented

let translate_parameter henv genv param =
  if param.v_linearity <> Linearity.Ltop || param.v_clock <> Clocks.Cbase then
    raise Not_implemented;
  ident_to_lopht_id param.v_ident, translate_ty henv genv param.v_type

let translate_node henv genv hnode =
  try
    QualEnv.find hnode.n_name genv.function_bindings
  with Not_found ->
    let fun_id = qualname_to_lopht_id hnode.n_name
    and fun_inputs = List.map (translate_parameter henv genv) hnode.n_input
    and fun_outputs = List.map (translate_parameter henv genv) hnode.n_output in
    let gfunc = add_function genv.cg fun_id fun_inputs fun_outputs in
    genv.function_bindings <- QualEnv.add hnode.n_name gfunc genv.function_bindings;
    gfunc

let translate_call henv genv ck call_name fun_name static_params inputs =
  if static_params <> [] then
    raise Not_implemented;
  let hnode = QualEnv.find fun_name henv.hnodes in
  let gfunc = translate_node henv genv hnode in
  let block_fun = FunBlock gfunc
  and block_clock = List.hd genv.cg.clocks in
  let gblock = add_block genv.cg block_clock block_fun in
  let bind_output (port_id,var_type) =
    let gvar = add_variable genv.cg var_type port_id gblock
    in Lopht_Variable gvar, {
      output_port_name = port_id;
      output_port_var = gvar;
    }
  in
  let targets, block_outputs = List.split (List.map bind_output gfunc.fun_outputs) in 
  gblock.block_outputs <- block_outputs;
  let input_bindings = List.map (translate_extvalue henv genv) inputs in
  genv.input_bindings <- (gblock, ck, input_bindings) :: genv.input_bindings;
  targets

let translate_exp henv genv exp =
  match exp.e_desc with
  | Eextvalue extvalue -> [ translate_extvalue henv genv extvalue ]
  | Efby (Some static_exp, extvalue) -> raise Not_implemented (* fby *)
  | Efby (None, extvalue) -> raise Not_implemented (* pre *)
  | Eapp (app, extvalue_list, None) ->
      begin match app.a_op with
        | Eequal -> raise Not_implemented
        | Efun fun_name
        | Enode fun_name -> translate_call henv genv exp.e_level_ck app.a_id fun_name app.a_params extvalue_list
        | _ -> raise Not_implemented
      end
  | Eapp (app, extvalue_list, Some _var_ident) -> raise Not_implemented
  | Ewhen (exp, _constructor_name, _var_ident) -> raise Not_implemented
  | Emerge (var_ident, l) -> [ Merge (var_ident, List.map (fun (n, e) -> n, translate_extvalue henv genv e) l) ]     
  | Estruct _ -> raise Not_implemented
  | Eiterator (_, _, _, _, _, _) -> raise Not_implemented

let translate_eq henv genv { eq_lhs ; eq_rhs ; eq_base_ck } =
  let sources = translate_exp henv genv eq_rhs in
  let destinations = match eq_lhs with
    | Evarpat var_ident -> [ var_ident ]
    | Etuplepat [] -> []
    | Etuplepat _pat_list -> raise Not_implemented
  in
  let add_binding dest source =
    genv.variable_bindings <- VarEnv.add dest source genv.variable_bindings
  in
  List.iter2 add_binding destinations sources 


(* Second pass, bind input parameters and clocks *)

let rec translate_clock genv ck =
  try
    ClEnv.find ck genv.clock_bindings  
  with Not_found ->
    match ck with 
      | Clocks.Cbase -> genv.primitive_clock
      | Clocks.Cvar _ -> raise Not_implemented
      | Clocks.Con (base_ck, constructor_name, var_ident) ->
          let base = translate_clock genv base_ck in
          let binding = VarEnv.find var_ident genv.variable_bindings in
          let var = match resolve_binding genv base_ck binding with
            | [ (var, _) ] -> var 
            | _ -> raise Not_implemented
          in 
          let value = match constructor_name with 
            | { Names.qual = Names.Pervasives; name = "false" } -> Boolean false
            | { Names.qual = Names.Pervasives; name = "true" } -> Boolean true
            | _ -> raise Not_implemented
          in 
          let clk_desc = Derived (Test (BaseClock base, Equal (var, Const value)))
          and clk_dependencies = [ (var,base) ]
          in
          let gclock = add_clock genv.cg clk_desc clk_dependencies in
          genv.clock_bindings <- ClEnv.add ck gclock genv.clock_bindings;
          gclock

and resolve_binding genv ck binding =
  let rec resolve ck r = function
    | Alias ident ->
        let binding = VarEnv.find ident genv.variable_bindings in
        resolve ck r binding
    | Merge (ident, l) ->
        let merge r (constructor_name, binding) =
          resolve (Clocks.Con (ck, constructor_name, ident)) r binding
        in
        List.fold_left merge r l 
    | Lopht_Variable var ->
        (var, translate_clock genv ck) :: r
  in
  resolve ck [] binding


let bind_input genv ck (input_port_name, _ty) binding =
  let input_port_arcs = resolve_binding genv ck binding in {
    input_port_name;
    input_port_arcs;
  }

let bind_inputs genv (block, ck, bindings) =
  let fun_inputs = match block.block_function with
    | DelayBlock _delay -> raise Not_implemented
    | FunBlock func -> func.fun_inputs
    | ConstBlock const_exp -> []
  in
  block.block_clk <- translate_clock genv ck;
  block.block_inputs <- List.map2 (bind_input genv ck) fun_inputs bindings


(* Target node handling *)

let translate_node henv genv hnode =
  if hnode.n_input <> [] then
    begin
      Format.eprintf "The top-level node must not have inputs.@.";
      raise Errors.Error
    end;
  let add_var_to_env var_dec =
    henv.hvars <- VarEnv.add var_dec.v_ident var_dec henv.hvars
  in
  List.iter add_var_to_env hnode.n_output;
  List.iter add_var_to_env hnode.n_local;
  List.iter (translate_eq henv genv) hnode.n_equs;
  List.iter (bind_inputs genv) genv.input_bindings


(* Initial environment *) 

let build_environement { p_desc } =
  let primitive_clock = { clk_index = 0 ; clk_id = None ; clk_desc = Primitive ; clk_dependencies = []}
  and ty_int = { Lopht_input.ty_index = 0 ; ty_id = "int" ; ty_desc = Lopht_input.PredefinedType }
  and ty_bool = { Lopht_input.ty_index = 1 ; ty_id = "bool" ; ty_desc = Lopht_input.PredefinedType }
  and qualname_int = { Names.qual = Names.Pervasives ; name = "int" }
  and qualname_bool = { Names.qual = Names.Pervasives ; name = "bool" } in
  let type_list = [ (qualname_int, ty_int) ; (qualname_bool, ty_bool) ] in
  let genv = {
    type_bindings = List.fold_left (fun env (n, t) -> TyEnv.add (Types.Tid n) t env) TyEnv.empty type_list;
    clock_bindings = ClEnv.empty;
    variable_bindings = VarEnv.empty;
    function_bindings = QualEnv.empty;
    input_bindings = [];
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
  }
  and henv = {
    hnodes = QualEnv.empty;
    hconsts = QualEnv.empty;
    htypes = QualEnv.empty;
    hvars = VarEnv.empty;
  }
  in let add_dec = function
    | Pnode node_dec -> henv.hnodes <- QualEnv.add node_dec.n_name node_dec henv.hnodes
    | Pconst const_dec -> henv.hconsts <- QualEnv.add const_dec.c_name const_dec henv.hconsts
    | Ptype type_dec -> henv.htypes <- QualEnv.add type_dec.t_name type_dec henv.htypes
  in
  List.iter add_dec p_desc;
  (henv, genv)

let find_target_node { p_desc } =
  let name = !Compiler_options.target_node in
  if name = "" then begin
    Format.eprintf "A top level node with no argument must be given.@.";
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


(* Entry point of the translation *)

let program ({ p_modname; p_opened; p_desc } as program) =
  let filename = Compiler_utils.filename_of_name (Names.modul_to_string p_modname) ^ ".gc" in
  let out = open_out filename in
  let fmt = Format.formatter_of_out_channel out in
  let (henv, genv) = build_environement program in
  let target_node = find_target_node program in
  translate_node henv genv target_node ;
  let cg = extract_cg genv in
  Lopht_printer.print_clocked_graph fmt cg

