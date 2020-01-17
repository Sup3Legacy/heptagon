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

open Linearity
open Minils
open Cg
open Cg_cwrapper
open Idents

       
exception Not_implemented of string

let qname_to_id = C.cname_of_qn
let name_to_id = C.cname_of_name
let ident_to_id ident = C.cname_of_name (Idents.name ident)


module StringSet = Set.Make (String)
module StringMap = Map.Make (String)
module IntMap = Map.Make(struct type t=int let compare = Pervasives.compare end)
module IntSet = Set.Make(struct type t=int let compare = Pervasives.compare end)
module TyEnv = Map.Make (struct type t = Types.ty let compare = Pervasives.compare end)
module QualEnv = Names.QualEnv
module VarEnv = Idents.Env

(* Needed to determine the partitions *)
let partition_map : int StringMap.t ref = ref StringMap.empty
let translate_partition (part_name:string) : int =
  if StringMap.mem part_name !partition_map then ()
  else
    begin
      let new_part_id =
	StringMap.fold
	  (fun _ n acc_id -> if n>= acc_id then n+1 else acc_id)
	  !partition_map
	  0
      in
      partition_map := StringMap.add part_name new_part_id !partition_map
    end ;
  StringMap.find part_name !partition_map
and reverse_translate_partition (part_id:int) : string =
  try 
    fst (StringMap.choose
	   (StringMap.filter
	      (fun _ id -> part_id = id)
	      !partition_map
	   )
	)
  with Not_found ->
    failwith "Searching for not yet registered partition name.\n"
  
    
(* Intermediate representation of variables between the first 
 * and the second pass. *)
type intermediate_variable =
  {
    iv_ident : Idents.var_ident;
    mutable iv_binding : variable_binding;
  }
 and variable_binding =
   | Unbound
   | Alias of intermediate_variable
   | Merge of
       intermediate_variable * (Names.constructor_name * variable_binding) list
   | Defined_Variable of variable
   | Constant_Binding of const_exp

(* Intermediate representation of clocks *)
 and clock_binding =
   | PrimitiveClock
   | NeverClock
   | DerivedClock of
       clock_binding * Names.constructor_name * intermediate_variable
   | UnionClock of clock_binding list
   | InterClock of clock_binding list
				 

(* Local environments associating an intermediate variable to each 
 * heptagon local variable and input and output parameter *)
type local_environment = intermediate_variable VarEnv.t

(* Debug printing by JP *)
let print_variable (v:variable) : string =
  String.concat
    ""
    [
      "Var:" ;
      string_of_int v.var_index ;
      "(" ;
      fst v.var_source_port ;
      "@" ;
      "Block:" ;
      string_of_int (snd v.var_source_port).block_index ;
      ")" ;
    ]
let rec print_variable_binding vb : string =
  match vb with
  | Unbound -> "Unbound"
  | Alias intermediate_variable ->
     "Alias("^(Idents.name intermediate_variable.iv_ident)^")"
  | Merge (intermediate_variable, nl) ->
     String.concat
       ""
       [
         "Merge(" ;
         Idents.name intermediate_variable.iv_ident ;
         "(" ;
         print_variable_binding intermediate_variable.iv_binding ;
         ")" ;
         "->" ;
         List.fold_left
           (fun acc_str (cn,vb) ->
             String.concat
               ""
               [
                 acc_str ;
                 Names.modul_to_string cn.Names.qual ;
                 "." ;
                 cn.Names.name ;
                 "(" ;
                 print_variable_binding vb ;
                 ")" ;
                 " " ;
               ]
           )
           ""
           nl ;
         ")" ;
       ]
  | Defined_Variable variable ->
     "Defined_Variable("^(print_variable variable)^")"
  | Constant_Binding c ->
     "Constant_Binding(TODO)"
let print_variable_binding_list vbl : string =
  List.fold_left
    (fun acc_str vb ->
     acc_str^(print_variable_binding vb)
    )
    ""
    vbl
let print_intermediate_variable iv : string =
  String.concat
    ""
    [
      "IntermVar(" ;
      Idents.name iv.iv_ident ;
      " -> " ;
      print_variable_binding iv.iv_binding ;
      ")" ;
    ]					       
let print_local_env
      (le:local_environment) : string =
  "Local environment: \n"^
  VarEnv.fold
    (fun id iv acc ->
     String.concat
       ""
       [
	 acc ;
	 Idents.name id ;
	 "::  " ;
	 print_intermediate_variable iv ;
	 "\n";
       ]
    )
    le
    ""

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
      | Union (e1, f1), Union (e2, f2) ->
	 lex_compare
	   compare
	   compare
	   (e1, f1)
	   (e2, f2)
      | Union _, _ -> 1
      | _, Union _ -> -1
      | Intersection (e1, f1), Intersection (e2, f2) -> lex_compare compare compare (e1, f1) (e2, f2)
      | Intersection _, _ -> 1
      | _, Intersection _ -> -1
      | Test (c1, e1), Test (c2, e2) -> lex_compare compare compare_exp (c1, e1) (c2, e2)  
      | _, _ -> assert false (* Any other case is not used in the current implementation *)
  end)

			
type stateful_binding =
  {
    (* The constant used to initialize or reset the state *)
    state_init : const ;
    (* The type of the state *)
    state_type : ty ;
    (* The sequence number, used when a node is instantiated
     * several times *)
    state_seq : int ref ;
  }
    
type function_binding =
  {
    (* The step function *)
    step : func ;
    (* The objects used for stateful (node) calls *)
    stateful : stateful_binding option ;
  }
			

type cg_environment = {
  (* Association of Heptagon type expression and symbols to cg equivalent *)
  mutable type_bindings : ty TyEnv.t;
  mutable constant_bindings : const QualEnv.t;
  valued_mls_constants : Types.static_exp QualEnv.t;
  mutable function_bindings : function_binding QualEnv.t;
  (* Bindings produced at the end of the first pass which must be resolved *)
  mutable input_bindings :
	    (block * clock_binding * ((argument*(string option)) list) * variable_binding list) list;
  (* Associate cg clock expressions to cg clocks to detects double definitions *)
  mutable clock_definitions : clk ClEnv.t;
  (* Generated C functions *)
  mutable operators : func StringMap.t;
  (* Index used to generate unique name for constants *)
  mutable last_constant_index : int;
  (* The single Primitive Clock, which is the Tick *)
  primitive_clock : clk;
  (* The oposite of the primitive clock is the clock that is never
   * active *)
  never_clock : clk ;
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
  (*
  Printf.fprintf
    stderr
    "cg_main.ml::get_node_by_qname called on %s \n"
    (Names.modul_to_string qname.Names.qual) ;
   *)
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
      raise (Not_implemented "translate_typename")
  | Types.Tinvalid | Types.Tclasstype _ ->
      assert false


let translate_ty (genv:cg_environment) ty =
  let ty = Static.simplify_type QualEnv.empty ty in
  try
    TyEnv.find ty genv.type_bindings
  with Not_found ->
    let gty = add_ty genv.cg (translate_typename ty) SimpleType in
    genv.type_bindings <- TyEnv.add ty gty genv.type_bindings ;
    gty

(* This function is responsible with adding constants to the 
 * CG specification. *)
let translate_const_ref genv const_name ty const_expr : const =
  try
    QualEnv.find const_name genv.constant_bindings
  with Not_found ->
       (* There is no binding for it, yet. There are two cases here:
        * - if the constant is declared (with a value) in 
        *   genv.valued_mls_constants, then I need to create a 
        *   valued constant in CG.
        * - if not, just create an ExternalConst object,
        *   as required by const_expr *)
       let cst_ty = translate_ty genv ty
       and cst_id = (qname_to_id const_name)
       and cst_expr =
         try
           let const_def = QualEnv.find const_name genv.valued_mls_constants in
           match const_def.Types.se_desc with
           | Types.Sint i -> LiteralConst (Integer i)
           | Types.Sfloat f -> LiteralConst (Float f)
           | Types.Sbool b -> LiteralConst (Boolean b)
           | Types.Svar constant_name -> ExternalConst
           | Sstring _ -> failwith "Unhandled type of valued constant (Sstring).\n"
           | Sconstructor _ -> failwith "Unhandled type of valued constant (Sconstructor).\n"
           | Sfield _ -> failwith "Unhandled type of valued constant (Sfield).\n"
           | Stuple _ -> failwith "Unhandled type of valued constant (Stuple).\n"
           | Sarray_power _ -> failwith "Unhandled type of valued constant (Sarray_power).\n"
           | Sarray _ -> failwith "Unhandled type of valued constant (Sarray).\n"
           | Srecord _ -> ExternalConst (* The actual definition is provided by the compil to C *)
           | Sop _ -> failwith "Unhandled type of valued constant (Sop).\n"
         with Not_found -> ExternalConst
       in
       let gconst = add_constant genv.cg cst_id cst_ty cst_expr in
       genv.constant_bindings <- QualEnv.add const_name gconst genv.constant_bindings ;
       gconst
      
let add_cdef (genv:cg_environment) cdef =
  genv.csource <- cdef :: genv.csource ;
  genv.cheader <- (C.cdecl_of_cfundef cdef) :: genv.cheader

let add_cdecl_constant
      (genv:cg_environment)
      (const_name:string)
      (const_type:C.cty)
      (const_expr:Types.static_exp_desc) =
  let cexpr:C.cexpr =
    C.Cconst
      (match const_expr with
       | Types.Sint i -> C.Ccint i
       | Types.Sfloat f -> C.Ccfloat f
       | Types.Sbool b -> if b then C.Ccint 1 else C.Ccint 0
       | Types.Sstring s -> C.Cstrlit s
       | _ ->
	  failwith "MLS2CG: constant expression not handled.\n"
      )
  in
  genv.cheader <- (C.Cdecl_constant (const_name,
				     const_type,
				     Some cexpr)
		  )::genv.cheader
		       
let build_operator (genv:cg_environment) op_name fun_inputs fun_outputs cdef = 
  try
    StringMap.find op_name genv.operators
  with Not_found ->
    let gfunc = add_function genv.cg op_name fun_inputs fun_outputs in
    genv.operators <- StringMap.add op_name gfunc genv.operators ;
    add_cdef genv cdef ;
    gfunc

let build_array_power (genv:cg_environment) ty =
  let ty_elt, size = match ty with
  | Types.Tarray (ty_elt, size) -> ty_elt, int_of_static_exp size
  | _ -> assert false
  in 
  let op_name = ("fill_" ^ translate_typename ty)
  and fun_inputs =
    [
      {
        arg_name = "src" ;
        arg_type = translate_ty genv ty_elt ;
      },
      None
    ]
  and fun_outputs =
    [
      (
        {
          arg_name = "dest" ;
          arg_type = translate_ty genv ty ;
        },
        None
      )
    ]
  in
  let cdef = build_c_array_power ty ty_elt size op_name in
  let gfunc =
    build_operator genv op_name fun_inputs fun_outputs cdef
  in
  gfunc

let build_array_constructor (genv:cg_environment) ty =
  let ty_elt, size = match ty with
    | Types.Tarray (ty, size) -> ty, int_of_static_exp size
    | _ -> assert false
  in
  let rec build_args r = function
    | 0 -> r
    | i -> build_args
             (
               (
                 {
                   arg_name = "i" ^ string_of_int i ;
                   arg_type = translate_ty genv ty_elt ;
                 },
                 None
               )
               ::r
             )
             (i -1)
  in
  let op_name = ("construct_" ^ translate_typename ty)
  and fun_inputs = build_args [] size 
  and fun_outputs =
    [
      (
        {
          arg_name = "o" ;
          arg_type = translate_ty genv ty ;
        },
        None
      )
    ]
  in
  let cdef = build_c_array_constructor ty ty_elt size op_name in
  let _gfunc = build_operator genv op_name fun_inputs fun_outputs cdef in
  raise (Not_implemented "build_array_constructor") (* Need to generated array initialisation in C *)

let build_struct_constructor (genv:cg_environment) ty =
  let structure_def = find_structure_def ty in
  let field_to_arg { Signature.f_name ; f_type } =
    (
      {
        arg_name = qname_to_id f_name ;
        arg_type = translate_ty genv f_type ;
      },
      None
    )
  in
  let op_name = ("construct_" ^ translate_typename ty)
  and fun_inputs = List.map field_to_arg structure_def
  and fun_outputs =
    [
      (
        {
          arg_name = "o" ;
          arg_type = translate_ty genv ty ;
        },
        None
      )
    ]
  in
  let cdef = build_c_struct_constructor ty structure_def op_name in
  let gfunc = build_operator genv op_name fun_inputs fun_outputs cdef in
  gfunc

let add_anonymous_constant (genv:cg_environment) cst_ty cst_def =
  genv.last_constant_index <- genv.last_constant_index + 1;
  let cst_name = "const_" ^ string_of_int genv.last_constant_index in
  add_constant genv.cg cst_name cst_ty cst_def

let rec translate_static_exp (genv:cg_environment) static_exp : const_exp =
  let ty = static_exp.Types.se_ty in
  match static_exp.Types.se_desc with
  | Types.Svar const_name -> 
      let const = translate_const_ref genv const_name ty  ExternalConst in
      NamedConst const
  | Types.Sint i -> Integer i
  | Types.Sfloat f -> Float f
  | Types.Sbool b -> Boolean b
  | Types.Sstring s -> String s

  | Types.Sconstructor _e ->
     raise (Not_implemented "translate_static_exp(constr)")
  | Types.Sfield _field_name ->
     raise (Not_implemented "translate_static_exp(field)") 
  | Types.Stuple _l ->
     raise (Not_implemented "translate_static_exp(tuple)")
  | Types.Sop (_fun_name, _parameters) ->
     raise (Not_implemented "translate_static_exp(op)")

  | Types.Sarray_power (value, _sizes) ->
      let gfunc = build_array_power genv ty
      and inputs = [ translate_static_exp genv value ] in
      let cst_desc = InitFunctionConst (gfunc, inputs)
      and cst_ty = (fst (List.hd gfunc.fun_outputs)).arg_type 
      in
      NamedConst (add_anonymous_constant genv cst_ty cst_desc) 

  | Types.Sarray values ->
      let gfunc = build_array_constructor genv ty
      and inputs = List.map (translate_static_exp genv) values in
      let cst_desc = InitFunctionConst (gfunc, inputs)
      and cst_ty = (fst (List.hd gfunc.fun_outputs)).arg_type
      in
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
      and cst_ty = (fst (List.hd gfunc.fun_outputs)).arg_type
      in
      NamedConst (add_anonymous_constant genv cst_ty cst_desc) 

let build_block
      (genv:cg_environment)
      clkb
      block_id
      block_fun
      (fun_inputs:(argument*(string option)) list )
      (fun_outputs:(argument*(string option)) list )
      input_bindings
      block_partition
      block_preemptive
      block_release
      block_deadline : variable_binding list =
  (*
  cg_debug_print
    ("build_block called with output arguments ["
     ^(List.fold_left (fun acc_str { arg_name } -> acc_str^" "^arg_name) "" fun_outputs)
     ^" ]\n"
    ) ;
   *)
  let block_clock =
    (* Clock is by default the primitive clock tick. It is modified later *)
    genv.primitive_clock
  in
  let gblock =
    (* Add the block to the environment *)
    add_block
      genv.cg
      block_clock
      block_id
      block_fun
      block_partition
      block_preemptive
      block_release
      block_deadline
  in
  let (targets, block_outputs) =
    let bind_output ({ arg_name ; arg_type },_) : variable_binding*output_port =
      (* Build the output variables and the output ports and add them to 
       * the environment *)
      let gvar =
        let var_name =
          None (* I set these later *)
        in
        add_variable genv.cg var_name arg_type arg_name gblock
      in
      (
	Defined_Variable gvar,
	{
	  output_port_name = arg_name;
	  output_port_var = gvar;
	}
      )
    in
    List.split (List.map bind_output fun_outputs)
  in
  (* Set the outputs of the block, non-functional *)
  gblock.block_outputs <- block_outputs;
  (* Add to the input bindings of the block in the environment *)
  genv.input_bindings <-
    (gblock,
     clkb,
     fun_inputs,
     input_bindings)
    :: genv.input_bindings;
  (* The output is a list of variables (the outputs of the block) *)
  targets

let build_block_from_func
      gfunc
      (genv:cg_environment)
      clkb
      input_bindings
      block_partition
      block_preemptive
      block_release
      block_deadline : variable_binding list =
    let block_fun = FunBlock gfunc
    and block_id = Some gfunc.fun_id
    and fun_outputs = gfunc.fun_outputs
    and fun_inputs = gfunc.fun_inputs
    in
    build_block
      genv
      clkb
      block_id
      block_fun
      fun_inputs
      fun_outputs
      input_bindings
      block_partition
      block_preemptive
      block_release
      block_deadline
      
let translate_const
      (genv:cg_environment)
      static_exp
      eq_partition : variable_binding =
  let gconst = translate_static_exp genv static_exp
  and gty = translate_ty genv static_exp.Types.se_ty
  in
  Constant_Binding gconst

let translate_var
      (lenv:local_environment)
      (var_ident:Idents.var_ident) : intermediate_variable =
  try
    VarEnv.find var_ident lenv
  with Not_found ->
    begin
      Printf.fprintf
	stderr
	"translate_var : searching for missing variable %s in lenv:\n%s\n"
	(Idents.name var_ident)
	(print_local_env lenv) ;
      failwith "translate_var : exiting."
    end
		  
let rec translate_ck
	  (lenv:local_environment) = function
  | Clocks.Cbase -> PrimitiveClock
  | Clocks.Cvar _ -> raise (Not_implemented "translate_ck")
  | Clocks.Con (base_ck, constructor_name, var_ident) ->
     DerivedClock
       (translate_ck lenv base_ck,
	constructor_name,
	translate_var lenv var_ident)

let rec translate_extvalue
	  (genv:cg_environment)
	  (lenv:local_environment)
	  (eq_partition:int option)
	  (eq_preemptive: bool)
	  (eq_release:int option)
	  (eq_deadline:int option)
	  extvalue =
  match extvalue.w_desc with
  | Wconst static_exp -> translate_const genv static_exp eq_partition
  | Wvar var_ident ->
     Alias
       (translate_var lenv var_ident)
  | Wfield (_extvalue, _field_name) ->
     raise (Not_implemented "translate_extvalue") (* Build a selector block *)
  | Wwhen (extvalue, _constructor_name, _var_ident) ->
     translate_extvalue genv lenv eq_partition eq_preemptive eq_release eq_deadline extvalue 
  | Wreinit (_extvalue1, _extvalue2) ->
     raise (Not_implemented "translate_extvalue")

let generated_arg_counter = ref 0

                            	    
let translate_arg (genv:cg_environment) param : argument =
  let open Signature in
  if param.a_clock <> Cbase then
    raise (Not_implemented "translate_arg - clock different from base")
  else
    let name = match param.a_name with
      | Some name -> name
      | None ->
         (* This is the case where the function parameter has no
          * provided name. In this case, I create a new name (not
          * a new variable). *)
         generated_arg_counter := !generated_arg_counter + 1 ;
         "gen"^(string_of_int !generated_arg_counter)
    in
    {
      arg_name = name_to_id name ;
      arg_type = translate_ty genv param.a_type ;
    }

let translate_input_arg (genv:cg_environment) (param:Signature.arg) : argument*(string option) =
  match param.Signature.a_linearity with
  | Linearity.Ltop ->
     (translate_arg genv param,None)
  | Linearity.Lat name ->
     begin
       match param.a_name with
       | None ->
          (* 
          raise (Not_implemented "translate_input_arg - nameless input argument")
           *)
          (translate_arg genv param,Some name)
       | Some param_name ->
          if name = param_name then
            (translate_arg genv param, Some name)
          else
            raise (Not_implemented ("translate_input_arg - input allocated on different argument: "
                                    ^param_name
                                    ^" on "
                                    ^name))
     end
  | _ ->
     raise (Not_implemented "translate_input_arg - linearity different from Ltop, Lat")
and translate_output_arg (genv:cg_environment) (param:Signature.arg) : (argument*(string option)) =
  match param.Signature.a_linearity with
  | Linearity.Ltop ->
     (translate_arg genv param, None)
  | Linearity.Lat name ->
     (translate_arg genv param, Some name)
  | _ ->
     raise (Not_implemented "translate_output_arg - linearity not handled")

                 
(* JP: translate a function call, currently without using any context
 * information, just the signature of the function and its name. *)
let translate_function
      (genv:cg_environment)
      (name:Names.qualname)
      (hnode:Signature.node) : function_binding =
  try
    let old_function_binding = 
      QualEnv.find name genv.function_bindings
    in
    (*
    cg_debug_print
      ("translate_function called for already translated function "
       ^(Names.fullname name)
       ^"\n") ;
     *)
    old_function_binding
  with Not_found ->
    (*
    cg_debug_print
      ("translate_function called for new function "
       ^(Names.fullname name)
       ^"\n") ;
     *)
    let open Signature in
    let fun_id = qname_to_id name in
    let fun_inputs_no_state:(argument*(string option)) list =
      List.map (translate_input_arg genv) hnode.node_inputs
    and fun_outputs_no_state:(argument*(string option)) list =
      List.map (translate_output_arg genv) hnode.node_outputs
    in
    let fun_step_id =
      fun_id ^
	(if  (name.Names.qual = Names.Pervasives) && not hnode.node_stateful then "" else "_step")
    and fun_reset_id = fun_id ^ "_reset"
    in
    let (fun_inputs:(argument*(string option)) list),
        (fun_outputs:(argument*(string option)) list),
        stateful_objects =
      if hnode.node_stateful then
	(* The type of the state variables *)
	let ty_name = { Names.qual = Names.LocalModule ; Names.name = fun_id ^ "_mem" } in
	let ty = Types.Tid ty_name in
        let state_ty = translate_ty genv ty in
	(* The two state variables that go in and out of the 
	 * state, as well as the output parameter of the init 
	 * function *)
        let state_out_param =
          (
            {
              arg_name = "state_out" ;
              arg_type = state_ty ;
            },
            Some "state_in"
          )
	and state_in_param =
          (
            {
              arg_name = "state_in" ;
              arg_type = state_ty ;
            },
            Some "state_in"
          )
	and reset_out_param =
          (
            {
              arg_name = "state_out" ;
              arg_type = state_ty ;
            },
            None (* because the reset function has no input *)
          )
	in
	(fun_inputs_no_state@[state_in_param],
	 fun_outputs_no_state@[state_out_param],
	 Some
	   {
	     state_init  =
	       begin 
		 (* The function needed to initialize the constant *)
		 let gfunc_reset =
		   add_function genv.cg fun_reset_id [] [reset_out_param]
		 in
		 let const_name = { Names.qual = Names.LocalModule ;
                                    Names.name = fun_id ^ "_init_state" } in
		 translate_const_ref genv const_name ty (InitFunctionConst (gfunc_reset,[]))
	       end ;
	     state_type = state_ty ;
	     state_seq = ref 0 ; (* always start at index 0 *)
	   }
	)
      else
        (fun_inputs_no_state,
	 fun_outputs_no_state,
	 None)
    in
    let gfunc_step = add_function genv.cg fun_step_id fun_inputs fun_outputs in
    (* Put all constructed objects in the environment, and build the C 
     * wrappers *)
    genv.function_bindings <-
      QualEnv.add
	name
	{
	  step = gfunc_step ;
	  stateful = stateful_objects ;
	}
	genv.function_bindings;
    (* This piece of code creates wrappers for 
    let _ =
      let cdefs = build_c_wrappers fun_step_id fun_reset_id name hnode in
      List.iter (add_cdef genv) cdefs
    in
     *)
    {
      step = gfunc_step ;
      stateful = stateful_objects ;
    }
      
      
let translate_fby
      (genv:cg_environment)
      (lenv:local_environment)
      ck
      init
      extvalue
      fby_partition
      fby_preemptive
      fby_release
      fby_deadline : variable_binding list =
  (* Printf.printf "translate_fby started.\n" ;*)
  let delay_ty = translate_ty genv extvalue.w_ty in
  let result_variable_binding_list =
    let clkb = translate_ck lenv ck
    and block_id = None
    and block_fun =
      let init_const = match init with
	| Some static_exp ->
           (* FBY with constant (static expression) initial value *)
           translate_static_exp genv static_exp
	| None ->
           (* If the initial value is not a static expression, cannot handle *)
           raise (Not_implemented "translate_fby")
      in
      let gdelay =
        {
	  delay_ty;
	  delay_depth = 1;
	  delay_init = [ init_const ];
	}
      in
      DelayBlock gdelay
    and fun_inputs =
      (* There is a single input port on a delay, named "i" *)
      [
        (
          {
            arg_name = "i";
            arg_type = delay_ty;
          },
          None
        )
      ]
    and fun_outputs =
      (* There is a single output port on a delay, named "o" *)
      [
        (
          {
            arg_name = "o";
            arg_type = delay_ty;
          },
          None
        )
      ]
    and input_bindings =
      (* Input binding *)
      [ translate_extvalue
	  genv
	  lenv
	  fby_partition
	  fby_preemptive
	  fby_release
	  fby_deadline
	  extvalue
      ]
    in
    build_block
      genv
      clkb
      block_id
      block_fun
      fun_inputs
      fun_outputs
      input_bindings
      fby_partition
      fby_preemptive
      fby_release
      fby_deadline
  in
  (*
  let _ =
    Printf.printf
      "translate_fby has produced the following bindings:\n%s\n"
      (print_variable_binding_list result_variable_binding_list)
  in
   *)
  result_variable_binding_list

let translate_merge
      (genv:cg_environment)
      (lenv:local_environment)
      var_ident
      (l:(Names.constructor_name * extvalue) list)
      merge_partition
      merge_preemptive
      merge_release
      merge_deadline =
  let var = translate_var lenv var_ident
  and l' =
    List.map
      (fun (n, e) -> n, translate_extvalue
			  genv
			  lenv
			  merge_partition
			  merge_preemptive
			  merge_release
			  merge_deadline
			  e
      )
      l
  in
  [ Merge (var, l') ]


let translate_app_ifthenelse
      (genv:cg_environment)
      (lenv:local_environment)
      inputs
      (app_partition:int option)
      (app_preemptive:bool)
      (app_release:int option)
      (app_deadline:int option)
    : variable_binding list =
  (* Printf.printf ">>translate_app ifthenelse branch.\n" ;*)
  match inputs with
  | sel_extval::then_extval::else_extval::[] ->
     let selector_var_ident =
       match sel_extval.w_desc with
       | Wvar var_ident -> var_ident
       | _ ->
	  raise (Not_implemented "translate_app_ifthenelse - bad w_desc(selector).")
     in
     translate_merge
       genv
       lenv
       selector_var_ident
       [
	 (Names.pervasives_qn "true",then_extval);
	 (Names.pervasives_qn "false",else_extval);
       ]
       app_partition
       app_preemptive
       app_release
       app_deadline
       
  | _ ->
     failwith "Ifthenelse shoud have 3 parameters."



let fby_eq
      fby_in_var_id
      ck
      state_in_var_ident
      stateful_binding
      ty
      app_partition
      app_preemptive
      app_release
      app_deadline : eq
  =
  {
    eq_lhs    = Evarpat state_in_var_ident ;
    eq_rhs    =
      {
	e_desc            = Efby
			      (
				Some
				  {
				    Types.se_desc = Types.Svar (Names.local_qn stateful_binding.state_init.cst_id) ;
				    Types.se_ty = ty ;
				    Types.se_loc = Location.no_location ;
				  },
				{
				  w_desc      = Wvar fby_in_var_id ;
				  w_ck        = ck ;
				  w_ty        = Types.Tid (Names.local_qn stateful_binding.state_type.ty_id) ;
				  w_linearity = Linearity.Ltop ;
				  w_loc       = Location.no_location ;
				}
			      ) ;
	e_level_ck        = ck ;
	e_ct              = Clocks.Ck ck ; (* here, we are only using scalars, so the clock type is
				     * a scalar of the current clock *)
	e_ty              = ty ;
	e_linearity       = Linearity.Ltop ;
	e_loc             = Location.no_location ;
      } ;
    eq_unsafe     = false ;
    eq_base_ck    = ck ;
    eq_loc        = Location.no_location;
    eq_partition  =
      begin
	match app_partition with
	| None -> None
	| Some x -> Some (reverse_translate_partition x)
      end ;
    eq_preemptive = app_preemptive ;
    eq_release    = app_release ;
    eq_deadline   = app_deadline ; 
  }		
and merge_eq 
      fby_in_var_ident
      (reset_var : Idents.ident)
      ck
      state_out_var_ident
      stateful_binding
      ty
      app_partition
      app_preemptive
      app_release
      app_deadline : eq =
  {
    eq_lhs    = Evarpat fby_in_var_ident ;
    eq_rhs    =
      {
	e_desc            = Emerge
			      (
				reset_var,
				[
				  (
				    { Names.qual = Names.Pervasives ; name = "true"},
				    {
				      w_desc      = Wconst
						      {
							Types.se_desc =
							  Types.Svar (Names.local_qn stateful_binding.state_init.cst_id) ;
							Types.se_ty = ty ;
							Types.se_loc = Location.no_location ;
						      } ;
				      w_ck        = Clocks.Con
						      (
							ck,
							{ Names.qual = Names.Pervasives ; name = "true"},
							reset_var
						      ) ;
				      w_ty        = ty ;
				      w_linearity = Linearity.Ltop ;
				      w_loc       = Location.no_location ;
				    }
				  ) ;
				  (
				    { Names.qual = Names.Pervasives ; name = "false"},
				    {
				      w_desc      = Wvar state_out_var_ident ;
				      w_ck        = Clocks.Con
						      (
							ck,
							{ Names.qual = Names.Pervasives ; name = "false"},
							reset_var
						      ) ;
				      w_ty        = ty ;
				      w_linearity = Linearity.Ltop ;
				      w_loc       = Location.no_location ;
				    }					   
				  ) ;
				]
			      ) ;
	e_level_ck        = ck ;
	e_ct              = Clocks.Ck ck ;
	e_ty              = ty ;
	e_linearity       = Linearity.Ltop ;
	e_loc             = Location.no_location ;
      } ;
    eq_unsafe     = false ;
    eq_base_ck    = ck ;
    eq_loc        = Location.no_location;
    eq_partition  =
      begin
	match app_partition with
	| None -> None
	| Some x -> Some (reverse_translate_partition x)
      end ;
    eq_preemptive = app_preemptive ;
    eq_release    = app_release ;
    eq_deadline   = app_deadline ; 
  }
    
let split_last (l:'a list) : 'a*('a list) =
  let rev_l = List.rev l in
  match rev_l with
  | hh::tt -> (hh,List.rev tt)
  | [] ->
     failwith "remove_last on empty list."
    
    
let rec translate_app_fun_stateful
	  (genv:cg_environment)
	  (lenv:local_environment)
	  (reset_vars:Idents.ident list)
	  (ck:Clocks.ck)
	  (app_partition:int option)
	  (app_release:int option)
	  (app_deadline:int option)
	  (app_preemptive:bool)
	  (extra_var_ids:Idents.var_ident list)	  
	  input_bindings_no_state
	  fb
	  step_clkb
	  stateful_binding
	: variable_binding list
  =
  (*
  Printf.printf
    ">>translate_app_fun_stateful entered with extra vars = %s.\n"
    (List.fold_left
       (fun acc id ->
	acc^(Idents.name id)^"; "
       )
       ""
       extra_var_ids
    );
   *)
  let state_out_var_ident,state_in_var_ident,fby_in_var_ident_maybe =
    match extra_var_ids with
    | x1::x2::l1 -> (x1,x2,l1)
    | _ -> failwith "Bad construction."
  in
  let ty = Types.Tid (Names.local_qn stateful_binding.state_type.ty_id) in
  let result_bindings = 
    match reset_vars with
    | [] ->
       (* Printf.printf ">>translate_app no reset branch.\n" ;*)
       (* This stateful node is only initialized at the beginning,
	* and never reset. *)
       let fby_equation : eq =
	 fby_eq
	   state_out_var_ident
	   ck
	   state_in_var_ident
	   stateful_binding
	   ty
	   app_partition
	   app_preemptive
	   app_release
	   app_deadline
       in
       translate_eq genv lenv [] fby_equation [] ;
       (* Printf.printf
	 "After translation of fby equation:\n%s\n"
	 (print_local_env lenv) ;*)
       (* Now the fby has been translated, I still have to create the
	* function call. This one is more complicated, as I cannot resort
	* to calling translate_eq (half the work has been already done, and
	* the function call does not match the interface declaration.
	*)
       let input_bindings =
	 input_bindings_no_state@[(translate_var lenv state_in_var_ident).iv_binding]
       in
       let (var_binding_list : variable_binding list) = 
	 build_block_from_func
	   fb.step
	   genv
	   step_clkb
	   input_bindings
	   app_partition
	   app_preemptive
	   app_release
	   app_deadline
       in
       let state_out_binding,other_bindings =
	 split_last var_binding_list 
       in
       (translate_var lenv state_out_var_ident).iv_binding <- state_out_binding ;
       other_bindings

    | [reset_var] ->
       (* Printf.printf ">>translate_app reset branch.\n" ; *)
       (* This stateful node is reset by variable reset_var *)
       let fby_in_var_ident =
	 match fby_in_var_ident_maybe with
	 | [x] -> x
	 | _ -> failwith "Bad construction (2)."
       in
       let merge_equation : eq =
	 merge_eq 
	   fby_in_var_ident
	   reset_var
	   ck
	   state_out_var_ident
	   stateful_binding
	   ty
	   app_partition
	   app_preemptive
	   app_release
	   app_deadline
       and fby_equation : eq =
	 fby_eq
	   fby_in_var_ident
	   ck 
	   state_in_var_ident
	   stateful_binding
	   ty
	   app_partition
	   app_preemptive
	   app_release
	   app_deadline
       in
       translate_eq genv lenv [] fby_equation [] ;
       translate_eq genv lenv [] merge_equation [] ;
       (* Now the fby and the merge have been translated, I still have to 
	* create the function call. This one is more complicated, as I 
	* cannot resort to calling translate_eq (half the work has been 
	* already done, and the function call does not match the interface 
	* declaration.
	*)
       let input_bindings =
	 input_bindings_no_state@[(translate_var lenv state_in_var_ident).iv_binding]
       in
       let (var_binding_list : variable_binding list) = 
	 build_block_from_func
	   fb.step
	   genv
	   step_clkb
	   input_bindings
	   app_partition
	   app_preemptive
	   app_release
	   app_deadline
       in
       let state_out_binding,other_bindings =
	 split_last var_binding_list 
       in
       (translate_var lenv state_out_var_ident).iv_binding <- state_out_binding ;
       other_bindings
	 
    | _ ->
       failwith "Cannot handle multiple reset levels."
  in
  (* Printf.printf ">>translate_app_fun_stateful completed.\n" ;*)
  result_bindings
    
and translate_app_fun
      (genv:cg_environment)
      (lenv:local_environment)
      (reset_vars:Idents.ident list)
      (ck:Clocks.ck)
      app
      inputs
      fun_name
      (app_partition:int option)
      (app_preemptive:bool)
      (app_release:int option)
      (app_deadline:int option)
      (extra_var_ids:Idents.var_ident list)	: variable_binding list =
  (* Printf.printf ">>translate_app node/fun branch.\n" ;*)
  (* Compute function name and input bindings. *)
  let step_clkb = translate_ck lenv ck in
  let input_bindings_no_state:variable_binding list =
    List.map
      (translate_extvalue
	 genv
	 lenv
	 app_partition
	 app_preemptive
	 app_release
	 app_deadline
      )
      inputs
  in
  let function_binding =
    let hnode = Modules.find_value fun_name in
    translate_function genv fun_name hnode
  in
  let input_bindings =
    List.map
      (translate_extvalue
	 genv
	 lenv
	 app_partition
	 app_preemptive
	 app_release
	 app_deadline
      )
      inputs
  in
  if app.a_inlined then
    begin
      (* Printf.printf ">>translate_app inlined branch.\n" ;*)
      let hnode = get_node_by_qname fun_name in
      translate_node genv reset_vars hnode input_bindings
    end
  else
    begin
      (* Printf.printf ">>translate_app non-inlined branch.\n" ;*)
      let (fb : function_binding) =
	let hnode = Modules.find_value fun_name in
	translate_function genv fun_name hnode
      in
      match fb.stateful with
      | None ->
	 begin 
	   (* Printf.printf ">>translate_app non-stateful branch.\n" ;*)
	   (* If there is no state, then the bindings are exactly
	    * those corresponding to the inputs. *)
	   build_block_from_func
	     function_binding.step
	     genv
	     step_clkb
	     input_bindings_no_state
	     app_partition
	     app_preemptive
	     app_release
	     app_deadline
	 end
	   
      | Some stateful_binding  ->
	 translate_app_fun_stateful
	   genv
	   lenv
	   reset_vars
	   ck
	   app_partition
	   app_release
	   app_deadline
	   app_preemptive
	   extra_var_ids
	   input_bindings_no_state
	   fb
	   step_clkb
	   stateful_binding
    end
      
and translate_app
      (genv:cg_environment)
      (lenv:local_environment)
      reset_vars
      ck
      app
      inputs
      (app_partition:int option)
      (app_preemptive:bool)
      (app_release:int option)
      (app_deadline:int option)
      (extra_var_ids:Idents.var_ident list) : variable_binding list =
  (* 
  Printf.printf
    ">>translate_app called with reset_vars = %s.\n"
    (List.fold_left
       (fun acc var ->
	acc^(Idents.name var)^"; "
       )
       ""
       reset_vars
    );
   *)
  let result_var_bindings = 
    if app.a_params <> [] then
      raise (Not_implemented "translate_app - static params");
    match app.a_op with
    | Efield_update
      | Earray       
      | Earray_fill  
      | Eselect      
      | Eselect_slice
      | Eselect_dyn  
      | Eselect_trunc
      | Eupdate      
      | Econcat      
      | Eequal ->
       raise (Not_implemented "translate_app")
    | Eifthenelse ->
       translate_app_ifthenelse
	 genv
	 lenv
	 inputs
	 app_partition
	 app_preemptive
	 app_release
	 app_deadline

    | Efun fun_name
      | Enode fun_name ->
       translate_app_fun
	 genv
	 lenv
	 reset_vars
	 ck
	 app
	 inputs
	 fun_name
	 app_partition
	 app_preemptive
	 app_release
	 app_deadline
	 extra_var_ids
  in
  (* Printf.printf ">>translate_app completed.\n" ;*)
  result_var_bindings
    
and translate_eq
      (genv:cg_environment)
      (lenv:local_environment)
      (reset_vars:Idents.ident list)
      (eq : eq)
      (extra_var_ids:Idents.var_ident list) : unit =
  (*
  Printf.printf "=====================================\n";
  Printf.printf "translate_eq called.\n";
   *)
  let destinations:Idents.var_ident list = match eq.eq_lhs with
    | Evarpat var_ident -> [ var_ident ]
    | Etuplepat l ->
       List.map
	 (function
	    Evarpat var_ident -> var_ident
	  | Etuplepat _ ->
             raise (Not_implemented "translate_eq on equations with hierarchic tuples")
	 )
	 l
  and sources:variable_binding list =
    let partition_id_opt =
      match eq.eq_partition with
      | None ->
	 (* Printf.fprintf stderr "MiniLS equation without partition...\n" ;*)
	 None
      | Some s -> Some (translate_partition s)
    in
    translate_exp
      genv
      lenv
      reset_vars
      eq.eq_rhs
      partition_id_opt
      eq.eq_preemptive
      eq.eq_release
      eq.eq_deadline
      extra_var_ids
  in
  (*
  let _ =
    Printf.printf
      "translate_eq will bind %s\n"
      (List.fold_left2
	 (fun acc_str d s ->
	  String.concat
	    ""
	    [
	      Idents.name d ;
	      "=>" ;
	      print_variable_binding s ;
	      "\n" ;
	    ]
	 )
	 ""
	 destinations
	 sources
      )
  in
   *)
  try
    let add_binding (dest:Idents.var_ident) (source:variable_binding) : unit =
      (translate_var lenv dest).iv_binding <- source ;
      match source with
      | Defined_Variable variable ->
         variable.var_name <- Some (Idents.name dest)
      | Unbound ->
         cg_debug_print "translate_eq::add_binding called with non-defined (unbound) source.\n"
      | Alias _ -> 
         cg_debug_print "translate_eq::add_binding called with non-defined (alias) source.\n"
      | Merge _ ->
         cg_debug_print
           ("translate_eq::add_binding called with non-defined (merge) source:\n"
            ^(Idents.name dest)^"->"^(print_variable_binding source)
            ^"\n")
      | Constant_Binding _ ->
         cg_debug_print
           ("translate_eq::add_binding on var "^(Idents.name dest)^" called with non-defined (const) source.\n")
    in
    List.iter2 add_binding destinations sources
  with Invalid_argument _ ->
    failwith
      (String.concat
	 ""
	 [
	   "translate_eq: Incompatible list lengths: destinations: " ;
	   string_of_int (List.length destinations) ;
	   " sources: " ;
	   string_of_int (List.length sources) ;
	   "\n" ;
	 ]
      )
    
and translate_exp
      (genv:cg_environment)
      (lenv:local_environment)
      reset_vars
      exp
      eq_partition
      eq_preemptive
      eq_release
      eq_deadline
      (extra_var_ids:Idents.var_ident list) : variable_binding list =
  match exp.e_desc with
  | Eextvalue extvalue ->
     (* Printf.printf "Translate EXTVAL.\n" ;*)
     [
       translate_extvalue
	 genv
	 lenv
	 eq_partition
	 eq_preemptive
	 eq_release
	 eq_deadline
	 extvalue
     ]
  | Efby (static_exp_opt, extvalue) ->
     (* Printf.printf "Translate FBY.\n" ;*)
     translate_fby
       genv
       lenv
       exp.e_level_ck
       static_exp_opt
       extvalue
       eq_partition
       eq_preemptive
       eq_release
       eq_deadline
  | Eapp (app, extvalue_list, None) ->
     (* Printf.printf "Translate APP.\n" ;*)
     translate_app
       genv
       lenv
       reset_vars
       exp.e_level_ck
       app
       extvalue_list
       eq_partition
       eq_preemptive
       eq_release
       eq_deadline
       extra_var_ids
  | Eapp (app, extvalue_list, Some reset_ident) ->
     (* Printf.printf "Translate APP with reset.\n" ;*)
     let new_reset_vars = reset_ident :: reset_vars in
     translate_app
       genv
       lenv
       new_reset_vars
       exp.e_level_ck
       app
       extvalue_list
       eq_partition
       eq_preemptive
       eq_release
       eq_deadline
       extra_var_ids
  | Ewhen (exp, _constructor_name, _var_ident) ->
     (* Printf.printf "Translate WHEN.\n" ;*)
     translate_exp
       genv
       lenv
       reset_vars
       exp
       eq_partition
       eq_preemptive
       eq_release
       eq_deadline
       []
  | Emerge (var_ident, l) ->
     (* Printf.printf "Translate MERGE.\n" ;*)
     translate_merge
       genv
       lenv
       var_ident
       l
       eq_partition
       eq_preemptive
       eq_release
       eq_deadline
  | Estruct _
    | Eiterator (_, _, _, _, _, _) ->
     raise (Not_implemented "translate_exp")


           
and translate_node
      genv
      reset_vars
      hnode
      input_bindings : variable_binding list =
  (*
  cg_debug_print
    ("translate_node called on "
     ^hnode.n_name.name
     ^"\n") ;
   *)
  (* The only function call of this file that can create 
   * new variables. It is only called at node level. *)
  print_endline "CG::translate_node start" ;
  let add_var_to_lenv
	(lenv:local_environment)
	binding
	var_dec
      : local_environment =
    (*
    cg_debug_print
      ("add_var_to_lenv called by translate_node for node/fun "
       ^hnode.n_name.name
       ^" on variable "
       ^(Idents.source_name var_dec.v_ident)
       ^"\n") ;
     *)
    VarEnv.add
      var_dec.v_ident
      {
	iv_ident = var_dec.v_ident ;
	iv_binding = binding
      }
      lenv
  in
  (* print_endline "CG::translate_node intermediate 1" ;*)
  (* Start with an empty local environment *)
  let lenv = VarEnv.empty in
  (* Then, add to it the input bindings *)
  let lenv =
    List.fold_left2
      add_var_to_lenv (* function to apply *)
      lenv            (* initial accumulator state *)
      (List.rev input_bindings)  (* first list *)
      (List.rev hnode.n_input)   (* second list *)
(*    List.fold_right2
      add_var_to_lenv (* function to apply *)
      input_bindings  (* first list *)
      hnode.n_input   (* second list *)
      lenv            (* initial accumulator state *) 
 *)
  in
  print_endline "CG::translate_node intermediate 2" ;
  (* Next, add to it the local variables, set to Unbound *)
  let lenv =
    List.fold_left
      (fun acc x -> add_var_to_lenv acc Unbound x)  (* function to apply *)
      lenv                       (* initial acc state *)
      (List.rev hnode.n_local)              (* list *)
    (*
    List.fold_right
      (add_var_to_lenv Unbound)  (* function to apply *)
      hnode.n_local              (* list *)
      lenv                       (* initial acc state *)
     *)
  in
  (* Next, add the output variables, set to Unbound *)
  let lenv =

    List.fold_left
      (fun acc x -> add_var_to_lenv acc Unbound x)  (* function to apply *)
      lenv                       (* initial acc state *)
      (List.rev hnode.n_output)            (* list *)
      (*
    List.fold_right
      (add_var_to_lenv Unbound)  (* function to apply *)
      hnode.n_output             (* list *)
      lenv                       (* initial acc state *)
       *)
  in
  print_endline "CG::translate_node intermediate 3" ;
  (*
  cg_debug_print
    ("translate_node before creation of extra variables:\n"
     ^(print_local_env lenv)
     ^"\n") ;
   *)
  (* Finally, traverse the statements to:
   * - add the variables that we will synthesize 
   *   automatically.
   * - build the lists of variable identifiers that will
   *   be passed from variable construction to the second
   *   phase. *)
  let lenv,extra_var_idents =
    (* Aux function for building new variables *)
    let build_aux_variables
	  ((lenv:local_environment),
	   (extra_var_idents:Idents.var_ident list list),
           (cnt:int))
	  (eq:eq)
	: local_environment*(Idents.var_ident list list)*int =
      if cnt mod 1000 = 0 then
        begin
          Printf.printf "\tTraversed %d nodes\n" cnt ;
          flush stdout
        end ;
      match eq.eq_rhs.e_desc with
      | Eapp (app, extvalue_list, reset_ident_opt) ->
	 begin
	   match app.a_op with
	   | ( Efun fun_name | Enode fun_name) ->
              (*
              print_endline
                ("build_aux_variables - traversing fun with name "
                 ^(Names.fullname fun_name)^".\n") ;
               *)
	      if app.a_inlined then
                (lenv,extra_var_idents@[[]],cnt+1) 
              else
                begin
		  let (fb : function_binding) =
		    let hnode = Modules.find_value fun_name in
		    translate_function genv fun_name hnode
		  in
		  match fb.stateful with
		  | None -> (lenv,extra_var_idents@[[]],cnt+1)
		  | Some stateful_binding ->
		     let base_name =
		       let curr_seq = !(stateful_binding.state_seq) in
		       stateful_binding.state_seq := curr_seq + 1 ;
		       String.concat
		         ""
		         [
			   qname_to_id fun_name ;
			   if curr_seq = 0 then "" else ("_"^(string_of_int curr_seq)) ;
		         ]
		     in
		     let state_in_var_name = base_name^"_state_in"
		     and state_out_var_name = base_name^"_state_out"
		     in
		     let state_out_var_ident =
		       Idents.ident_of_name ~reset:false state_out_var_name
		     and state_in_var_ident =
		       Idents.ident_of_name ~reset:false state_in_var_name
		     in
		     let lenv_no_reset =
		       VarEnv.add
		         state_in_var_ident
		         {
			   iv_ident = state_in_var_ident ;
			   iv_binding = Unbound
		         }
		         (VarEnv.add
			    state_out_var_ident
			    {
			      iv_ident = state_out_var_ident ;
			      iv_binding = Unbound
			    }
			    lenv
		         )
		     in
		     let new_reset_vars =
		       match reset_ident_opt with
		       | None -> reset_vars
		       | Some new_reset_var ->
			  new_reset_var::reset_vars
		     in
		     match new_reset_vars with
		     | [] ->
		        (
			  lenv_no_reset,
			  extra_var_idents@[[state_out_var_ident;state_in_var_ident]],
                          cnt+1
		        )
		     | [reset_var] ->
		        let fby_in_var_name = base_name^"_fby_in" in
		        let fby_in_var_ident =
			  Idents.ident_of_name ~reset:false fby_in_var_name
		        in
		        (
			  VarEnv.add
			    fby_in_var_ident
			    {
			      iv_ident = state_in_var_ident ;
			      iv_binding = Unbound
			    }
			    lenv_no_reset,
			  extra_var_idents@[[state_out_var_ident;state_in_var_ident;fby_in_var_ident]],
                          cnt+1
		        )
		     | _ ->
		        failwith "Cannot handle more than one reset var."
                end
	   | _ -> (lenv,extra_var_idents@[[]],cnt+1)
	 end
      | _ -> (lenv,extra_var_idents@[[]],cnt+1)
    in
    print_endline ("CG::translate_node processing "
                   ^(string_of_int (List.length hnode.n_equs))
                   ^" equations") ;
    let res1,res2,_ =
      List.fold_left
        build_aux_variables
        (lenv,[],0)
        hnode.n_equs
    in
    (res1,res2)
  in
  print_endline "CG::translate_node intermediate 4" ;
  (*
  cg_debug_print
    ("translate_node after creation of extra variables:\n"
     ^(print_local_env lenv)
     ^"\n") ;
   *)
  (* Now, translate the equations *)
  begin
    try
      List.iter2
	(translate_eq genv lenv reset_vars)
	hnode.n_equs
	extra_var_idents
    with
      Invalid_argument _ ->
      failwith
	(String.concat
	   ""
	   [
	     "translate_node: Incompatible list lengths: eqs: " ;
	     string_of_int (List.length hnode.n_equs) ;
	     " lsts: " ;
	     string_of_int (List.length extra_var_idents) ;
	     "\n" ;
	   ]
	)
  end ;
  print_endline "CG::translate_node intermediate 5" ;

  (*
  Printf.printf
    "After translation of equations:\n%s\n"
    (print_local_env lenv) ;
  flush stdout ;
   *)

  (* Finally, extract the output bindings from the 
   * local environment *)
  let extract_var_from_lenv (lenv:local_environment) var_dec =
    (translate_var lenv var_dec.v_ident).iv_binding
  in
  let result = 
    List.map
      (extract_var_from_lenv lenv)
      hnode.n_output
  in
  (*
  let _ =
    Printf.printf
      "translate_node call on %s completed.\n"
      hnode.n_name.name
  in
   *)
  print_endline "CG::translate_node intermediate finished" ;
  result

  

(* Second pass, bind input parameters and clocks *)
let rec evaluate_ivar_in_cklb ivar clkb =
  match clkb with
  | PrimitiveClock
  | NeverClock -> None
  | DerivedClock (base_clkb, constructor_name, ivar') ->
     if ivar' == ivar
     then Some constructor_name
     else evaluate_ivar_in_cklb ivar base_clkb
  | _ -> assert false
		
let build_clk_term constructor_name (rvalue, clock) =
  let predicate =
    match constructor_name with
    (* Test the value against a constructor *) 
    | { Names.qual = Names.Pervasives; name = "false" } -> Not (Predicate rvalue)
    | { Names.qual = Names.Pervasives; name = "true" } -> Predicate rvalue
    | _ -> raise (Not_implemented "build_clk_term")
  in
  Test (BaseClock clock, predicate)

let memo_clock_exp (genv:cg_environment) clk_exp clk_dependencies : clk =
  try
    ClEnv.find clk_exp genv.clock_definitions
  with Not_found ->
    let gclock = add_clock genv.cg (Derived clk_exp) clk_dependencies in
    genv.clock_definitions <- ClEnv.add clk_exp gclock genv.clock_definitions;
    gclock

(* From an environment and a binding, produce a clock *)
let rec resolve_clock (genv:cg_environment) (c:clock_binding) : clk =
  let rec resolve_clock_exp (c:clock_binding) : clk_exp*(clock_rvalue list) =
    match c with 
    | PrimitiveClock ->
       failwith "Case handled by resolve_clock (PrimitiveClock)."
    | NeverClock ->
       failwith "Case handled by resolve_clock (NeverClock)."
    | DerivedClock (base_clkb, constructor_name, ivar) ->
       (* Printf.fprintf stderr "resolve_clock_exp::DerivedClock\n" ;*)
       let clk_dependencies : clock_rvalue list =
	 resolve_binding
	   genv
	   base_clkb
	   ivar.iv_binding
       in
       let clk_exp =
	 let tmp =
	   List.map
	      (build_clk_term constructor_name)
	      clk_dependencies
	 in
	 if tmp = [] then
	   failwith "mk_union on empty list."
	 else
	   mk_union tmp
       in
       (clk_exp,clk_dependencies)
    | UnionClock l ->
       (* Printf.fprintf stderr "resolve_clock_exp::UnionClock\n" ;*)
       let nvl = List.filter (fun c -> c <> NeverClock) l in
       if nvl = [] then
	 (BaseClock genv.never_clock, [])
       else
	 let clk_exps, dependencies =
	   List.split (List.map resolve_clock_exp nvl)
	 in
	 let clk_exp = mk_union clk_exps
	 and clk_dependencies = List.fold_left (@) [] dependencies
	 in
	 (clk_exp,clk_dependencies)
    | InterClock l ->
       (* Printf.fprintf stderr "resolve_clock_exp::InterClock\n" ;*)
       if l = [] then
	 failwith "mk_inter on empty list."
       else 
	 let clk_exps, dependencies =
	   List.split (List.map resolve_clock_exp l)
	 in
	 let clk_exp = mk_inter clk_exps
	 and clk_dependencies = List.fold_left (@) [] dependencies
	 in
	 (clk_exp,clk_dependencies)
  in
  match c with
  | PrimitiveClock -> genv.primitive_clock
  | NeverClock -> genv.never_clock
  | _ ->
     let clk_exp,clk_dependencies =
       resolve_clock_exp c
     in
     match clk_exp with
     | BaseClock _ ->
	(* This case only occurs when the construction process 
	 * produces a never clock. *)
	genv.never_clock
     | _ -> 
	memo_clock_exp genv clk_exp clk_dependencies
		    
and resolve_binding
      (genv:cg_environment)
      (clkb:clock_binding)
      (binding:variable_binding) : clock_rvalue list =
  (* Recursively build a list of variables with clocks. *)
  (* Clocks are built during the recursion and solved at leaves. *)
  let rec resolve
	    (clkb:clock_binding)
	    (r:clock_rvalue list)
	    (x:variable_binding) : clock_rvalue list =
    match x with 
    | Unbound ->
       assert false
	      
    | Alias (ivar) ->
       if ivar.iv_binding == x then
	 failwith "Recursive binding. Aborting...\n"
       else 
	 resolve clkb r ivar.iv_binding
		 
    | Merge (ivar, l) ->
       let merge r (constr, binding) =
         match evaluate_ivar_in_cklb ivar clkb with
         | Some constr' when constr' = constr ->
	    (* The variable is already evaluated *)
            resolve clkb r binding
         | Some _ ->
	    (* The path is unfeasible, ignore it *)
            r
         | None ->
            resolve (DerivedClock (clkb, constr, ivar)) r binding
       in
       List.fold_left merge r l

    | Defined_Variable var ->
       (Variable var,resolve_clock genv clkb) :: r

    | Constant_Binding clk_exp ->
       (Const clk_exp,resolve_clock genv clkb)::r
						  
  in
  resolve clkb [] binding


let bind_input
      (genv:cg_environment)
      ck
      (input_port,_)
      (binding:variable_binding) : input_port =
  {
    input_port_name = input_port.arg_name ;
    input_port_arcs = resolve_binding genv ck binding ;
  }
    
let bind_inputs
      (genv:cg_environment)
      ((block:block),
       (clkb:clock_binding),
       (fun_inputs:(argument*(string option)) list),
       (bindings:variable_binding list)) : unit
  =
  (* Build (if needed) and set the clock of the block *)
  block.block_clk <- resolve_clock genv clkb;
  (* Bind block inputs, by iterating jointly over the 
   * function inputs and the bindings. *)
  block.block_inputs <- List.map2
                          (bind_input genv clkb)
                          fun_inputs
                          bindings

(* Initial environment *)
let build_valued_const_env (constants : (const_dec*Types.static_exp) list) : Types.static_exp QualEnv.t =
  List.fold_left
    (fun acc_env (const_dec,exp) ->
      QualEnv.add const_dec.c_name exp acc_env
    )
    QualEnv.empty
    constants
    
let build_predef_genv (constants : (const_dec*Types.static_exp) list) =
  (* Predefined clocks and types *)
  let primitive_clock =
    {
      clk_index = 0 ;
      clk_id = Some "Tick" ;
      clk_desc = Primitive ;
      clk_dependencies = []
    }
  in
  let never_clock =
    {
      clk_index = 1 ;
      clk_id = Some "Never" ;
      clk_desc = Derived
		   (Test
		      (
			BaseClock primitive_clock,
			Predicate (Const (Boolean false))
		      )
		   )  ;
      clk_dependencies = []
    }
  and ty_bool = { ty_index = 0 ; ty_id = "bool" ; ty_desc = PredefinedType }
  and ty_int = { ty_index = 1 ; ty_id = "int" ; ty_desc = PredefinedType } in
  let type_list = [ (Initial.pint, ty_int) ; (Initial.pbool, ty_bool) ] in
  {
    type_bindings =
      List.fold_left
	(fun env (n, t) -> TyEnv.add (Types.Tid n) t env)
	TyEnv.empty
	type_list ;
    constant_bindings = QualEnv.empty ;
    valued_mls_constants = build_valued_const_env constants ;
    function_bindings = QualEnv.empty ;
    input_bindings = [] ;
    clock_definitions = ClEnv.empty ;
    operators = StringMap.empty ;
    last_constant_index = 0 ;
    primitive_clock = primitive_clock ;
    never_clock = never_clock ; 
    cg =
      {
	types = List.map snd type_list ;
	functions = [] ;
	constants = [] ;
	variables = [];
	clocks = [never_clock;primitive_clock];
	relations = [];
	partitions = [];
	blocks = [];
        period = None ;
      };
    cdependencies = [];
    cheader = [];
    csource = [];
  }

(* Before the synchronous execution starts, a partition 
 * initialization phase is needed in order to set up the
 * application state. Valentin's version of the code
 * generation uses the classical translation pattern 
 * of Heptagon and represents this init phase as the first
 * synchronous execution step.
 * But in doing so, it also transforms reset function 
 * calls from constant initializations into synchronous
 * function calls, and the state variables into somewhat
 * weird normal variables updated through side effects. *)
let build_init_var (genv:cg_environment) =
  (* Determine in which partition to place the boot
   * protocol. *)
  let init_code_partition_opt =
    match !Compiler_options.control_partition_name with
    | None -> None
    | Some str -> Some (translate_partition str)
  in
  (* Build the boot protocol in an empty variable context,
   * and extract the single variable it built. *)
  let va_init =
    match
      translate_fby
	genv
	(VarEnv.empty)
	Clocks.Cbase
	(Some (Types.mk_static_exp Initial.tbool (Types.Sbool true)))
	(extvalue_false Clocks.Cbase)
	init_code_partition_opt
	false (* non-preemptive *)
	None (* No release date *)
	None (* No deadline *)
    with 
    | [Defined_Variable va] -> va
    | _ -> assert false
  in
  (* Bind this variable to a new identifier with name "init" *)
  {
    iv_ident = Idents.ident_of_name "init";
    iv_binding = Defined_Variable va_init
  }
    

(* Extraction of the clocked graph from environment *)
 
let extract_cg (genv:cg_environment) p = {
  types = List.rev genv.cg.types ;
  functions = List.rev genv.cg.functions ;
  constants = List.rev genv.cg.constants ;
  variables = List.rev genv.cg.variables ;
  clocks = List.rev genv.cg.clocks ;
  relations = List.rev genv.cg.relations ;
  partitions = List.rev genv.cg.partitions ;
  blocks = List.rev genv.cg.blocks ;
  period = p ;
}


(* Find target node *)

let find_target_node { p_desc } =
  let lqname = !Compiler_options.mainnode in
  if (lqname=[]) then (
    Format.eprintf "A main node with no input arguments must be given.@.";
    raise Errors.Error
  );
  if ((List.length lqname)>1) then (
    Format.eprintf "Warning: multiple main node declared. Last one selected.@.";
  );

  (* Main node is the last target node used *)
  let qname = List.hd lqname in
  let node =
    try
      let desc = List.find (function Pnode n -> n.n_name = qname | _ -> false) p_desc in
      match desc with
      | Pnode n -> n
      | _ -> assert false
    with Not_found ->
        Format.eprintf "The node %s does not exists.@." (Names.shortname qname);
        raise Errors.Error
  in
  node


(* Entry point of the translation *)

    
let program p =
  print_endline "CG transformation:start" ;
  (*
  let _ =
    Printf.printf
      ">>>start translation from MiniLS to CG         \n"
  in
   *)
  (* Initialize the partition information *)
  let initial_part_map =
    let tmp_map = 
      match !Compiler_options.system_partition_id with
      | None -> StringMap.empty
      | Some id -> StringMap.singleton "System" id
    in
    match !Compiler_options.sync_partition_id with
    | None -> tmp_map
    | Some id -> StringMap.add "Sync" id tmp_map
  in
  partition_map := initial_part_map ;
  
  print_endline "CG transformation:intermediate 1" ;

  (* Extract the top-level constants of the file that do have a
   * value. These constants must be defined in the GC file. *)
  let constants =
    List.fold_left
      (fun acc_lst x ->
        match x with
        | Pconst c ->
           begin 
             match c.c_value with
             | None -> acc_lst
             | Some e -> (c,e)::acc_lst
           end
        | _ -> acc_lst
      )
      []
      p.p_desc
  in

  (* print_endline "CG transformation:intermediate 2" ; *)

  (* Find the target node *)
  let target_node = find_target_node p in
  if target_node.n_input <> [] then
    begin
      Format.eprintf "The top-level node must not have inputs.@.";
      raise Errors.Error
    end;


  (* print_endline "CG transformation:intermediate 3" ; *)

  (* Init callgraph environement for module opening *)
  Callgraph.info.Callgraph.opened <-
    Names.ModulEnv.add p.p_modname p Names.ModulEnv.empty ;


  (* print_endline "CG transformation:intermediate 4" ; *)

  (* Build the clocked graph *)
  let genv = build_predef_genv (constants) in


  (* print_endline "CG transformation:intermediate 4.5" ; *)


  (* Iteratively build objects (constants, blocks, variables, types, 
   * etc.). *)
  (* TODO - step 1 - traverse the node and build the needed extra
   * variables just after reading the declarations of the node. *)
  (* let init_local_variable = build_init_var genv in*)
  ignore (translate_node genv [] target_node []) ;


  (* Bind the already built objects together and build clocks,
   * arcs, etc. *)
  (* print_endline "CG transformation:intermediate 5: binding inputs" ;*)
  List.iter
    (bind_inputs genv)
    genv.input_bindings ;

  (* Extract the clocked graph from the environment *)
  (* print_endline "CG transformation: intermediate 6: 
   * extract CG from environment.\n" ;*)
  let cg_without_partitions = extract_cg genv target_node.n_period in
  let cg_without_variable_at =
    let partition_set = 
      StringMap.fold
	(fun pname pid acc_part_table ->
	 IntMap.add
	   pid
	   {
	     part_index = pid ;
	     part_id = pname ;
	   }
	   acc_part_table
	)
	!partition_map
	IntMap.empty
    in
    let _,ordered_partition_list =
      List.split (IntMap.bindings partition_set)
    in
    { cg_without_partitions with
      partitions = ordered_partition_list }    
  in
  
  (* JP - adding the AT fields on variables *)
  (*
  let _ =
    let fmt_stdout = Format.formatter_of_out_channel stdout in
    Cg_printer.print_clocked_graph fmt_stdout cg_without_variable_at
  in
   *)
  (* print_endline "CG transformation: intermediate 7: add var AT fields.\n" ;*)
  let (cg:clocked_graph) =
    let (delay_output_variables:IntSet.t) =
      List.fold_left
        (fun acc_set blk ->
          match blk.block_function with
          | DelayBlock _ ->
             begin
               match blk.block_outputs with
               | [oport] ->
                  IntSet.add
                    oport.output_port_var.var_index
                    acc_set
               | _ -> failwith "cg_main.ml:program - delay with bad output.\n"
             end
          | _ -> acc_set
        )
        IntSet.empty
        cg_without_variable_at.blocks
    in
    let (vars_with_at:variable IntMap.t) =
      (* Build maps from var names and var indices to var records *)
      let (var_map_by_name:variable StringMap.t),
          (var_map_by_id:variable IntMap.t) =
        List.fold_left
          (fun (acc_map,acc_map2) var ->
            let new_acc_map = 
              match var.var_name with
              | None -> acc_map (* Unnamed variables cannot be "at" destinations *)
              | Some name ->
                 if StringMap.mem name acc_map then
                   begin
                     Format.eprintf "Filling in variables' at fields - two variables with same name.@.";
                     raise Errors.Error
                   end
                 else
                   StringMap.add name var acc_map
            and new_acc_map2 =
              IntMap.add var.var_index var acc_map2
            in
            (new_acc_map,new_acc_map2)
          )
          (StringMap.empty,IntMap.empty)
          cg_without_variable_at.variables
      in
      (* From the local node take the list of local variables and store the
       * correspondence from variable names to linearity names, for variables
       * having a linearity *)
      let (node_at:string IntMap.t) =
        List.fold_left
          (fun acc_map (var_dec:Minils.var_dec) ->
            match var_dec.v_linearity with
            | Ltop -> acc_map
            | Lat name ->
               let var_idx =
                 let var_name = Idents.name var_dec.v_ident in
                 let variable = StringMap.find var_name var_map_by_name in
                 variable.var_index
               in
               (* Printf.printf "Found linearity %s -> %s\n" var_name name ; *)
               IntMap.add var_idx name acc_map
            | _ -> failwith "Bad linearity"
          )
          IntMap.empty
          target_node.n_local
      in
      (* Determine for each linearity name the set of variables using it *)
      let (linearity_classes:IntSet.t StringMap.t) =
        IntMap.fold
          (fun (var_id:int)
               (at_name:string)
               (acc_map:IntSet.t StringMap.t) ->
            let var_set =
              try
                StringMap.find at_name acc_map
              with Not_found -> IntSet.empty
            in
            StringMap.add
              at_name
              (IntSet.add var_id var_set)
              acc_map
          )
          node_at
          StringMap.empty
      in
      (* Choose one variable from each linearity class -- the one that
       * will be allocated. *)
      let (representative_var:string StringMap.t) =
        StringMap.map
          (fun var_ids ->
            let (representative_var_idx:int) =
              try 
                IntSet.min_elt 
                  (IntSet.diff var_ids delay_output_variables)
              with Not_found -> 
                failwith "cg_main.ml:program All vars with given AT are delay outputs.\n"
            in
            let representative_var =
              try
                IntMap.find representative_var_idx var_map_by_id
              with Not_found -> failwith "Missing var record in partial CG.\n"
            in
            match representative_var.var_name with
            | None -> failwith "Unnamed variable with AT.\n"
            | Some s -> s
          )
          linearity_classes          
      in
      
      (* print_endline "CG transformation: intermediate 8: identified at requirements.\n" ;*)
      flush stdout ;
      (* Iterate over the map from node names to linearity names *)
      IntMap.fold
        (fun var_idx at_name acc_variables ->
          let var =
            try
              IntMap.find var_idx var_map_by_id
            with Not_found -> 
              failwith "Missing variable in variable map."
          and at_var =
            let rep_var_name = 
              try
                StringMap.find
                  at_name
                  representative_var
              with Not_found ->
                failwith
                  (Printf.sprintf "Missing rep variable for at class %s." at_name)
            in
            try
              StringMap.find
                rep_var_name
                var_map_by_name
            with Not_found ->
              failwith
                (Printf.sprintf "Missing variable %s in variable map." rep_var_name)
          in
          var.var_at <- Some (at_var.var_index) ;
          IntMap.add var.var_index var acc_variables
        )
        node_at
        var_map_by_id
    in
    { cg_without_variable_at with
      variables =
        List.rev
          ( IntMap.fold
              (fun _ var acc_lst ->  var::acc_lst)
              vars_with_at
              []
          )
    }
  in
  (* Open output file *)
  let basename =
    Compiler_utils.filename_of_name (Names.modul_to_string p.p_modname)
  in
  let out = open_out (basename ^ ".gc") in
  let fmt = Format.formatter_of_out_channel out in

  (* Print results *)
  Cg_printer.print_clocked_graph fmt cg ;

  (*
  (* Output C glue *)
  output_cfile
    (basename ^ ".h")
    (C.Cheader (genv.cdependencies, genv.cheader)) ;
  output_cfile
    (basename ^ ".c")
    (C.Csource genv.csource) ;
   *)
  (*
  let _ =
    Printf.printf
      ">>>completed translation from MiniLS to CG.\n"
  in
   *)
  ()
