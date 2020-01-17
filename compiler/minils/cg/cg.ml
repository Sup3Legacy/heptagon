(*******************************************************************************
 * Fiabilité et Sûreté de Fonctionnement
 * Copyright (c) 2013, 2014 Institut de Recherche Technologique SystemX
 * All rights reserved.
 *******************************************************************************)

let cg_debug_mode = true ;;
let cg_debug_print text =
  if cg_debug_mode 
  then (Printf.fprintf stderr "CG debug: %s\n" text ; flush stderr)
  else ()
;;

open Misc
     
type id = string

(* Types of variables and functions inputs/outputs *) 
type ty = {
  ty_index : int;
  ty_id : id;
  ty_desc : ty_desc
}
and ty_desc = PredefinedType | SimpleType | EnumeratedType of id list

(* Functions which can be instanciated in blocks *)
and func =
  {
    fun_index : int;
    fun_id : id;
    (* On both input and output arguments, an optional string 
     * can specify the location of the argument, and be used 
     * to set one input and one output on the same location.
     * In a minimalistic way, I should only need it on outputs,
     * but having it also on inputs helps with parsing and code
     * generation *)
    fun_inputs : (argument*(string option)) list;
    fun_outputs : (argument*(string option)) list;
    (* TODO: fun_ensures ? *)
  }
and argument =
  (* These are input arguments. For output arguments, the func record
   * above adds another information to the argument record. 
   * In this definition, tuples are formed of argument name and type *)
  {
    arg_name : string ;
    arg_type : ty ;
  }                 


(* Named constant to put in the constant table. *)
and const = {
  cst_index : int;
  cst_id : id;
  cst_ty : ty;
  cst_desc : cst_desc;
}
and cst_desc =
  | ExternalConst
  | LiteralConst of const_exp
  | InitFunctionConst of func * const_exp list
(* Variables used to connect a source port to multiple target ports *)
and variable =
  {
    mutable var_name : string option ;
    var_index : int;
    var_type : ty;
    var_source_port : id * block;
    var_allocation : unit option;
    mutable var_at : int option ; (* If it is Some var_idx then this
                                   * var will use the location of 
                                   * this var index (and has to have the same
                                   * type *)
  }

(* Clock on which blocks are executed or variable transmited *)
and clk = {
  clk_index : int;
  clk_id : id option;
  clk_desc : clk_desc;
  clk_dependencies : clock_rvalue list
}
and clock_dependency = variable * clk
and clock_rvalue = rvalue*clk
and clk_desc = Never | Primitive | Derived of clk_exp
and clk_exp =
  | BaseClock of clk
  | Union of clk_exp * clk_exp
  | Intersection of clk_exp * clk_exp
  | Difference of clk_exp * clk_exp
  | Subsampling of clk_exp * unit
  | Test of clk_exp * bool_exp
and bool_exp =
  | Predicate of rvalue
  | Equal of variable * rvalue
  | NotEqual of variable * rvalue
  | LowerEqual of variable * rvalue
  | Lower of variable * rvalue
  | GreaterEqual of variable * rvalue
  | Greater of variable * rvalue
  | In of variable * id list
  | And of bool_exp * bool_exp
  | Or of bool_exp * bool_exp
  | Diff of bool_exp * bool_exp
  | Not of bool_exp
and rvalue =
  | Variable of variable
  | Function of func * rvalue list
  | Const of const_exp 
and const_exp = 
  | NamedConst of const
  | Integer of int
  | Boolean of bool
  | Float of float
  | String of string

(* Known relations between clocks *)
and rel = {
  rel_index : int;
  rel_kind : rel_kind;
  rel_clocks : clk list; (* Must not be empty *)
}
and rel_kind = EqualClocks | ExclusiveClocks | LowerOrEqualClocks

(* Partition of the system *)
and partition = {
  part_index : int;
  part_id : id;
}

(* Instance of functions which are executed on some clock and linked
 * with other blocks with variables *)
and block = {
  block_index : int;
  block_id : id option;
  mutable block_clk : clk;
  mutable block_inputs : input_port list;
  mutable block_outputs : output_port list;
  block_function : block_function;
  block_preemptible : bool option;
  block_offset : int option;
  block_deadline : int option;
  block_partition : int option ;
  block_schedule : schedule option;
}
and block_function =
  | DelayBlock of delay
  | FunBlock of func
  | ConstBlock of const_exp
and delay = {
  delay_ty : ty;
  delay_depth : int;
  delay_init : const_exp list;
}
and schedule = unit

and input_port = {
  input_port_name: id;
  input_port_arcs: clock_rvalue list;
}
and output_port = {
  output_port_name: id;
  output_port_var: variable;
}

type clocked_graph = {
  mutable types : ty list; (* Must not be empty *)
  mutable functions : func list; (* Must not be empty *)
  mutable constants : const list;
  mutable variables : variable list; (* Must not be empty (JP: why?) *)
  mutable clocks : clk list; (* Must not be empty *)
  mutable relations : rel list;
  partitions : partition list; (* Optional *)
  mutable blocks : block list; (* Must not be empty *)
  period : int option ; 
}


(* Basic functions to add new things to a clocked graph *)

let add_ty cg ty_id ty_desc =
  let ty_index = match cg.types with
    | { ty_index } :: _ -> ty_index + 1
    | [] -> 0
  in
  let gty = {
    ty_index;
    ty_id;
    ty_desc;
  }
  in
  cg.types <- gty :: cg.types;
  gty

let add_clock cg clk_desc clk_dependencies =
  let clk_index = match cg.clocks with
    | { clk_index } :: _ -> clk_index + 1
    | [] -> 0
  in
  let gclock = {
    clk_index ;
    clk_id = None ;
    clk_desc ;
    clk_dependencies ;
  }
  in
  cg.clocks <- gclock :: cg.clocks;
  gclock

let add_constant cg cst_id cst_ty cst_desc =
  let cst_index = match cg.constants with
    | { cst_index } :: _ -> cst_index + 1
    | [] -> 0
  in
  let gconst = {
    cst_index;
    cst_ty;
    cst_id;
    cst_desc;
  }
  in
  cg.constants <- gconst :: cg.constants;
  gconst

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

let add_block
      cg
      block_clk
      block_id
      block_function
      block_partition
      block_preemptive
      block_release
      block_deadline =
  (* Printf.printf "add_block called with preemptive: %B\n" block_preemptive ;*)
  let block_index = match cg.blocks with
    | { block_index } :: _ -> block_index + 1
    | [] -> 0
  in
  let gblock = {
    block_index;
    block_id;
    block_clk;
    block_inputs = [];
    block_outputs = [];
    block_function;
    block_preemptible = Some block_preemptive ;
    block_offset = block_release ;
    block_deadline = block_deadline ;
    block_partition = block_partition ;
    block_schedule = None;
  }
  in
  cg.blocks <- gblock :: cg.blocks;
  gblock


let add_variable
      cg
      (var_name:string option)
      (var_type:ty)
      (fun_arg_name:string)
      gblock =
  let var_index = match cg.variables with
    | { var_index } :: _ -> var_index + 1
    | [] -> 0
  in
  let gvar =
    {
      var_name = var_name ;
      var_index = var_index ;
      var_type = var_type ;
      var_source_port = (fun_arg_name, gblock);
      var_allocation = None;
      var_at = None ;
    }
  in
  cg.variables <- gvar :: cg.variables;
  gvar


(* Expression building *)
let fold_left_1_msg f l msg =
  match l with
  | [] -> invalid_arg ("fold_left_1: empty list"^msg)
  | [x] -> x
  | x :: l -> f (fold_left_1 f l) x

let mk_union (l : clk_exp list) : clk_exp =
  fold_left_1_msg
    (fun e1 e2 -> Union (e1, e2))
    l
    "cg.ml::mk_union"

let mk_inter (l : clk_exp list) : clk_exp =
  fold_left_1_msg
    (fun e1 e2 -> Intersection (e1, e2))
    l
    "cg.ml::mk_inter"

