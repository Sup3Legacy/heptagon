type lopht_id = string

(* Types of variables and functions inputs/outputs *) 
type ty = {
  ty_index : int;
  ty_id : lopht_id;
  ty_desc : ty_desc
}
and ty_desc = PredefinedType | SimpleType | EnumeratedType of lopht_id list

(* Functions which can be instanciated in blocks *)
and func = {
  fun_index : int;
  fun_id : lopht_id;
  fun_inputs : (lopht_id * ty) list;
  fun_outputs : (lopht_id * ty) list;
  (* TODO: fun_ensures ? *)
}

(* Constant which can be used for block input *)
and const = {
  cst_index : int;
  cst_id : lopht_id;
  cst_desc : cst_desc;
}
and cst_desc = ExternalConst | InitFunctionConst of func * const_exp list

(* Variables used to connect a source port to multiple target ports *)
and variable = {
  var_index : int;
  var_type : ty;
  var_source_port : lopht_id * block;
  var_allocation : unit option;
}

(* Clock on which blocks are executed or variable transmited *)
and clk = {
  clk_index : int;
  clk_id : lopht_id option;
  clk_desc : clk_desc;
  clk_dependencies : clock_dependency list
}
and clock_dependency = variable * clk
and clk_desc = Primitive | Derived of clk_exp
and clk_exp =
  | BaseClock of clk
  | Union of clk_exp * clk_exp
  | Intersection of clk_exp * clk_exp
  | Difference of clk_exp * clk_exp
  | Subsampling of clk_exp * unit
  | Test of clk_exp * bool_exp
and bool_exp =
  | Predicate of val_exp
  | Equal of variable * val_exp
  | NotEqual of variable * val_exp
  | LowerEqual of variable * val_exp
  | Lower of variable * val_exp
  | GreaterEqual of variable * val_exp
  | Greater of variable * val_exp
  | In of variable * lopht_id list
  | And of bool_exp * bool_exp
  | Or of bool_exp * bool_exp
  | Diff of bool_exp * bool_exp
  | Not of bool_exp
and val_exp =
  | Variable of variable
  | Function of func * val_exp list
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
and rel_kind = EqualClocks | EclusiveClocks | LowerOrEqualClocks

(* Partition of the system *)
and partition = {
  part_index : int;
  part_id : lopht_id;
}

(* Instance of functions which are executed on some clock and linked with other blocks with variables *)
and block = {
  block_index : int;
  block_id : lopht_id option;
  block_clk : clk;
  mutable block_inputs : input_port list;
  mutable block_outputs : output_port list;
  block_function : block_function;
  block_preemptible : bool option;
  block_offset : int option;
  block_deadline : deadline option;
  block_partitions : partition list;
  block_schedule : schedule option;
}
and block_function = DelayBlock of delay | FunBlock of func | ConstBlock of const_exp
and delay = {
  delay_ty : ty;
  delay_depth : int;
  delay_init : const_exp list;
}
and schedule = unit

and input_port = {
  input_port_name: lopht_id;
  input_port_arcs: clock_dependency list;
}
and output_port = {
  output_port_name: lopht_id;
  output_port_var: variable;
}
and deadline = Finite of int * int | Infinite

type clocked_graph = {
  mutable types : ty list; (* Must not be empty *)
  mutable functions : func list; (* Must not be empty *)
  mutable constants : const list;
  mutable variables : variable list; (* Must not be empty *)
  mutable clocks : clk list; (* Must not be empty *)
  mutable relations : rel list;
  mutable partitions : partition list; (* Optional *)
  mutable blocks : block list; (* Must not be empty *)
}
