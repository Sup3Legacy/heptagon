open Lopht_input

(* TODO list
   1/ ensure that there is a correct mapping between the C function names
   wheter they are generated with lopth target or c target.
   2/ transform constant function application into LoPhT equivalent.
   3/ ensute that the produced file is correct, even if it implies to generate
   dummy symbols (function, variable, etc. since these table must not be empty)
   or raise exceptions.
   4/ check int, float and string coding *)
  
  
let program (p : Minils.program) : unit =
  let filename = Compiler_utils.filename_of_name (Names.modul_to_string p.Minils.p_modname) ^ ".gc" in
  let out = open_out filename in
  let fmt = Format.formatter_of_out_channel out in
  let rec ty_int = {ty_index = 0 ; ty_id = "int" ; ty_desc = SimpleType}
  and fun_f = {fun_index = 0 ; fun_id = "f" ; fun_inputs = [("i", ty_int)] ; fun_outputs = [("o", ty_int)]}
  and var_v = {var_index = 0 ; var_type = ty_int ; var_source_port = ("i",block_b) ; var_allocation = None }
  and clk_c = {clk_index = 0 ; clk_id = None ; clk_desc = Primitive ; clk_dependencies = []}
  and block_b = {
    block_index = 0 ;
    block_id = None ;
    block_clk = clk_c ; 
    block_inputs = [] ;
    block_outputs = [] ;
    block_function = FunBlock fun_f ;
    block_preemptible = None ; 
    block_offset = None ;
    block_deadline = None ;
    block_partitions = [] ;
    block_schedule = None
  }
  and cg = {
    types = [ty_int];
    functions = [fun_f];
    constants = [];
    variables = [var_v];
    clocks = [clk_c];
    relations = [];
    partitions = [];
    blocks = [block_b];
  }
  in
  Lopht_printer.print_clocked_graph fmt cg
