(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* Compiler options *)

open Names

(* version of the compiler *)
let version = "0.4"
let date = "DATE"

(* standard module *)
let pervasives_module = Pervasives
let standard_lib = "STDLIB"
let standard_lib = try Sys.getenv "HEPTLIB" with Not_found -> standard_lib

(* list of modules initially opened *)
let default_used_modules = ref [pervasives_module]
let set_no_pervasives () = default_used_modules := []

(* load paths *)
let load_path = ref ([standard_lib])


let set_stdlib p =
  load_path := [p]
and add_include d =
  load_path := d :: !load_path;;

(* where is the standard library *)
let locate_stdlib () =
  print_string (try Sys.getenv "HEPTLIB" with Not_found -> standard_lib);
  print_newline ()

let show_version () =
  Format.printf "The Heptagon compiler, version %s (%s)@."
    version date;
  locate_stdlib ()


(* other options of the compiler *)
let verbose = ref false
let print_types = ref false

let assert_nodes : name list ref = ref []
let add_assert nd = assert_nodes := nd :: !assert_nodes

let simulation = ref false
let simulation_node : name ref = ref ""
let set_simulation_node s =
  simulation := true;
  simulation_node := s

let hepts_simulation = ref false

let create_object_file = ref false

let boolean = ref false

(* Target languages list for code generation *)
let target_languages : string list ref = ref []

let add_target_language s =
  if s = "z3z" then boolean := true; (* TODO use load_conf instead *)
  target_languages := s :: !target_languages

(* Optional path for generated files (C or Java) *)
let target_path : string option ref = ref None

let set_target_path path =
  target_path := Some path


let java_queue_size = ref 1l
let java_queue_nb = ref 1l

let set_java_queue_size i = java_queue_size := Int32.of_int i

let no_async = ref false

let full_type_info = ref false

let full_qual_info = ref false

let stateful_info = ref false

let full_name = ref false

let causality = ref true
let init = ref true

let inline : qualname list ref = ref []
let add_inlined_node s = inline := s :: !inline

let flatten = ref false

let deadcode = ref false

let tomato = ref false

let tomato_nodes : qualname list ref = ref []

let add_tomato_node s = tomato_nodes := s :: !tomato_nodes

let tomato_check : qualname list ref = ref []

let add_tomato_check s = tomato_check := s :: !tomato_check

let do_iterator_fusion = ref false

let do_scalarize = ref false
let do_simplify = ref true

let do_lho = ref false

let do_mem_alloc = ref false
let do_linear_typing = ref false

let do_mem_alloc_and_typing () =
  do_mem_alloc := true;
  do_linear_typing := true

let use_old_scheduler = ref false

let no_clocking_error = ref false


let normalize_register_outputs = ref true
let strict_ssa = ref false
(* if this option is on, generate code that first copies the whole array and then modifies one element.
   Otherwise, generate two loops so that each element in the array is only assigned once. *)
let memcpy_array_and_struct = ref true

let set_strict_ssa () =
  strict_ssa := true;
  memcpy_array_and_struct := false

let functions_are_classes = ref true

let unroll_loops = ref false

let enforce_callgraph = ref false

let optim = ref false
let do_optim () =
(*  do_iterator_fusion := true; *)(*TODO reset when itfusion is fixed *)
  do_mem_alloc_and_typing ();
  tomato := true;
  deadcode := true


let check_options () =
  let err m = raise (Arg.Bad m) in
  if !strict_ssa
  then (
    if !do_mem_alloc then err "Unable to activate memory allocation with strict SSA activated.";
    if !do_linear_typing then err "Unable to activate linear typing with strict SSA activated."
  )

let interf_all = ref false

let time_passes = ref false

let doc_verbose = " Set verbose mode"
and doc_version = " The version of the compiler"
and doc_print_types = " Print types"
and doc_include = "<dir> Add <dir> to the list of include directories"
and doc_stdlib = "<dir> Directory for the standard library"
and doc_object_file = " Only generate a .epo object file"
and doc_sim = "<node> Create simulation for node <node>"
and doc_hepts = " Simulation for hepts (graphical simulator)"
and doc_locate_stdlib = " Locate standard libray"
and doc_no_pervasives = " Do not load the pervasives module"
and doc_flatten = " Inline everything"
and doc_enforce_callgraph = " Prevent generation of templates: enforce callgraph expansion"
and doc_target = "<lang> Generate code in language <lang> (with <lang>=c, java or z3z)"
and doc_full_type_info = " Print full type information"
and doc_full_qual_info = " Print full qualifier information"
and doc_stateful_info = " Print stateful information"
and doc_full_name = " Print full variable name information"
and doc_target_path = "<path> Generated files will be placed in <path> (the directory is cleaned)"
and doc_boolean = " Translate enumerated values towards boolean vectors"
and doc_deadcode = " Deadcode removal"
and doc_nocaus = " Disable causality analysis"
and doc_noinit = "Disable initialization analysis"
and doc_assert = "<node> Insert run-time assertions for boolean node <node>"
and doc_inline = "<node> Inline node <node>"
and doc_itfusion = " Enable iterator fusion"
and doc_tomato = " Enable automata minimization"
and doc_lho = " Enable LHO"
and doc_strict_ssa = " Ensure that the generated code is SSA, even for array elements."
and doc_memalloc = " Enable memory allocation and linear annotations"
and doc_memalloc_only = " Enable memory allocation"
and doc_java_queue_size = " Set the default input queue size for async nodes, 0 means threadPool, \
default to 1"
and doc_noasync = " Erase asynchronous calls and futures."
and doc_java_queue_nb = " Set the default thread number for async nodes, default to 1"
and doc_linear_only = " Enable linear annotations"
and doc_interf_scheduler = " Use the old scheduler"
and doc_no_clocking_error = " Disable clocking errors (use at your own risk!)"
and doc_optim = " Optimize with deadcode, tomato, itfusion and memalloc"
and doc_interf_all = " Perform memory allocation on all types"
and doc_unroll = " Unroll all loops"
and doc_time_passes = " Time compilation passes"
and doc_compile = " Compile multiple files (the remainings)"
