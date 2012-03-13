(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)


open Misc
open Modules
open Location
open Compiler_utils
open Compiler_options


let compile_interface modname source_f =

  (* output file names *)
  let output = String.uncapitalize modname in
  let epci_f = output ^ ".epci" in

  (* input/output channels *)
  let source_c, lexbuf = lexbuf_from_file source_f in
  let epci_c = open_out_bin epci_f in
  let close_all_files () = close_in source_c; close_out epci_c in

  try
  (* Process the [lexbuf] to an Heptagon AST *)
    let p = Hept_parser_scoper.parse_interface modname lexbuf in
    if !print_types then Global_printer.print_interface Format.std_formatter;

    (* Process the interface *)
    let p = Hept_compiler.compile_interface p in
    (* Output the .epci *)
    output_value epci_c (Modules.get_current_module ());
    (* Translate to Obc *)
    let p = Hept2mls.interface p in
    (* Generate the sequential code *)
    Mls2seq.interface p;
    close_all_files ()
  with
    | x -> close_all_files (); raise x

(* [modname] is the module name, [source_f] is the source file *)
let compile_program modname source_f =

  (* output file names *)
  let output = String.uncapitalize modname in
  let epci_f = output ^ ".epci" in
  let mls_f = output ^ ".mls" in

  (* input/output channels *)
  let source_c, lexbuf = lexbuf_from_file source_f in
  let epci_c = open_out_bin epci_f in
  let mls_c = open_out mls_f in
  let close_all_files () = close_in source_c; close_out epci_c; close_out mls_c in

  try
  (* Activates passes according to the backend used *)
    Mls2seq.load_conf ();
  (* Record timing information *)
    Compiler_timings.start_compiling modname;
  (* Process the [lexbuf] to an Heptagon AST *)
    let p = Hept_parser_scoper.parse_program modname lexbuf in
  (* Process the Heptagon AST *)
    let p = Hept_compiler.compile_program p in
  (* Compile Heptagon to MiniLS *)
    let p = do_pass "Translation into MiniLS" Hept2mls.program p Mls_compiler.pp in
  (* Output the .mls *)
    do_silent_pass "MiniLS serialization" (fun () -> Mls_printer.print mls_c p) ();
  (* Process the MiniLS AST *)
    let p = Mls_compiler.compile_program p in
  (* Output the .epci *)
    output_value epci_c (Modules.get_current_module ());
  (* Generate the sequential code *)
    Mls2seq.program p;
    close_all_files ();
    Compiler_timings.report_statistics ()
  with x -> close_all_files (); raise x



let compile source_f =
  let modname = source_f |> Filename.basename |> Filename.chop_extension |> String.capitalize in
  let modul = Name_utils.modul_of_string modname in
  Initial.initialize modul;
  source_f |> Filename.dirname |> add_include;
  check_options ();
  match Misc.file_extension source_f with
    | "ept" -> compile_program modname source_f
    | "epi" -> compile_interface modname source_f
    | ext -> raise (Arg.Bad ("Unknow file type: " ^ ext ^ " for file: " ^ source_f))



(** [main] function to be launched *)
let main () =
  let read_qualname f = Arg.String (fun s -> f (Name_utils.qualname_of_string s)) in
  try
    Arg.parse
      [
        "-v",Arg.Set verbose, doc_verbose;
        "-version", Arg.Unit show_version, doc_version;
        "-i", Arg.Set print_types, doc_print_types;
        "-I", Arg.String add_include, doc_include;
        "-where", Arg.Unit locate_stdlib, doc_locate_stdlib;
        "-stdlib", Arg.String set_stdlib, doc_stdlib;
        "-c", Arg.Set create_object_file, doc_object_file;
        "-s", Arg.String set_simulation_node, doc_sim;
        "-hepts", Arg.Set hepts_simulation, doc_hepts;
        "-bool", Arg.Set boolean, doc_boolean;
        "-deadcode", Arg.Set deadcode, doc_deadcode;
        "-tomato", Arg.Set tomato, doc_tomato;
        "-tomanode", read_qualname add_tomato_node, doc_tomato;
        "-tomacheck", read_qualname add_tomato_check, "";
        "-inline", read_qualname add_inlined_node, doc_inline;
        "-flatten", Arg.Set flatten, doc_flatten;
        "-assert", Arg.String add_assert, doc_assert;
        "-nopervasives", Arg.Unit set_no_pervasives, doc_no_pervasives;
        "-target", Arg.String add_target_language, doc_target;
        "-targetpath", Arg.String set_target_path, doc_target_path;
        "-nocaus", Arg.Clear causality, doc_nocaus;
        "-noinit", Arg.Clear init, doc_noinit;
        "-fti", Arg.Set full_type_info, doc_full_type_info;
        "-fqi", Arg.Set full_qual_info, doc_full_qual_info;
        "-statefuli", Arg.Set stateful_info, doc_stateful_info;
        "-fname", Arg.Set full_name, doc_full_name;
        "-itfusion", Arg.Set do_iterator_fusion, doc_itfusion;
        "-strict_ssa", Arg.Set strict_ssa, doc_strict_ssa;
        "-memalloc", Arg.Unit do_mem_alloc_and_typing, doc_memalloc;
        "-java_queue_size", Arg.Int set_java_queue_size, doc_java_queue_size;
        "-only-memalloc", Arg.Set do_mem_alloc, doc_memalloc_only;
        "-only-linear", Arg.Set do_linear_typing, doc_linear_only;
        "-old-scheduler", Arg.Set use_old_scheduler, doc_interf_scheduler;
        "-unroll", Arg.Set unroll_loops, doc_unroll;
        "-no-clocking-error", Arg.Set no_clocking_error, doc_interf_scheduler;
        "-O", Arg.Unit do_optim, doc_optim;
        "-mall", Arg.Set interf_all, doc_interf_all;
        "-time", Arg.Set time_passes, doc_time_passes;
      ]
        compile errmsg;
  with
    | Errors.Error -> exit 2;;


(** Launch the [main] *)
main ()
