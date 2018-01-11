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


open Compiler_utils
open Compiler_options


let compile_interface modname source_f =

  (* output file names *)
  let output = String.uncapitalize_ascii modname in
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
    output_value epci_c (Modules.current_module ());
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
  let output = String.uncapitalize_ascii modname in
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
    output_value epci_c (Modules.current_module ());
  (* Generate the sequential code *)
    Mls2seq.program p;
    close_all_files ();
    Compiler_timings.report_statistics ()
  with x -> close_all_files (); raise x

let extract_symbol pd =
  let n =
    match pd with
    | Heptagon.Ptype  { Heptagon.t_name = n } -> n
    | Heptagon.Pnode  { Heptagon.n_name = n } -> n
    | Heptagon.Pconst { Heptagon.c_name = n } -> n
    | Heptagon.Pclass { Heptagon.c_nameclass = n } -> n
    | Heptagon.Pinstance { Heptagon.i_nametype = n } -> n (* Not sure about this one => instance does not have names => might be redundant *) 
  in
  Names.shortname n

let uppercase_first str =
  if (str="") then "" else
  let fstChar = String.get str 0 in
  let fstChar = Char.uppercase_ascii fstChar in
  let fstStr = Char.escaped fstChar in
  fstStr ^ (String.sub str 1 ((String.length str) -1))


let calculate_deps modname source_f =
  (* output file names *)
  let output = String.uncapitalize modname in
  let epci_f = output ^ ".epci" in
  let mls_f = output ^ ".mls" in

  (* input/output channels *)
  let source_c, lexbuf = lexbuf_from_file source_f in
  let epci_c = open_out_bin epci_f in
  let mls_c = open_out mls_f in
  let close_all_files () = close_in source_c; close_out epci_c; close_out mls_c in
  let p = Hept_parser_scoper.parse_program modname lexbuf in
  let deps = List.sort_uniq String.compare
               (!Modules.unknown_nodes @ !Modules.unknown_vars) in
  let { Heptagon.p_desc=pds } = p in
  let syms = List.map extract_symbol pds in
  
  (* Uppercases if needed - don't do it for Safran UC, else we are losing some info *)
  let opt_uppercase_first b str =
    if b then uppercase_first str else str
  in
  
  let source_f = opt_uppercase_first (not !safran_handling) source_f in
  let syms = List.map (opt_uppercase_first (not !safran_handling)) syms in
  let deps = List.map (opt_uppercase_first (not !safran_handling)) deps in
  
  Printf.printf "%s=%s: %s\n" source_f (String.concat " " syms)
                                       (String.concat " " deps)


(* Get some simple stats on the source program (number of equations/ variables/ constants) *)
let simple_stats modname source_f = 
  (* output file names *)
  let output = String.uncapitalize modname in
  let stats_f = output ^ ".stats" in
  
  (* input/output channels *)
  let source_c, lexbuf = lexbuf_from_file source_f in
  let stats_c = open_out stats_f in
  let close_all_files () = close_in source_c; close_out stats_c in
  
  let p = do_silent_pass "Parsing" (Hept_parser_scoper.parse Hept_parser.program) lexbuf in
  
  (* Get the stats of the file *)
  let name_node = modname in
  let num_const = List.fold_left
    (fun cnt pdesc -> match pdesc with
      | Hept_parsetree.Pconst _ -> (cnt+1)
      | _ -> cnt
    )
    0 p.p_desc in
  let (num_eq, num_var_in, num_var_out, num_var_loc) = List.fold_left
    (fun (cnt_eq, cnt_var_in, cnt_var_out, cnt_var_loc) pdesc -> match pdesc with
      | Hept_parsetree.Pnode nd ->
        (cnt_eq + (List.length nd.n_block.b_equs),
          cnt_var_in + (List.length nd.n_input),
          cnt_var_out + (List.length nd.n_output),
          cnt_var_loc + (List.length nd.n_block.b_local)
        )
      | _ -> (cnt_eq, cnt_var_in, cnt_var_out, cnt_var_loc)
    )
    (0,0,0,0) p.p_desc in
  
  Printf.printf "Node %s => (Num_eq : %i) (Num_var_in : %i) (Num_var_out : %i) (Num_var_loc : %i) (Num_const : %i)\n"
    name_node num_eq num_var_in num_var_out num_var_loc num_const;
  close_all_files ()



let compile source_f =
  let modname = source_f
                |> Filename.basename
                |> Filename.chop_extension
                |> String.capitalize_ascii in
  let modul = Names.modul_of_string modname in
  Initial.initialize modul;
  source_f |> Filename.dirname |> add_include;
  check_options ();
  if !calc_deps then
    match Misc.file_extension source_f with
      | "saofd" -> calculate_deps modname source_f
      | "ept" -> calculate_deps modname source_f
      | ext -> raise (Arg.Bad ("Cannot calculate dependencies for files of type: "
                        ^ ext ^ " for file: " ^ source_f))
  else
  if !calc_stats then
    match Misc.file_extension source_f with
      | "saofd" -> simple_stats modname source_f
      | "ept" -> simple_stats modname source_f
      | ext -> raise (Arg.Bad ("Cannot calculate statistics for files of type: "
                        ^ ext ^ " for file: " ^ source_f))
  else
  match Misc.file_extension source_f with
    | "saofd" -> compile_program modname source_f
    | "ept" -> compile_program modname source_f
    | "epi" -> compile_interface modname source_f
    | ext -> raise (Arg.Bad ("Unknow file type: " ^ ext ^ " for file: " ^ source_f))



(** [main] function to be launched *)
let main () =
  let read_qualname f =
    Arg.String (fun s -> f (try Names.qualname_of_string s with
      | Exit -> raise (Arg.Bad ("Invalid name: "^ s)))) in
  try
    Arg.parse
      [
        "-v",Arg.Set verbose, doc_verbose;
        "-version", Arg.Unit show_version, doc_version;
        "-i", Arg.Set print_types, doc_print_types;
        "-I", Arg.String add_include, doc_include;
        "-where", Arg.Unit locate_stdlib, doc_locate_stdlib;
        "-stdlib", Arg.String set_stdlib, doc_stdlib;
        
        "-M", Arg.Set calc_deps, doc_calc_deps;
        "-stats", Arg.Set calc_stats, doc_calc_stats;
        "-safran", Arg.Set safran_handling, doc_safran_handling;
        
        "-open", Arg.String new_file_to_open, doc_files_to_open;
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
        "-mainnode", read_qualname add_main_node, doc_mainnode;
        "-prune", Arg.Set prune, doc_prune;
        "-copyRemoval", Arg.Set copyRemoval, doc_copyRemoval;
        "-arrayDestruct", Arg.Set arrayDestruct, doc_arrayDestruct;

        "-depGraph", Arg.String add_depgraph, doc_depgraphGeneration;
        
        
        "-assert", Arg.String add_assert, doc_assert;
        "-nopervasives", Arg.Unit set_no_pervasives, doc_no_pervasives;
        "-target", Arg.String add_target_language, doc_target;
        "-targetpath", Arg.String set_target_path, doc_target_path;
        "-nocaus", Arg.Clear causality, doc_nocaus;
        "-noinit", Arg.Clear init, doc_noinit;
        "-fti", Arg.Set full_type_info, doc_full_type_info;
        "-statefuli", Arg.Set stateful_info, doc_stateful_info;
        "-fname", Arg.Set full_name, doc_full_name;
        "-nbvars", Arg.Set nbvars, doc_nbvars;
        "-itfusion", Arg.Set do_iterator_fusion, doc_itfusion;
        "-strict_ssa", Arg.Unit set_strict_ssa, doc_strict_ssa;
        "-nosink", Arg.Set nosink, doc_nosink;
        "-memalloc", Arg.Unit do_mem_alloc_and_typing, doc_memalloc;
        "-only-memalloc", Arg.Set do_mem_alloc, doc_memalloc_only;
        "-only-linear", Arg.Set do_linear_typing, doc_linear_only;
        "-old-scheduler", Arg.Set use_old_scheduler, doc_interf_scheduler;
        "-unroll", Arg.Set unroll_loops, doc_unroll;
        "-O", Arg.Unit do_optim, doc_optim;
        "-mall", Arg.Set interf_all, doc_interf_all;
        "-time", Arg.Set time_passes, doc_time_passes;
        "-abstract-infinite", Arg.Set abstract_infinite, doc_abstract_infinite;
        ("-Wno-untranslatable", Arg.Clear warn_untranslatable,
         doc_no_warn_untranslat);
        ("-Wno-abstract", Arg.Clear warn_abstractions,
         doc_no_warn_abstractions);
      ]
        compile errmsg;
  with
    | Errors.Error -> exit 2;;


(* Launch the [main] *)
main ()
