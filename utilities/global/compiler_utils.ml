(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
open Misc
open Location

let lexical_error err loc =
  Printf.eprintf "%aIllegal character.\n" output_location loc;
  raise Error

let syntax_error loc =
  Printf.eprintf "%aSyntax error.\n" output_location loc;
  raise Error

let language_error lang =
  Printf.eprintf "Unknown language: %s.\n" lang

let parse parsing_fun lexing_fun lexbuf =
  try
    parsing_fun lexing_fun lexbuf
  with
    | Lexer.Lexical_error(err, pos1, pos2) ->
        lexical_error err (Loc(pos1, pos2))
    | Parsing.Parse_error ->
        let pos1 = Lexing.lexeme_start lexbuf
        and pos2 = Lexing.lexeme_end lexbuf in
        let l = Loc(pos1,pos2) in
        syntax_error l

let comment s = Printf.printf "** %s done **\n" s; flush stdout

let do_pass f d p pp enabled =
  if enabled
  then
    let r = f p in
    if !verbose
    then begin
      comment d;
      pp r;
    end;
    r
  else p

let do_silent_pass f d p enabled =
  if enabled
  then begin
    let r = f p in
    if !verbose then comment d; r
  end
  else p

let build_path suf =
  match !target_path with
    | None -> suf
    | Some path -> Filename.concat path suf

let clean_dir dir =
  if Sys.file_exists dir && Sys.is_directory dir
  then begin
    let rm_file_in_dir fn = Sys.remove (Filename.concat dir fn) in
    Array.iter rm_file_in_dir (Sys.readdir dir);
  end else Unix.mkdir dir 0o740;
  dir

let init_compiler modname source_name ic =
    Location.initialize source_name ic;
    Modules.initialize modname;
    Initial.initialize ()

let doc_verbose = "\t\t\tSet verbose mode"
and doc_version = "\t\tThe version of the compiler"
and doc_print_types = "\t\t\tPrint types"
and doc_include = "<dir>\t\tAdd <dir> to the list of include directories"
and doc_stdlib = "<dir>\t\tDirectory for the standard library"
and doc_sim = "<node>\t\tCreate simulation for node <node>"
and doc_locate_stdlib = "\t\tLocate standard libray"
and doc_no_pervasives = "\tDo not load the pervasives module"
and doc_target =
  "<lang>\tGenerate code in language <lang>\n\t\t\t(with <lang>=c,"
  ^ " vhdl_seq, vhdl_df,\n\t\t\t java or z3z)"
and doc_full_type_info = "\t\t\tPrint full type information"
and doc_target_path =
  "<path>\tGenerated files will be placed in <path>\n\t\t\t(the directory is cleaned)"
and doc_noinit = "\t\tDisable initialization analysis"

let errmsg = "Options are:"

