(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

open Compiler_utils
open Compiler_options
open Obc
open Minils
open Misc

(** Definition of a target. A target starts either from
    dataflow code (ie Minils) or sequential code (ie Obc),
    with or without static parameters *)
type target =
  | Obc of (Obc.program -> unit)
  | Obc_no_params of (Obc.program -> unit)
  | Minils of (Minils.program -> unit)
  | Minils_no_params of (Minils.program -> unit)

(** Writes a .epo file for program [p]. *)
let write_object_file p =
  let filename = (Names.modul_to_string p.Minils.p_modname)^".epo" in
  let epoc = open_out_bin filename in
    output_value epoc p;
    close_out epoc;
    comment "Generating of object file"

(** Writes a .obc file for program [p]. *)
let write_obc_file p =
  let obc_name = (Names.modul_to_string p.Obc.p_modname)^".obc" in
  let obc = open_out obc_name in
    Obc_printer.print obc p;
    close_out obc;
    comment "Generation of Obc code"

let no_conf () = ()
let targets = [ "c",(Obc_no_params Cmain.program, no_conf);
               "java", (Obc Java_main.program, no_conf);
                "obc", (Obc write_obc_file, no_conf);
                "obc_np", (Obc_no_params write_obc_file, no_conf);
                "epo", (Minils write_object_file, no_conf) ]

let generate_target p s =
(*  let print_unfolded p_list =
    comment "Unfolding";
    if !Compiler_options.verbose
    then List.iter (Mls_printer.print stderr) p_list in*)
  let target =
    (try fst (List.assoc s targets)
     with Not_found -> language_error s; raise Errors.Error) in
  match target with
    | Minils convert_fun ->
        convert_fun p
    | Obc convert_fun ->
        let o = Mls2obc.program p in
        let o = Obc_compiler.compile_program o in
          convert_fun o
    | Minils_no_params convert_fun ->
        let p_list = Callgraph.program p in
          List.iter convert_fun p_list
    | Obc_no_params convert_fun ->
        let p_list = Callgraph.program p in
        let o_list = List.map Mls2obc.program p_list in
        let o_list = List.map Obc_compiler.compile_program o_list in
        List.iter convert_fun o_list

let load_conf () =
  let target_conf s =
    try
      let conf = snd (List.assoc s targets) in
        conf ()
    with
        Not_found -> language_error s; raise Errors.Error
  in
    List.iter target_conf !target_languages

(** Translation into dataflow and sequential languages, defaults to obc. *)
let program p =
  let targets = match !target_languages with
    | [] -> ["obc"] (* by default, generate obc file *)
    | l -> l in
  let targets = if !create_object_file then "epo"::targets else targets in
  List.iter (generate_target p) targets
