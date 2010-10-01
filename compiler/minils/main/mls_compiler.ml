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
open Compiler_utils
open Compiler_options

let pp p = if !verbose then Mls_printer.print stdout p
(*
let parse parsing_fun lexing_fun lexbuf =
  try
    parsing_fun lexing_fun lexbuf
  with
    | Mls_lexer.Lexical_error(err, loc) ->
        lexical_error err loc
    | Mls_parser.Error ->
        let pos1 = Lexing.lexeme_start_p lexbuf
        and pos2 = Lexing.lexeme_end_p lexbuf in
        let l = Loc(pos1,pos2) in
        syntax_error l

let parse_implementation prog_name lexbuf =
  let p = parse Mls_parser.program Mls_lexer.token lexbuf in
  { p with Mls_parsetree.p_modname = prog_name }
*)
let compile pp p =
  vhdl_simpl := !vhdl_simpl or (List.mem "vhdl" !target_languages);

  (* Clocking *)
  let p = pass "Clocking" true Clocking.program p pp in

  (* Check that the dataflow code is well initialized *)
  (*let p = silent_pass "Initialization check" !init Init.program p in *)

  (* Iterator fusion *)
  let p = pass "Iterator fusion" !do_iterator_fusion Itfusion.program  p pp in

  (* Automata minimization *)
  let p =
    let call_tomato = !tomato or (List.length !tomato_nodes > 0) in
    pass "Automata minimization" call_tomato Tomato.program p pp in

  let p =
    pass "Automata minimization checks" true Tomato.tomato_checks p pp in

  let p =
    pass "Reset elimination" !vhdl_simpl Mls2vhdl.AddRst.program p pp in

  (* Normalization to maximize opportunities *)
  let p = pass "Normalization" true Normalize.program p pp in

  let p =
    pass "Call simplification" !vhdl_simpl Mls2vhdl.SimpCalls.program p pp in

  (* Scheduling *)
  let p = pass "Scheduling" true Schedule.program p pp in

  p
