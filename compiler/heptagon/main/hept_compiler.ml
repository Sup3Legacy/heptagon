(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

open Compiler_options
open Compiler_utils
open Location
open Global_printer

let pp p = if !verbose then Hept_printer.print stdout p

let compile_program p =
  (* Typing *)
  let p = silent_pass "Statefulness check" true Stateful.program p in
  let p = pass "Typing" true Typing.program p pp in

  (* Causality check *)
  let p = silent_pass "Causality check" !causality Causality.program p in

  (* Initialization check *)
  let p = silent_pass "Initialization check" !init Initialization.program p in

  (* Completion of partial definitions *)
  let p = pass "Completion" true Completion.program p pp in

  (* Inlining *)
  let p =
    let call_inline_pass = (List.length !inline > 0) || !flatten in
    pass "Inlining" call_inline_pass Inline.program p pp in

  (* Automata *)
  let p = pass "Automata" true Automata.program p pp in

  (* Present *)
  let p = pass "Present" true Present.program p pp in

  (* Shared variables (last) *)
  let p = pass "Last" true Last.program p pp in

  (* Reset *)
  let p = pass "Reset" true Reset.program p pp in

  (* Remove switch statements *)
  let p = pass "switch" true Switch.program p pp in

  (* Every *)
  let p = pass "Every" true Every.program p pp in

  (* Iterator fusion *)
  let p = pass "Iterator fusion" !do_iterator_fusion Itfusion.program  p pp in

  (* Normalization *)
  let p = pass "Normalization" true Normalize.program p pp in

  (* Block flatten *)
  let p = pass "Block" true Block.program p pp in

  (* Return the transformed AST *)
  p


