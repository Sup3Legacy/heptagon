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

let pp p = if !verbose then Obc_printer.print stdout p

let compile_program p =
  (* Correct the memories of the kernels *)
  let p = pass "Correct kernels" true Correct_kernels.program p pp in

  (*Control optimization*)
  let p = pass "Control optimization" true Control.program p pp in
  p
