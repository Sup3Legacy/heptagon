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

let pp p = if !verbose then Mls_printer.print stdout p

let compile pp p =
  vhdl_simpl := !vhdl_simpl or (List.mem "vhdl" !target_languages);

  (* Clocking *)
  let p = do_pass Clocking.program "Clocking" p pp true in

  (* Check that the dataflow code is well initialized *)
  (*let p = do_silent_pass Init.program "Initialization check" p !init in *)

  (* Iterator fusion *)
  let p = do_pass Itfusion.program "Iterator fusion" p pp true in

  let p =
    do_pass Mls2vhdl.AddRst.program "Reset elimination" p pp !vhdl_simpl in

  (* Normalization to maximize opportunities *)
  let p = do_pass Normalize.program "Normalization" p pp true in

  let p =
    do_pass Mls2vhdl.SimpCalls.program "Call simplification" p pp !vhdl_simpl in

  (* Scheduling *)
  let p = do_pass Schedule.program "Scheduling" p pp true in

  p
