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

open Compiler_options
open Compiler_utils

let pp p = if !verbose then Hept_printer.print stdout p

let compile_program p =
  (* Remove the "current" construct (syntactic sugar) *)
  let p = silent_pass "Current removal" true CurrentRemoval.program p in
  
  (* Typing *)
  let p = silent_pass "Statefulness check" true Stateful.program p in
  let p = silent_pass "Unsafe check" true Unsafe.program p in
  let p = pass "Typing" true Typing.program p pp in
  let p = pass "Linear Typing" !do_linear_typing Linear_typing.program p pp in
  
  (* Inlining *)
  let p = pass "Inlining" true Inline.program p pp in
  
  (* Pruning of the uncalled node *)
  let p = pass "Pruning" !prune Pruning.program p pp in
  
  (* Contracts handling *)
  let p = pass "Contracts" true Contracts.program p pp in

  (* Causality check *)
  let p = silent_pass "Causality check" !causality Causality.program p in

  (* Initialization check *)
  let p = silent_pass "Initialization check" !init Initialization.program p in

  (* Completion of partial definitions *)
  let p = pass "Completion" true Completion.program p pp in

  (* Shared variables (remove last) *)
  let p = pass "Last" true Last.program p pp in

  (* Automata *)
  let p = pass "Automata" true Automata.program p pp in

  (* Present *)
  let p = pass "Present" true Present.program p pp in

  (* Reset *)
  let p = pass "Reset" true Reset.program p pp in

  (* Remove switch statements *)
  let p = pass "Switch" true Switch.program p pp in

  (* Every *)
  let p = pass "Every" true Every.program p pp in

  (* Iterator fusion *)
  let p = pass "Iterator fusion" !do_iterator_fusion Itfusion.program  p pp in

  (* Normalization *)
  let p = pass "Normalization" true Normalize.program p pp in
  
  (* Boolean pass *)
  let p = pass "Clocking(Heptagon)" !boolean Hept_clocking.program p pp in
  let p = pass "Boolean" !boolean Boolean.program p pp in
  let p = pass "Normalization" !boolean Normalize.program p pp in

  (* Block flatten *)
  let p = pass "Block" true Block.program p pp in
  

  (* Temp pass - make a real compiler option for that *)
  let p = pass "Inline all constant" true InlineConstant.program p pp in
  
  
  (* For script adaptation with Lopht ===> Should be disabled afterward *)
  (* let p = silent_pass "Variable renaming" true Varname_change.program p in *)


  let p = silent_pass "Elimination of pre" !preElimination EliminationPre.program p in

  (* Copy equation ("VarLoc1 = VarLoc2") removal *)
  let p = pass "Copy equation removal" !copyRemoval CopyRemoval.program p pp in
  


  (* TODO: DEBUG (in order to merge the as and the ecas *)
  if (true) then
    let oc = open_out "all_ept_pre_merging.mls" in
    Hept_printer.print oc p
  else ();
  (* *)

  (* Array destruction + copy equation afterward to clean up *)
  let p = pass "Array destruction" !arrayDestruct ArrayDestruct.program p pp in
  let p = pass "Copy equation removal - post array destruction" !arrayDestruct CopyRemoval.program p pp in
  let p = silent_pass "Slicing nominal" !slicing_nominal Slicing.program p in
  let p = pass "Copy equation removal - post slicing" !slicing_nominal CopyRemoval.program p pp in

  (* TODO: DEBUG (in order to merge the as and the ecas *)
  if (true) then
    let oc = open_out "all_ept_post_arrdestr.mls" in
    Hept_printer.print oc p
  else ();
  (* *)

  (* let p = pass "Dependence graph generation" ((!depgraphGeneration)!=[]) DepGraphGeneration.program p pp in *)

  (* Dirty hyperperiod expansion output for the Safran usecase *)
  let p = silent_pass "Dirty Hyperperiod expansion" !hyperperiod Dirty_hyperperiod_expansion_Safran.program p in

  let p = silent_pass "Remove unused locvar" !removeUnusedLocVar RemoveUnusedLocVar.program p in
  let p = silent_pass "Copy equation removal" !copyEqRemoval CopyRemoval.program p in
  

  let p = pass "Equation clustering" !safran_clustering EquationClustering.program p pp in
  
  (* TODO DEBUG: still causal at that point *)

  
  (* TODO DEBUG Causality check *)
  let p = silent_pass "Causality check" !causality Causality.program p in
  Format.fprintf (Format.formatter_of_out_channel stdout) "CAUSALITY PASSED\n@?";
  

  (* Note: should not be activated outside of debugging *)
  if (!safran_clustering) then
    let oc = open_out "all_mls_clustered.mls" in
    Hept_printer.print oc p
  else ();

  (* Return the transformed AST *)
  p


let compile_interface i =
  let i = silent_pass "Typing" true Typing.interface i in
  i
