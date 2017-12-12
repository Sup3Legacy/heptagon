
open Signature
open Heptagon
open Hept_utils

(* Remove all occurence of "buffer" in the program *)
(* Require the type of the subexpression of "buffer", in order to build the intermediate variable *)
(* Author : Guillaume I *)

(* buffer(c1, id1, c2, id2, eInit, e) = current(c1, id1, eInit, e) when c2(id2) *)
let edesc funs acc ed = match ed with
  | Ebuffer (c1, id1, c2, id2, eInit, e) ->
    let edesc_curr = Ecurrent(c1, id1, eInit, e) in
    let expr_curr =  mk_exp edesc_curr e.e_ty ~linearity:Linearity.Ltop in
    Ewhen(expr_curr, c2, id2), acc
  | _ -> Hept_mapfold.edesc funs acc ed (* Default recursion case *)


(* Main function *)
let program p =
  let funs = { Hept_mapfold.defaults with edesc = edesc} in
  let (p, _) = Hept_mapfold.program funs [] p in
  p


