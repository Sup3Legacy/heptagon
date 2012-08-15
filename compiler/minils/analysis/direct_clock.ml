(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

open Clocks

(* Remove links from clocks. *)

let ck _ () c = ck_repr c, ()

let program p =
  let funs = { Mls_mapfold.defaults with
    Mls_mapfold.global_funs = {Global_mapfold.defaults with Global_mapfold.ck = ck} }
  in
  let p, _ = Mls_mapfold.program_it funs () p in
  p
