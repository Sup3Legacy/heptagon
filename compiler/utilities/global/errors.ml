(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(* error during the whole process *)
exception Error

let errorf f p =
	Format.eprintf (" Error : "^^f^^"@.") p;
	raise Error

let warningf f p =
	Format.eprintf (" Warning : "^^f^^"@.") p;


(** Ast iterators *)
exception Fallback
