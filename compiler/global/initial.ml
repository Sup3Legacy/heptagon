(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* initialization of the typing environment *)

open Names
open Location
open Signature

let tglobal = []
let cglobal = []

let pbool = { qual = Pervasives; name = "bool" }
let tbool = Tid pbool
let por = { qual = Pervasives; name = "or" }
let pint = { qual = Pervasives; name = "int" }
let tint = Tid pint
let pfloat = { qual = Pervasives; name = "float" }
let tfloat = Tid pfloat
let pstring = { qual = Pervasives; name = "string" }
let tstring = Tid pstring

let pfile = { qual = Module "Iostream"; name = "file" }
let tfile = Tid pfile

let mk_pervasives s = { qual = Pervasives; name = s }

let mk_static_int_op ?(loc = no_location) op args =
  mk_static_exp ~loc:loc tint (Sop (mk_pervasives op, args))

let mk_static_int ?(loc = no_location) i =
  mk_static_exp ~loc:loc tint (Sint (Int32.of_int i))

let mk_static_int32 ?(loc = no_location) i =
  mk_static_exp ~loc:loc tint (Sint i)

let mk_static_bool ?(loc = no_location) b =
  mk_static_exp ~loc:loc tbool (Sbool b)

let mk_static_string ?(loc = no_location) s =
  mk_static_exp ~loc:loc tstring (Sstring s)

let mk_static_float ?(loc = no_location) f =
  mk_static_exp ~loc:loc tfloat (Sfloat f)


let strue = mk_static_bool true
let sfalse = mk_static_bool false



(* build the initial environment *)
let initialize modul =
  Modules.initialize modul;
  List.iter (fun (f, ty) -> Modules.add_type f ty) tglobal;
  List.iter (fun (f, ty) -> Modules.add_constrs f ty) cglobal
