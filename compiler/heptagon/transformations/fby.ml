(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)


open Heptagon
open Hept_utils

(* e1 fby e2 are translated to e1 -> pre e2 when needed, ie e1 not static*)


let exp funs () e = 
  let e,_ = Hept_mapfold.exp funs () e in
  match e.e_desc with
    | Efby (e1, p, e2, c) ->
        (match e1 with
        | None | Some {e_desc = Econst _} -> e,()
        | Some e1 ->
            let e_noinit = {e with e_desc = Efby(None,p,e2,c)} in
            let arrow = mk_op_app ~reset:c Earrow [e1;e_noinit] in
            {e with e_desc = arrow},()
        )
    | _ -> e,()

let funs = { Hept_mapfold.defaults with Hept_mapfold.exp = exp }

let program p =
  let p, _ = Hept_mapfold.program_it funs () p in
  p
