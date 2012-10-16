(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(** This module simplify static expression of the program and deal with :
    (0^n)[3] ==> 0
    [3,4,5][2] ==> 5
 *)



open Signature
open Static
open Obc
open Obc_mapfold

let extvaluedesc funs () evd = match evd with
  | Warray (ev,e) ->
      let ev, () = extvalue_it funs () ev in
      (match ev.w_desc with
        | Wconst se ->
          (match se.se_desc with
            | Sarray_power (sv, [_]) ->
              Wconst sv, ()
            | Sarray_power (sv, _::idx) ->
              Wconst { se with se_desc = Sarray_power (sv, idx)}, ()
            | Sarray sv_l ->
              (match e.e_desc with
                | Eextvalue { w_desc = Wconst i } ->
                  (try
                     let indice = int_of_static_exp i in
                     Wconst (Misc.nth_of_list (Int32.to_int indice + 1) sv_l), ()
                   with _ -> raise Errors.Fallback)
                | _ -> raise Errors.Fallback
              )
            | _ -> raise Errors.Fallback
          )
        | _ -> raise Errors.Fallback
      )
  | _ -> raise Errors.Fallback

let static_exp _ () se = Static.simplify se, ()

let program p =
  let gfuns = {Global_mapfold.defaults with
                 Global_mapfold.static_exp = static_exp}
  in
  let funs = { defaults with evdesc      = extvaluedesc;
                             global_funs = gfuns}
  in
  let p, _ = program_it funs () p in
  p

