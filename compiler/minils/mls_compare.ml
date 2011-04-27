(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(* Comparison functions for MiniLustre *)

open Idents
open Minils
open Misc
open Global_compare

let rec extvalue_compare w1 w2 =
  let cr = type_compare w1.w_ty w2.w_ty in
  if cr <> 0 then cr
  else
    match w1.w_desc, w2.w_desc with
      | Wconst se1, Wconst se2 -> static_exp_compare se1 se2
      | Wvar vi1, Wvar vi2 -> ident_compare vi1 vi2
      | Wwhen (e1, cn1, vi1), Wwhen (e2, cn2, vi2) ->
          let cr = Pervasives.compare cn1 cn2 in
            if cr <> 0 then cr else
              let cr = ident_compare vi1 vi2 in
                if cr <> 0 then cr else extvalue_compare e1 e2
      | Wfield (r1, f1), Wfield(r2, f2) ->
            let cr = compare f1 f2 in
            if cr <> 0 then cr else extvalue_compare w1 w2

      | Wconst _, _ -> 1

      | Wvar _, Wconst _ -> -1
      | Wvar _, _ -> 1

      | Wwhen _, (Wconst _ | Wvar _) -> -1
      | Wwhen _, _ -> 1

      | Wfield _, _ -> -1

let rec exp_compare e1 e2 =
  let cr = type_compare e1.e_ty e2.e_ty in
  if cr <> 0 then cr
  else
    let cr = clock_compare e1.e_ck e2.e_ck in
    if cr <> 0 then cr
    else
      match e1.e_desc, e2.e_desc with
        | Eextvalue w1, Eextvalue w2 ->
            extvalue_compare w1 w2
        | Efby (seo1, e1), Efby (seo2, e2) ->
            let cr = option_compare static_exp_compare seo1 seo2 in
            if cr <> 0 then cr else extvalue_compare e1 e2
        | Eapp (app1, el1, vio1), Eapp (app2, el2, vio2) ->
            let cr = app_compare app1 app2 in
            if cr <> 0 then cr
            else let cr = list_compare extvalue_compare el1 el2 in
            if cr <> 0 then cr else option_compare ident_compare vio1 vio2
        | Emerge (vi1, cnel1), Emerge (vi2, cnel2) ->
            let compare_cne (cn1, e1) (cn2, e2) =
              let cr = compare cn1 cn2 in
              if cr <> 0 then cr else extvalue_compare e1 e2 in
            let cr = ident_compare vi1 vi2 in
            if cr <> 0 then cr else list_compare compare_cne cnel1 cnel2
        | Estruct fnel1, Estruct fnel2 ->
            let compare_fne (fn1, e1) (fn2, e2) =
              let cr = compare fn1 fn2 in
              if cr <> 0 then cr else extvalue_compare e1 e2 in
            list_compare compare_fne fnel1 fnel2
        | Eiterator (it1, app1, se1, pel1, el1, vio1),
          Eiterator (it2, app2, se2, pel2, el2, vio2) ->
            let cr = compare it1 it2 in
            if cr <> 0 then cr else
              let cr = static_exp_compare se1 se2 in
              if cr <> 0 then cr else
                let cr = app_compare app1 app2 in
                if cr <> 0 then cr else
                  let cr = option_compare ident_compare vio1 vio2 in
                    if cr <> 0 then cr else
                      let cr = list_compare extvalue_compare pel1 pel2 in
                        if cr <> 0 then cr else list_compare extvalue_compare el1 el2

        | Eextvalue _, _ -> 1

        | Efby _, Eextvalue _ -> -1
        | Efby _, _ -> 1

        | Eapp _, (Eextvalue _ | Efby _) -> -1
        | Eapp _, _ -> 1

        | Emerge _, (Estruct _ | Eiterator _) -> 1
        | Emerge _, _ -> -1

        | Estruct _, Eiterator _ -> 1
        | Estruct _, _ -> -1

        | Eiterator _, _ -> -1

and app_compare app1 app2 =
  let cr = Pervasives.compare app1.a_unsafe app2.a_unsafe in

  if cr <> 0 then cr else let cr = match app1.a_op, app2.a_op with
    | Efun ln1, Efun ln2 -> compare ln1 ln2
    | x, y when x = y -> 0 (* all constructors can be compared with P.compare *)
    | (Eequal | Etuple | Efun _ | Enode _ | Eifthenelse
      | Efield_update), _ -> -1
    | (Earray | Earray_fill | Eselect | Eselect_slice | Eselect_dyn
      | Eselect_trunc | Eupdate | Econcat | Ebang), _ -> 1 in

  if cr <> 0 then cr
  else list_compare static_exp_compare app1.a_params app2.a_params

let rec pat_compare pat1 pat2 = match pat1, pat2 with
  | Evarpat id1, Evarpat id2 -> ident_compare id1 id2
  | Etuplepat pat_list1, Etuplepat pat_list2 ->
      list_compare pat_compare pat_list1 pat_list2
  | Evarpat _, _ -> 1
  | Etuplepat _, _ -> -1
