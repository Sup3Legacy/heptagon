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
open Signature
open Clocks
open Minils
open Misc

module type ClockCompare =
sig
  val clock_compare : Clocks.ck -> Clocks.ck -> int
end

module Make = functor (C : ClockCompare) ->
struct
  let rec extvalue_compare w1 w2 =
    let cr = type_compare w1.w_ty w2.w_ty in
    if cr <> 0 then cr
    else
      let cr = Linearity.linearity_compare w1.w_linearity w2.w_linearity in
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
      | Wfield (w1, f1), Wfield(w2, f2) ->
        let cr = compare f1 f2 in
        if cr <> 0 then cr else extvalue_compare w1 w2
      | Wreinit (w1, ww1), Wreinit (w2, ww2) ->
        let cr = extvalue_compare w1 w2 in
        if cr <> 0 then cr else extvalue_compare ww1 ww2
      | Wbang w1, Wbang w2 ->
          extvalue_compare w1 w2

      | Wconst _, _ -> 1

      | Wvar _, Wconst _ -> -1
      | Wvar _, _ -> 1

      | Wwhen _, (Wconst _ | Wvar _) -> -1
      | Wwhen _, _ -> 1

      | Wfield _, (Wconst _ | Wvar _ | Wwhen _) -> -1
      | Wfield _, _ -> 1

      | Wreinit _, Wbang _ -> 1
      | Wreinit _, _ -> -1

      | Wbang _, _ -> -1

  let reset_compare r1 r2 =
    list_compare extvalue_compare r1 r2

  let rec exp_compare e1 e2 =
    let cr = type_compare e1.e_ty e2.e_ty in
    if cr <> 0 then cr
    else
      let cr = Linearity.linearity_compare e1.e_linearity e2.e_linearity in
      if cr <> 0 then cr
      else
        match e1.e_desc, e2.e_desc with
        | Eextvalue w1, Eextvalue w2 ->
          extvalue_compare w1 w2
        | Efby (seo1, p1, e1, r1), Efby (seo2, p2, e2, r2) ->
          let cr = option_compare static_exp_compare seo1 seo2 in
          if cr <> 0 then cr
          else let cr = list_compare static_exp_compare p1 p2 in
          if cr <> 0 then cr
          else let cr = extvalue_compare e1 e2 in
          if cr <> 0 then cr
          else reset_compare r1 r2
        | Eapp (app1, el1, vio1), Eapp (app2, el2, vio2) ->
          let cr = app_compare app1 app2 in
          if cr <> 0 then cr
          else let cr = list_compare extvalue_compare el1 el2 in
          if cr <> 0 then cr else reset_compare vio1 vio2
        | Ewhen (e1, cn1, id1), Ewhen (e2, cn2, id2) ->
          let cr = compare cn1 cn2 in
          if cr <> 0 then cr
          else let cr = ident_compare id1 id2 in
               if cr <> 0 then cr else exp_compare e1 e2
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
        | Eiterator (it1, app1, sel1, pel1, el1, vio1),
          Eiterator (it2, app2, sel2, pel2, el2, vio2) ->
          let cr = compare it1 it2 in
          if cr <> 0 then cr else
            let cr = list_compare static_exp_compare sel1 sel2 in
            if cr <> 0 then cr else
              let cr = app_compare app1 app2 in
              if cr <> 0 then cr else
                let cr = reset_compare vio1 vio2 in
                if cr <> 0 then cr else
                  let cr = list_compare extvalue_compare pel1 pel2 in
                  if cr <> 0 then cr else list_compare extvalue_compare el1 el2

        | Eextvalue _, _ -> 1

        | Efby _, Eextvalue _ -> -1
        | Efby _, _ -> 1

        | Eapp _, (Eextvalue _ | Efby _) -> -1
        | Eapp _, _ -> 1

        | Ewhen _, (Eextvalue _ | Efby _ | Eapp _) -> -1
        | Ewhen _, _ -> 1

        | Emerge _, (Estruct _ | Eiterator _) -> 1
        | Emerge _, _ -> -1

        | Estruct _, Eiterator _ -> 1
        | Estruct _, _ -> -1

        | Eiterator _, _ -> -1

  and app_compare app1 app2 =
    let cr = Pervasives.compare app1.a_unsafe app2.a_unsafe in

    if cr <> 0 then cr
    else
      let cr = match app1.a_op, app2.a_op with
        | Efun ln1, Efun ln2 | Enode ln1, Enode ln2 -> compare ln1 ln2
        | x, y when x = y -> 0 (* all constructors can be compared with P.compare *)


        | Eequal, _ -> 1

        | Efun _, Eequal -> -1
        | Efun _, _ -> 1

        | Enode _, (Eequal | Efun _) -> -1
        | Enode _, _ -> 1

        | Eifthenelse, (Eequal | Efun _ | Enode _) -> -1
        | Eifthenelse, _ -> -1

        | Efield_update, (Eifthenelse | Eequal | Efun _ | Enode _) -> -1
        | Efield_update, _ -> 1

        | Earray, (Efield_update | Eifthenelse | Eequal | Efun _ | Enode _) -> -1
        | Earray, _ -> 1

        | Earray_fill, (Earray | Efield_update | Eifthenelse | Eequal | Efun _ | Enode _) -> -1
        | Earray_fill, _ -> 1

        | Eselect,
          (Earray_fill | Earray | Efield_update | Eifthenelse | Eequal | Efun _ | Enode _) -> -1
        | Eselect, _ -> 1

        | Eselect_slice,
          (Eselect | Earray_fill | Earray | Efield_update
              | Eifthenelse | Eequal | Efun _ | Enode _) -> -1
        | Eselect_slice, _ -> 1

        | Eselect_dyn,
          (Eselect_slice | Eselect | Earray_fill | Earray | Efield_update
              | Eifthenelse | Eequal | Efun _ | Enode _) -> -1
        | Eselect_dyn, _ -> 1

        | Eselect_trunc,
          (Eselect_dyn | Eselect_slice | Eselect | Earray_fill | Earray | Efield_update
              | Eifthenelse | Eequal | Efun _ | Enode _) -> -1
        | Eselect_trunc, _ -> 1

        | Eupdate,
          (Eselect_trunc |Eselect_dyn | Eselect_slice | Eselect | Earray_fill | Earray
              | Efield_update | Eifthenelse | Eequal | Efun _ | Enode _) -> -1
        | Eupdate, _ -> 1

        | Econcat,
          (Eupdate | Eselect_trunc |Eselect_dyn | Eselect_slice | Eselect | Earray_fill | Earray
              | Efield_update | Eifthenelse | Eequal | Efun _ | Enode _) -> -1
        | Econcat, _ -> 1

        | Ebang, _ -> -1
      in
      if cr <> 0 then cr
      else list_compare static_exp_compare app1.a_params app2.a_params

  let rec pat_compare pat1 pat2 = match pat1, pat2 with
    | Evarpat id1, Evarpat id2 -> ident_compare id1 id2
    | Etuplepat pat_list1, Etuplepat pat_list2 ->
      list_compare pat_compare pat_list1 pat_list2
    | Evarpat _, _ -> 1
    | Etuplepat _, _ -> -1

end

include Make(struct let clock_compare = clock_compare end)
