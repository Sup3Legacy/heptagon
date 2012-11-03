open Heptagon


(* Transform [f (...) every e]
   into [f (...) every r] and add an equation [r=e] *)
(* Transform [ ... fby ... every e]
   into [... fby ... every r] and add an equation [r=e] *)

let rec transform (v,eq) re = match re with
| [] -> [], (v,eq)
| r::re ->
    let r, vr, eqr = Reset.reset_var_from_exp r in
    let re, acc = transform (vr@v, eqr@eq) re in
    r::re, acc

let block funs acc b =
  let b, (v, acc_eq_list) = Hept_mapfold.block funs ([], []) b in
    { b with b_local = v @ b.b_local; b_equs = acc_eq_list@b.b_equs }, acc

let edesc funs acc ed =
  let ed, acc = Hept_mapfold.edesc funs acc ed in
  match ed with
  | Efby (i,p,e,re) ->
      let re, acc = transform acc re in
      Efby (i,p,e,re), acc
  | Eapp (op, e_list, re) ->
      let re, acc = transform acc re in
      Eapp(op, e_list, re), acc
  | Eiterator(it, op, n, pe_list, e_list, re) ->
      let re, acc = transform acc re in
      Eiterator(it, op, n, pe_list, e_list, re), acc
  | _ -> ed, acc

let program p =
  let funs = { Hept_mapfold.defaults
               with Hept_mapfold.edesc = edesc; Hept_mapfold.block = block } in
  let p, _ = Hept_mapfold.program_it funs ([],[]) p in
    p
