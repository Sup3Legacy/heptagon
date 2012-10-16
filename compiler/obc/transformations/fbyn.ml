
open Linearity
open Signature
open Initial
open Heptagon
open Hept_utils

(* Translate fby<<n>> into an array and index *)


(*
y = 42 fby<<n>> x every r
==>
y = y_d[>y_i<]
y_u = [y_d with [y_i] = x]
y_d = 42^n fby y_u every r
y_i = 0 fby y_m
y_n = y_i + 1
y_b = y_n >= n
y_m = if y_b then 0 else y_n
*)


let fresh var prefix =
  Idents.gen_var "fbyn" ~reset:true (var^"_"^prefix)

let new_var loc from_var prefix t =
  let y = fresh from_var prefix in
  let vd = mk_var_dec ~loc:loc y t Ltop in
  let e = mk_var_exp y t in
  let pat = Evarpat y in
  vd, e, pat

(** Try to set correct variable name *)
let eqdesc funs (_, vd_acc, eq_acc) ed =
  let rec get_string pat = match pat with
    | Evarpat y -> Idents.name y
    | Etuplepat [] -> "reg"
    | Etuplepat y_l -> get_string (List.hd y_l)
  in
  let y = match ed with
    | Eeq(pat, _) -> get_string pat
    | _ -> "reg"
  in
  Hept_mapfold.eqdesc funs (y, vd_acc, eq_acc) ed


(** changing registers with one parameter,
    adding var decs and equations,
    using [y] and [loc] *)
let exp funs (y, vd_acc, eq_acc) e = match e.e_desc with
  | Efby (sv, [n], x, r) ->
      let loc = e.e_loc in
      let t = Tarray (x.e_ty, n) in
      let sv = match sv with
      | None -> None
      | Some ({e_desc = Econst v} as ev) ->
          let v = {v with se_desc = Sarray_power (v,[n])} in
          let ev = {ev with e_ty = t; e_desc = Econst v} in
          Some ev
      | _ -> Misc.internal_error "Pass fbyn shoudl come after \
                                  pass fby (normalize into true fby)"
      in
      let (vd_u, e_u, pat_u) = new_var loc y "u" t
      and vd_d, e_d, pat_d = new_var loc y "d" t
      and vd_i, e_i, pat_i = new_var loc y "i" (Tbounded n)
      and vd_n, e_n, pat_n = new_var loc y "n" tint
      and vd_b, e_b, pat_b = new_var loc y "b" tbool
      and vd_m, e_m, pat_m = new_var loc y "m" tint
      in
      (* y_u = [y_d with [y_i] = x] *)
      let e_y_u = mk_exp (mk_op_app Eupdate [e_d;x;e_i]) ~loc:loc t Ltop in
      let eq_y_u = mk_equation ~loc:loc (Eeq (pat_u,e_y_u)) in
      (* y_d = 42^n fby y_u every r *)
      let e_y_d = mk_exp (Efby (sv, [], e_u, r)) ~loc:loc t Ltop in
      let eq_y_d = mk_equation ~loc:loc (Eeq (pat_d, e_y_d)) in
      (* y_i = 0 fby y_m *)
      let e_y_i =
        mk_exp (Efby (Some (mk_exp_int 0), [], e_m, [])) ~loc:loc tint Ltop in
      let eq_y_i = mk_equation ~loc:loc (Eeq (pat_i, e_y_i)) in
      (* y_n = y_i + 1 *)
      let e_y_n =
        mk_exp (mk_op_app (Efun(mk_pervasives "+"))
               [e_i; mk_exp_int 1])
               ~loc:loc tint Ltop
      in
      let eq_y_n = mk_equation ~loc:loc (Eeq (pat_n, e_y_n)) in
      (* y_b = y_n >= n *)
      let e_y_b =
        mk_exp (mk_op_app (Efun(mk_pervasives ">="))
               [e_n; mk_static_exp_exp tint n.se_desc])
               ~loc:loc tint Ltop
      in
      let eq_y_b = mk_equation ~loc:loc (Eeq (pat_b, e_y_b)) in
      (* y_m = if y_b then 0 else y_n *)
      let e_y_m = mk_ifthenelse e_b (mk_exp_int 0) e_n in
      let eq_y_m = mk_equation ~loc:loc (Eeq (pat_m, e_y_m)) in
      (* y = y_d[>y_i<] *)
      let e_y = {e with e_desc = mk_op_app Eselect_trunc [e_d;e_i]} in
      let vd_acc = vd_u::vd_d::vd_i::vd_n::vd_b::vd_m::vd_acc in
      let eq_acc = eq_y_u::eq_y_d::eq_y_i::eq_y_n::eq_y_b::eq_y_m::eq_acc in
      Hept_mapfold.exp_it funs (y, vd_acc, eq_acc) e_y
  | Efby (_, _::_::_, _, _) ->
      Misc.unsupported "Too many arguments to fby"
  | _ ->
      Hept_mapfold.exp funs (y, vd_acc, eq_acc) e


(** Collecting equations and var dec *)
let block funs (y, vd_acc, eq_acc) b =
  let b, (y, vd_acc', eq_acc') = Hept_mapfold.block funs (y,[],[]) b in
  let b = { b with b_local = vd_acc'@b.b_local;
                   b_equs   = eq_acc'@b.b_equs; }
  in
  b, (y, vd_acc, eq_acc)


let funs = { Hept_mapfold.defaults with Hept_mapfold.block = block;
                                        Hept_mapfold.exp = exp;
                                        Hept_mapfold.eqdesc = eqdesc; }

let program p =
  let p, _ = Hept_mapfold.program_it funs ("",[],[]) p in
  p




