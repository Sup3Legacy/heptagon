
(* Slicing nominal: If a fby has a constant in its right part, then do the following transformation:
    Var = ... fby Const ===> Var = Const *)

(* Author: Guillaume I *)


open Heptagon
open Hept_mapfold


let is_const_exp e1 = match e1.e_desc with
  | Econst _ -> true
  | _ -> false


let edesc_slice funs acc edesc = match edesc with
  | Epre (_, e1) | Efby (_,e1) -> begin
    if (is_const_exp e1) then
      e1.e_desc, acc
    else
      Hept_mapfold.edesc funs acc edesc
  end
  | _ -> Hept_mapfold.edesc funs acc edesc


let node_slice nd =
  let funs_slice = { Hept_mapfold.defaults with edesc = edesc_slice } in
  let n_nd, _ = funs_slice.node_dec funs_slice [] nd in
  n_nd

(* ==================================================== *)
(* if true then e1 else e2 => e1 *)
(* if false then e1 else e2 => e2 *)

let edesc_ifte funs acc edesc = match edesc with
  | Eapp (ap, le1, _) ->
    if (not (ap.a_op=Eifthenelse)) then Hept_mapfold.edesc funs acc edesc else
    let eCond = List.hd le1 in
    begin
      match eCond.e_desc with
      | Econst se ->
        (* se is a static expression which is a boolean *)
        (match se.se_desc with
        | Sbool b -> (
          (* We act here! *)
          if (b) then
            let eThen = List.hd (List.tl le1) in
            let eThen, acc = Hept_mapfold.exp funs acc eThen in
            eThen.e_desc, acc
          else
            let eElse = List.hd (List.tl (List.tl le1)) in
            let eElse, acc = Hept_mapfold.exp funs acc eElse in
            eElse.e_desc, acc
          )
        | _ -> Hept_mapfold.edesc funs acc edesc
        )
      | _ -> Hept_mapfold.edesc funs acc edesc
    end
  | _ -> Hept_mapfold.edesc funs acc edesc


let node_ifte nd =
  let funs_ifte = { Hept_mapfold.defaults with edesc = edesc_ifte } in
  let n_nd, _ = funs_ifte.node_dec funs_ifte [] nd in
  n_nd


(* ==================================================== *)

let program p =
  let nlpdesc = List.fold_left
  (fun acc pdesc -> match pdesc with
    | Pnode nd ->
      let nd = node_slice nd in
      let nd = RemoveUnusedLocVar.closure_const_var_propagation nd in
      let nd = node_ifte nd in
      (Pnode nd)::acc
    | _ -> pdesc::acc
  ) [] p.p_desc in
  {p with p_desc = nlpdesc}