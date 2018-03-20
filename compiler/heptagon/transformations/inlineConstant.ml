
(* Inline all the constant of a program and remove all constant definition *)
(* Author: Guillaume *)

open Types
open Global_mapfold
open Heptagon
open Hept_mapfold


(* Type of htbl_cstdef : const_qualname -> const_dec *)

let sedesc_const_node htbl_cstdef funs acc sedesc = match sedesc with
  | Svar cname -> begin
    let cdecopt = (try
        Some (Hashtbl.find htbl_cstdef cname)
      with Not_found -> None)
    in
    match cdecopt with
      | None ->
        (Svar cname), acc
      | Some cd ->
        cd.c_value.se_desc, acc
    end
  | _ -> Global_mapfold.static_exp_desc funs acc sedesc

let inline_const_node htbl_cstdef nd =
  let glfuns_const_node = { Global_mapfold.defaults with static_exp_desc = (sedesc_const_node htbl_cstdef) } in
  let funs_const_node = { Hept_mapfold.defaults with global_funs = glfuns_const_node } in
  let n_nd, _ = funs_const_node.node_dec funs_const_node [] nd in
  n_nd


(* ======================================================= *)

let program p =
  let htbl_cstdef = List.fold_left
    (fun acc pdesc -> match pdesc with
      | Pconst cd ->
        Hashtbl.add acc cd.c_name cd;
        acc
      | _ -> acc
    ) (Hashtbl.create (List.length p.p_desc)) p.p_desc in

  let nlpdesc = List.map
    (fun pdesc -> match pdesc with
      | Pnode n -> Pnode (inline_const_node htbl_cstdef n)
      | _ -> pdesc
    ) p.p_desc in

  (* Flush all constants declaration *)
  let nlpdesc = List.filter
    (fun pdesc -> match pdesc with
      | Pconst _ -> false
      | _ -> true
    ) nlpdesc in
	{ p with p_desc = nlpdesc }
