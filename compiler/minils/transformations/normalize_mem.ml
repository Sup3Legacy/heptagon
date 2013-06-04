open Minils
open Mls_mapfold
open Mls_utils

(** REQUIRE no inner blocks *)
(**
  o = v fby e every r
  becomes
  mem_o = v fby e every r;
  o = v fbyread mem_o every r
*)

let rec replace_fby e x_mem = match e.e_desc with
  | Ewhen (e1, c, y) ->
      { e with e_desc = Ewhen ((replace_fby e1 x_mem), c, y) }
  | Efby (None, _, _, _) -> (* no need to reset *)
      let d = Efbyread (x_mem, None, []) in
      { e with e_desc = d }
  | Efby (Some v, _, _, re) ->
      let d = Efbyread (x_mem, Some v, re) in
      { e with e_desc = d }
  | _ -> assert false

let eq _ (vds, v, eqs) eq = match ((eq.eq_lhs), (eq.eq_rhs)) with
  | (Evarpat x, e) when Vars.is_fby e ->
      let vd = vd_find x vds in
      let x_mem = Idents.gen_var "normalize_mem" ("mem_" ^ (Idents.name x)) in
      (* mem_o = v fby e every r AND remove "when" stuffs *)
      let fby_exp = Vars.get_fby eq.eq_rhs in
      let fby_ck = Clocks.first_ck fby_exp.e_ct in
      let vd_mem = { vd with v_ident = x_mem;
                             v_is_memory = true;
                             v_clock = fby_ck;}
      in
      let eq_copy = { eq with eq_lhs = Evarpat x_mem;
                              eq_rhs = fby_exp;
                              eq_base_ck = fby_ck;}
      in
      (* o = v fbyread mem_o every r AND keep "when" stuffs *)
      let eq = { eq with eq_rhs = replace_fby e x_mem; }
      in (eq, (vds, (vd_mem :: v), (eq :: eq_copy :: eqs)))
  | (_, _) -> (eq, (vds, v, (eq :: eqs)))

let contract funs acc ct =
  let ct, (_, v, eqs) =
    Mls_mapfold.contract_it funs (ct.c_local, [], []) ct
  in
  let ct = { ct with c_local = v @ ct.c_local; c_eq = List.rev eqs } in
  ct, acc

let node_dec funs acc nd =
  let nd, (_, v, eqs) =
    Mls_mapfold.node_dec funs (nd.n_local @ nd.n_output, [], []) nd
  in
  let nd = { nd with n_local = v @ nd.n_local; n_equs = List.rev eqs } in
  let nd = Is_memory.update_node nd in
  nd, acc

let program p =
  let funs =
    { Mls_mapfold.defaults with
      eq = eq;
      node_dec = node_dec;
      contract = contract; }
  in
  let p, _ = Mls_mapfold.program_it funs ([], [], []) p in
  p
