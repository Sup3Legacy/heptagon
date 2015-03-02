open Heptagon

exception Not_implemented

(* TODO: check that there is no unpunctual in function outputs *)

type unpunctual_var = {
  uv_has_default : bool;
  uv_value : Idents.var_ident;
  uv_clock : Idents.var_ident;
}

let fresh s = Idents.gen_var "punctuality" s

let edesc funs acc = function
| Eontime v -> Evar v, acc
| e -> Hept_mapfold.edesc funs acc e

let node_dec funs acc node =
  let var_dec v (l,acc) =
    if not v.v_unpunctual then
      v :: l, acc
    else begin
      let base_name = Idents.name v.v_ident in
      let clock_ident = fresh (base_name ^ "_clock")
      and value_ident = fresh (base_name ^ "_value") in
      let clock = {v with v_ident = clock_ident;}
      and value = {v with v_ident = value_ident;} in
      clock :: value :: l, acc
    end
  in
  let n_input, acc = List.fold_right var_dec node.n_input ([],acc) in
  let n_block, acc = Hept_mapfold.block_it funs acc node.n_block in
  { node with n_input; n_block; }, acc

let program p =
  let funs = {
    Hept_mapfold.defaults with
    edesc;
    node_dec;
  } in
  let p, _ = Hept_mapfold.program_it funs () p in
  Hept_printer.print stdout p;
  p
