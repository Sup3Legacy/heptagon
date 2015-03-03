open Heptagon
open Types
open Clocks

(* TODO: check that there is no unpunctual in function outputs *)


type unpunctual_var = {
  uv_has_default : bool;
  uv_value : Idents.var_ident;
  uv_clock : Idents.var_ident;
}

module Env = Idents.Env





let fresh s = Idents.gen_var "punctuality" s

let edesc funs acc = function
| Eontime v ->
    if Env.mem v acc then
      Evar (Env.find v acc).uv_clock, acc
    else
      Evar v, acc
| Evar v ->
    if Env.mem v acc then
      Evar (Env.find v acc).uv_value, acc
    else
      Evar v, acc
| Eapp ({a_op = (Efun f | Enode f)} as app, e_list, r) ->
    begin try
      let node = Modules.find_value f in
      ignore (node)
    with Not_found -> ()
    end;
    Eapp(app, e_list, r), acc
| e -> Hept_mapfold.edesc funs acc e

let pat funs acc = function
  | Etuplepat _ as pat -> Hept_mapfold.pat funs acc pat
  | Evarpat v ->
    if Env.mem v acc then
      let uv = Env.find v acc in
      Etuplepat ([Evarpat uv.uv_value ; Evarpat uv.uv_clock ]), acc
    else
      Evarpat v, acc



let var_dec v (l,acc) =
  if not v.v_unpunctual then
    v :: l, acc
  else begin
    let base_name = Idents.name v.v_ident in
    let clock_ident = fresh (base_name ^ "_clock")
    and value_ident = fresh (base_name ^ "_value") in
    let clock = {v with
      v_ident = clock_ident;
      v_type = Tid Initial.pbool;
    }
    and value = {v with
      v_ident = value_ident;
      v_clock = Con (v.v_clock, Initial.ptrue, clock_ident);
    }
    in
    let uv = {
      uv_has_default = false;
      uv_value = value_ident;
      uv_clock = clock_ident;
    }
    in
    let acc = Env.add v.v_ident uv acc in
    clock :: value :: l, acc
  end

let block funs acc b =
  let b_local, acc = List.fold_right var_dec b.b_local ([],acc) in
  let b_equs, acc = Misc.mapfold (Hept_mapfold.eq_it funs) acc b.b_equs in
  { b with b_local; b_equs; }, acc

let node_dec funs acc node =
  let acc = Env.empty in
  let n_input, acc = List.fold_right var_dec node.n_input ([],acc) in
  let n_block, acc = Hept_mapfold.block_it funs acc node.n_block in
  { node with n_input; n_block; }, Env.empty

let program p =
  let funs = {
    Hept_mapfold.defaults with
    edesc; pat; block; node_dec;
  } in
  let p, _ = Hept_mapfold.program_it funs Env.empty p in
  Hept_printer.print stdout p;
  p
