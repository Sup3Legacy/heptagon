open Heptagon
open Hept_utils
open Types
open Clocks

(* TODO: check that there is no unpunctual in function outputs *)


type unpunctual_var = {
  uv_has_default : bool;
  uv_value : Idents.var_ident;
  uv_clock : Idents.var_ident;
}

module Env = Idents.Env

exception InvalidProgram


let fresh s = Idents.gen_var "punctuality" s

let var_ident funs env v =
  if Env.mem v env then
    (Env.find v env).uv_value, env
  else
    v, env

let split_unpunctual env param l = 
  match param.e_desc with
  | Evar v when Env.mem v env ->
      let uv = Env.find v env in
      let value_param = {param with e_desc = Evar uv.uv_value}
      and clock_param = {param with e_desc = Evar uv.uv_clock}
      in clock_param :: value_param :: l
  | _ -> param :: l

let edesc funs env = function
| Eontime v ->
    if Env.mem v env then
      Evar (Env.find v env).uv_clock, env
    else
      Econst (Initial.mk_static_bool true), env
| Eapp ({a_op = (Efun f | Enode f)} as app, params, r) ->
    let params = List.fold_right (split_unpunctual env) params [] in
    Eapp (app, params, r), env
| e -> Hept_mapfold.edesc funs env e

let map_unpunctual_pat env base_exp pat =
  let rec aux l = function
  | Etuplepat t ->
      let t, l = Misc.mapfold aux l t in
      Etuplepat t, l
  | Evarpat v ->
      try
        let uv = Env.find v env in
        let eq = mk_equation (Eeq (Evarpat uv.uv_clock, dtrue)) in
        Evarpat (uv.uv_value), eq :: l
      with
      | Not_found -> 
          raise InvalidProgram
  in
  let pat, l = aux [] pat in
  pat, List.rev l

let eq funs eq (l,env) = match eq.eq_desc with
| Eeq (pat, ({e_desc = Eapp ({a_op = (Efun f | Enode f)}, _, _)} as exp)) ->
    let node = Modules.find_value f in
    let eq, env = Hept_mapfold.eq funs env eq in
    if node.Signature.node_unpunctual then
      let exp, env = Hept_mapfold.exp funs env exp in
      let pat, new_eqs = map_unpunctual_pat env exp pat in
      let eq = {eq with eq_desc = Eeq (pat, exp)} in
      eq :: (new_eqs @ l), env
    else
      let eq, env = Hept_mapfold.eq funs env eq in
      eq :: l, env
| _ ->
    let eq, env = Hept_mapfold.eq funs env eq in
    eq :: l, env

let pat funs env = function
  | Etuplepat _ as pat -> Hept_mapfold.pat funs env pat
  | Evarpat v ->
      if Env.mem v env then
        let uv = Env.find v env in
        Etuplepat ([Evarpat uv.uv_value ; Evarpat uv.uv_clock ]), env
      else
        Evarpat v, env

let var_dec v (l,env) =
  if not v.v_unpunctual then
    v :: l, env
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
    let env = Env.add v.v_ident uv env in
    clock :: value :: l, env
  end

let block funs env b =
  let b_local, env = List.fold_right var_dec b.b_local ([],env) in
  let b_equs, env = List.fold_right (eq funs) b.b_equs ([],env) in
  { b with b_local; b_equs; }, env

let node_dec funs env node =
  let env = Env.empty in
  let n_input, env = List.fold_right var_dec node.n_input ([],env) in
  let n_block, env = Hept_mapfold.block_it funs env node.n_block in
  { node with n_input; n_block; }, Env.empty

let split_unpunctual_arg arg l =
  let open Signature in
  if not arg.a_unpunctual then
    arg :: l
  else begin
    let name = match arg.a_name with
    | Some s -> s
    | None -> assert false
  in
    let clock_name = name ^ "_clock"
    and value_name = name ^ "_value"
    in
    let clock = {
      arg with
      a_name = Some clock_name;
      a_type = Tid Initial.pbool;
    }
    and value = {
      arg with
      a_name = Some value_name;
      a_clock = Con (arg.a_clock, Initial.ptrue, clock_name);
    }
    in clock :: value :: l
  end

let replace_sig f node =
  let open Signature in 
  let node_inputs = List.fold_right split_unpunctual_arg node.node_inputs [] in
  Modules.replace_value f {node with node_inputs}

let main p =
  (* Translate the program *)
  let funs = {
    Hept_mapfold.defaults with
    edesc; block; node_dec;
    global_funs = {
      Global_mapfold.defaults with
      var_ident;
    }
  } in
  let p, _ = Hept_mapfold.program_it funs Env.empty p in
  (* Update signatures *)
  Names.QualEnv.iter replace_sig Modules.g_env.values;
  Hept_printer.print stdout p;
  p
