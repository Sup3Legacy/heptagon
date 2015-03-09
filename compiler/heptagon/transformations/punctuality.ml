open Heptagon
open Hept_utils
open Types
open Clocks
open Names

(* TODO: check that there is no unpunctual in function outputs *)


type unpunctual_var = {
  uv_has_default : bool;
  uv_decl : var_dec;
  uv_value : Idents.var_ident;
  uv_clock : Idents.var_ident;
}

module Env = Idents.Env

exception InvalidProgram


let fresh s = Idents.gen_var "punctuality" s

let var_ident funs env v =
  try
    let uv = Env.find v env in
    if uv.uv_has_default then
      v, env
    else
      uv.uv_value, env
  with Not_found ->
    v, env

let param env param l = 
  match param.e_desc with
  | Evar v when Env.mem v env ->
      let uv = Env.find v env in
      let clock_param = {param with e_desc = Evar uv.uv_clock}
      and value_param = {param with e_desc = Evar uv.uv_value}

(*      and value_param = {param with e_desc = Ewhen (
        {param with e_desc = Evar uv.uv_value},
        Initial.ptrue,
        uv.uv_clock)} *)
      in
      clock_param :: value_param :: l
  | _ -> param :: l

let edesc funs env = function
| Eontime v ->
    if Env.mem v env then
      Evar (Env.find v env).uv_clock, env
    else
      Econst (Initial.mk_static_bool true), env
| Eapp ({a_op = (Efun f | Enode f)} as app, params, r) as e ->
    let params = List.fold_right (param env) params [] in
    Eapp (app, params, r), env
| e -> Hept_mapfold.edesc funs env e

let map_unpunctual_pat env base_exp pat =
  let rec aux (vl,el) = function
  | Etuplepat t ->
      let t, l = Misc.mapfold aux (vl,el) t in
      Etuplepat t, l
  | Evarpat v ->
      try
        let uv = Env.find v env in
        let base_name = Idents.name v
        and ty = uv.uv_decl.v_type in
        let tmp_ident = fresh (base_name ^ "_tmp") in
        let eq1 = mk_equation (Eeq (Evarpat uv.uv_clock, dtrue))
        and eq2 = mk_equation (Eeq (Evarpat uv.uv_value, mk_exp (Ewhen (
          mk_exp (Evar tmp_ident) ty,
          Initial.ptrue,
          uv.uv_clock)) ty))
        and vd = {uv.uv_decl with v_ident = tmp_ident;} in
        Evarpat (tmp_ident), (vd :: vl, eq1 :: eq2 :: el)
      with
      | Not_found -> 
          raise InvalidProgram
  in
  let pat, (vl,el) = aux ([],[]) pat in
  pat, List.rev vl, List.rev el

let eq funs eq (vl,el,env) = match eq.eq_desc with
| Eeq (pat, ({e_desc = Eapp ({a_op = (Efun f | Enode f)}, _, _)} as exp)) ->
    let node = Modules.find_value f in
    let eq, env = Hept_mapfold.eq funs env eq in
    if node.Signature.node_unpunctual then
      let exp, env = Hept_mapfold.exp funs env exp in
      let pat, new_vars, new_eqs = map_unpunctual_pat env exp pat in
      let eq = {eq with eq_desc = Eeq (pat, exp)} in
      new_vars @ vl, eq :: (new_eqs @ el), env
    else
      let eq, env = Hept_mapfold.eq funs env eq in
      vl, eq :: el, env
| _ ->
    let eq, env = Hept_mapfold.eq funs env eq in
    vl, eq :: el, env

let pat funs env = function
  | Etuplepat _ as pat -> Hept_mapfold.pat funs env pat
  | Evarpat v ->
      if Env.mem v env then
        let uv = Env.find v env in
        Etuplepat ([Evarpat uv.uv_value ; Evarpat uv.uv_clock ]), env
      else
        Evarpat v, env

let var_dec v (vl,ll,el,env) =
  match v.v_punctuality with
  | Punctual -> v :: vl, ll, el, env
  | Unpunctual default ->
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
        uv_has_default = default <> None;
        uv_decl = v;
        uv_value = value_ident;
        uv_clock = clock_ident;
      }
      in
      let env = Env.add v.v_ident uv env in
      let ll, el = match default with
      | None -> ll, el
      | Some exp ->
          let eq = mk_equation (Eeq (
            Evarpat v.v_ident,
            mk_exp (Emerge (
              clock_ident, [
              Initial.ptrue, mk_exp (Evar value_ident) v.v_type; 
              Initial.pfalse, exp;
              ])) v.v_type))
          in
          v :: ll, eq :: el
      in 
      clock :: value :: vl, ll, el, env

let block funs env b =
  let b_local, more_locals, more_equs, env =
    List.fold_right var_dec b.b_local ([],[],[],env) in
  let more_vars, b_equs, env = List.fold_right (eq funs) b.b_equs ([],[],env) in
  let b_local = b_local @ more_locals @ more_vars
  and b_equs = more_equs @ b_equs in
  { b with b_local; b_equs; }, env

let node_dec funs env node =
  let env = Env.empty in
  let n_input, more_locals, more_equs, env =
    List.fold_right var_dec node.n_input ([],[],[],env) in
  let n_block, env = Hept_mapfold.block_it funs env node.n_block in
  let n_block = {
    n_block with
    b_local = n_block.b_local @ more_locals;
    b_equs = more_equs @ n_block.b_equs;
  } in
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
  QualEnv.iter replace_sig Modules.g_env.values;
  Hept_printer.print stdout p;
  p
