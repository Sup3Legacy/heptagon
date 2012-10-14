(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* removing accessed to shared variables (last x)      *)
open Heptagon
open Hept_utils
open Hept_mapfold
open Idents


let fresh id = Idents.gen_var "last" ("last_"^(Idents.name id))


(* introduce a fresh equation [last_x = pre(x)] for every *)
(* variable declared with a last *)
let last (eq_list, env, v)
  { v_ident = n; v_type = t; v_linearity = lin; v_last = last } =
  match last with
    | Var -> (eq_list, env, v)
    | Last(default) ->
        let lastn = fresh n in
        let default = match default with
        | None -> None
        | Some d -> Some(mk_exp (Econst d) d.Signature.se_ty Linearity.Ltop)
        in
        let ev = mk_exp (Evar n) t Linearity.Ltop in
        let epre = mk_exp (Efby (default, [], ev, [])) t lin in
        let eq = mk_equation (Eeq (Evarpat lastn, epre)) in
        eq:: eq_list,
        Env.add n lastn env,
        (mk_var_dec lastn t lin) :: v

let extend_env env v = List.fold_left last ([], env, []) v

let edesc _ env ed = match ed with
  | Elast x ->
      let lx = Env.find x env in Evar lx, env
  | _ -> raise Errors.Fallback

let block funs env b =
  let eq_lastn_n_list, env, last_v = extend_env env b.b_local in
  let b, _ = Hept_mapfold.block funs env b in
    { b with b_local = b.b_local @ last_v;
        b_equs = eq_lastn_n_list @ b.b_equs }, env

let node_dec funs _ n =
  Idents.push_node n.n_name;
  let _, env, _ = extend_env Env.empty n.n_input in
  let eq_lasto_list, env, last_o = extend_env env n.n_output in
  let n, _  = Hept_mapfold.node_dec funs env n in
  let _ = Idents.pop_node () in
    { n with n_block =
        { n.n_block with b_local = n.n_block.b_local @ last_o;
            b_equs = eq_lasto_list @ n.n_block.b_equs } }, env

let program p =
  let funs = { Hept_mapfold.defaults with
                 node_dec = node_dec; block = block; edesc = edesc } in
  let p, _ = Hept_mapfold.program_it funs Env.empty p in
    p
