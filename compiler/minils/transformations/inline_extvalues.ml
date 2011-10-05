(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

open Misc
open Names
open Idents
open Signature
open Minils
open Mls_utils
open Mls_printer
open Global_printer
open Types
open Clocks
open Pp_tools
open Mls_compare

(*
  Help tomato by inlining extended values.

  1. Create an environment mapping x to w for each equation of the form "x = w" ;

  2. Traverse the AST, replacing each use of x by its definition ;

  3. Compute potential new formed extended values, e.g. when y = 1 + x becomes y = 1 + w ;

  4. If no new extended value was formed, stop ; else, go back to 1.
*)


let gather_extvalues_node nd =
  let ty_env =
    let add env vd = Env.add vd.v_ident vd.v_type env in
    let add_l env vd_list = List.fold_left add env vd_list in
    (add_l (add_l (add_l Env.empty nd.n_output) nd.n_local) nd.n_input)
  in

  let changed_type w =
    let rec var_of_extvalue w = match w.w_desc with
      | Wvar _ -> Some w
      | Wfield(w, _) -> var_of_extvalue w
      | Wwhen(w, _, _) -> var_of_extvalue w
      | Wconst _ -> None
    in
    match var_of_extvalue w with
      | Some { w_ty = ty; w_desc = Wvar x; } ->
        let ty' = Env.find x ty_env in
        Global_compare.type_compare ty' ty = 0
      | _ -> false
  in

  let gather_extvalues_eq _ env eq =
    let env = match eq.eq_lhs, eq.eq_rhs.e_desc with
      | Evarpat x, Eextvalue w when not (changed_type w) -> Env.add x w env
      | _ -> env
    in
    eq, env
  in

  let funs = { Mls_mapfold.defaults with Mls_mapfold.eq = gather_extvalues_eq; } in
  let _, env = Mls_mapfold.node_dec funs Env.empty nd in
  env

let inline_extvalue_node env nd =
  let inline_extvalue_desc env funs () w_d =
    let w_d, () = Mls_mapfold.extvalue_desc funs () w_d in
    (match w_d with
      | Wvar x -> (try (Env.find x env).w_desc with Not_found -> w_d)
      | _ -> w_d), ()
  in

  let env =
    let funs =
      { Mls_mapfold.defaults with
        Mls_mapfold.extvalue_desc = inline_extvalue_desc env; } in

    let tclose x w new_env =
      let w, () = Mls_mapfold.extvalue funs () w in
      Env.add x w new_env
    in
    Env.fold tclose env Env.empty
  in

  let funs = { Mls_mapfold.defaults with Mls_mapfold.extvalue_desc = inline_extvalue_desc env; } in

  let nd, () = Mls_mapfold.node_dec funs () nd in
  nd

let form_new_extvalue_node nd =
  let rec form_new_extvalue e =
    try
      let se = form_new_const e in
      mk_extvalue ~ty:e.e_ty ~linearity:e.e_linearity ~clock:e.e_base_ck ~loc:e.e_loc (Wconst se)
    with Errors.Fallback ->
      let w_d = match e.e_desc with
        | Eextvalue w -> w.w_desc
        | Ewhen (e, v, x) -> Wwhen (form_new_extvalue e, v, x)
        | _ -> raise Errors.Fallback
      in
      mk_extvalue ~ty:e.e_ty ~linearity:e.e_linearity ~clock:e.e_base_ck ~loc:e.e_loc w_d

  and form_new_const e =
    let se_d = match e.e_desc with
      | Eextvalue { w_desc = Wconst c; } -> c.se_desc

    (* | Eextvalue { w_desc = Wvar n; } -> *)
    (*   (try Svar (Q (qualify_const local_const (ToQ n))) *)
    (*    with Error.ScopingError _ -> raise Errors.Fallback) *)

      | Eapp ({ a_op = Efun ({ qual = Names.Pervasives; } as funn); }, w_list, None) ->
        Sop (funn, form_new_consts w_list)

      | Eapp ({ a_op = Earray_fill; a_params = n_list; }, [w], None) ->
        Sarray_power (form_new_const_w w, n_list)

      | Eapp ({ a_op = Earray; }, w_list, None) ->
        Sarray (form_new_consts w_list)

      | Estruct w_list ->
        Srecord (List.map (fun (f, w) -> f, form_new_const_w w) w_list)

      | _ -> raise Errors.Fallback
    in
    mk_static_exp ~loc:e.e_loc e.e_ty se_d

  and form_new_consts w_list = List.map form_new_const_w w_list

  and form_new_const_w w =
    let mk_exp w =
      mk_exp w.w_ck w.w_ty ~linearity:w.w_linearity ~ck:w.w_ck ~ct:(Ck w.w_ck) (Eextvalue w) in
    form_new_const (mk_exp w)

  and form_new_extvalue_eq _ n eq = match eq.eq_rhs.e_desc with
    | Eextvalue _ -> (eq, n)
    | _ ->
      try
        let w = form_new_extvalue eq.eq_rhs in
        let e = { eq.eq_rhs with e_desc = Eextvalue w; } in
        { eq with eq_rhs = e; }, n + 1
      with Errors.Fallback ->
        eq, n
  in

  let funs = { Mls_mapfold.defaults with Mls_mapfold.eq = form_new_extvalue_eq; } in
  let nd, n = Mls_mapfold.node_dec funs 0 nd in
  nd, n > 0

let compute_needed nd =
  let compute_needed_edesc funs ids e_d =
    let e_d, ids = Mls_mapfold.edesc funs ids e_d in
    e_d,
    (match e_d with
      | Emerge (x, _) -> IdentSet.add x ids
      | Ewhen (_, _, x) -> IdentSet.add x ids
      | Eapp (_, _, Some x) -> IdentSet.add x ids
      | _ -> ids)

  and compute_needed_node funs ids nd =
    let nd, ids = Mls_mapfold.node_dec funs ids nd in
    nd, (List.fold_left (fun ids v -> IdentSet.add v.v_ident ids) ids nd.n_output) in

  let funs =
    { Mls_mapfold.defaults with
      Mls_mapfold.node_dec = compute_needed_node;
      Mls_mapfold.edesc = compute_needed_edesc; } in
  snd (Mls_mapfold.node_dec_it funs IdentSet.empty nd)

let id_set_of_env nd env =
  let needed = compute_needed nd in
  let add id _ ids = if IdentSet.mem id needed then ids else IdentSet.add id ids in
  Env.fold add env IdentSet.empty

let rec node funs () nd =
  let env = gather_extvalues_node nd in
  (* Format.eprintf "=> %d@." (Env.fold (fun _ _ n -> n + 1) env 0); *)
  (* Env.fold (fun x w () -> Format.eprintf "%a => @[%a@]@." print_ident x print_extvalue w) env (); *)
  let nd = inline_extvalue_node env nd in
  let nd = remove_eqs_from_node nd (id_set_of_env nd env) in
  (* IdentSet.iter (fun id -> Format.eprintf "%a@." print_ident id) (id_set_of_env nd env); *)
  let nd, changed = form_new_extvalue_node nd in
  if changed then node funs () nd else (nd, ())

let program program =
  let funs = { Mls_mapfold.defaults with Mls_mapfold.node_dec = node; } in
  let program, () = Mls_mapfold.program funs () program in
  program
