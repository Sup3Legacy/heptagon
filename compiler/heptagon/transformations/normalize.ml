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
open Location
open Heptagon
open Hept_utils
open Hept_mapfold
open Signature
open Clocks
open Linearity
open Format

(** Normalization pass
    The normal form of the language is given in the manual *)

module Error =
struct
  type error =
    | Eunsupported_language_construct

  let message loc kind =
    begin match kind with
      | Eunsupported_language_construct ->
          eprintf "%aThis construct is not supported by MiniLS.@."
            print_location loc
    end;
    raise Errors.Error
end

let exp_list_of_static_exp_list se_list =
  let mk_one_const se =
    mk_exp (Econst se) se.se_ty ~linearity:Ltop
  in
    List.map mk_one_const se_list

let is_list e = match e.e_desc with
 | Eapp({ a_op = Etuple }, _, _)
 | Econst { se_desc = Stuple _ } -> true
 | _ -> false

let e_to_e_list e = match e.e_desc with
  | Eapp({ a_op = Etuple }, e_list, _) -> e_list
  | Econst { se_desc = Stuple se_list } ->
      exp_list_of_static_exp_list se_list
  | _ -> assert false

let flatten_e_list l =
  let flatten = function
    | { e_desc = Eapp({ a_op =  Etuple }, l, _) } -> l
    | e -> [e]
  in
    List.flatten (List.map flatten l)

(** Creates a new equation x = e, adds x to d_list
    and the equation to eq_list. *)
let equation (d_list, eq_list) e =
  let add_one_var ty lin d_list =
    let n = Idents.gen_var "normalize" "v" in
    let d_list = (mk_var_dec n ty lin) :: d_list in
      n, d_list
  in
    match e.e_ty with
      | Tprod ty_list ->
          let lin_list =
            (match e.e_linearity with
              | Ltuple l -> l
              | Ltop -> Misc.repeat_list Ltop (List.length ty_list)
              | _ -> assert false)
          in
          let var_list, d_list =
            mapfold2 (fun d_list ty lin -> add_one_var ty lin d_list) d_list ty_list lin_list in
          let pat_list = List.map (fun n -> Evarpat n) var_list in
          let eq_list = (mk_equation (Eeq (Etuplepat pat_list, e))) :: eq_list in
          let e_list = Misc.map3
            (fun n ty lin -> mk_exp (Evar n) ty lin) var_list ty_list lin_list in
          let e = Eapp(mk_app Etuple, e_list, None) in
            (d_list, eq_list), e
      | _ ->
          let n, d_list = add_one_var e.e_ty e.e_linearity d_list in
          let eq_list = (mk_equation (Eeq (Evarpat n, e))) :: eq_list in
            (d_list, eq_list), Evar n

(* [(e1,...,ek) when C(n) = (e1 when C(n),...,ek when C(n))] *)
let rec whenc context e c n e_orig =
  let when_on_c c n e =
    { e_orig with e_desc = Ewhen(e, c, n); }
  in
    if is_list e then (
      let e_list = List.map (when_on_c c n) (e_to_e_list e) in
          context, { e_orig with e_desc = Eapp(mk_app Etuple, e_list, None) }
    ) else
      context, when_on_c c n e

type kind = ExtValue | Any

(** Creates an equation and add it to the context if necessary. *)
let add context expected_kind e =
  let up = match e.e_desc, expected_kind with
     (* static arrays should be normalized to simplify code generation *)
    | Econst { se_desc = Sarray _ }, ExtValue -> true
    | (Evar _ | Eapp ({ a_op = Efield | Etuple | Ereinit }, _, _) | Ewhen _
          | Econst _) , ExtValue -> false
    | _ , ExtValue -> true
    | _ -> false in
  if up then
    let context, n = equation context e in
      context, { e with e_desc = n }
  else
    context, e

let add_list context expected_kind e_list =
  let aux context e =
    let context, e = add context expected_kind e in
      e, context
  in
    mapfold aux context e_list

let rec translate kind context e =
  let context, e' = match e.e_desc with
    | Econst _
    | Evar _ -> context, e
    | Epre(v, e1) -> fby kind context e v e1
    | Efby({ e_desc = Econst v },se, e1) ->
        assert (se = None);
        fby kind context e (Some v) e1
    | Estruct l ->
        let translate_field context (f, e) =
          let context, e = translate ExtValue context e in
            (f, e), context
        in
        let l, context = mapfold translate_field context l in
          context, { e with e_desc = Estruct l }
    | Ewhen(e1, c, n) ->
        let context, e1 = translate kind context e1 in
          whenc context e1 c n e
    | Emerge(n, tag_e_list) ->
        merge context e n tag_e_list
    | Eapp({ a_op = Eifthenelse }, [e1; e2; e3], _) ->
        ifthenelse context e e1 e2 e3
    | Eapp(app, e_list, r) ->
        let context, e_list = translate_list ExtValue context e_list in
          context, { e with e_desc = Eapp(app, flatten_e_list e_list, r) }
    | Eiterator (it, app, n, pe_list, e_list, reset) ->
        let context, pe_list = translate_list ExtValue context pe_list in
        let context, e_list = translate_list ExtValue context e_list in
        context, { e with e_desc = Eiterator(it, app, n, flatten_e_list pe_list,
                                             flatten_e_list e_list, reset) }
    | Esplit (x, cl, e1) ->
        let context, e1 = translate ExtValue context e1 in
        let mk_when c = mk_exp ~linearity:e1.e_linearity (Ewhen (e1, c, x)) e1.e_ty in
        let el = List.map mk_when cl in
        context, { e with e_desc = Eapp(mk_app Etuple, el, None) }
    | Elast _ | Efby _ ->
        Error.message e.e_loc Error.Eunsupported_language_construct
  in add context kind e'

and translate_list kind context e_list =
  match e_list with
    | [] -> context, []
    | e :: e_list ->
        let context, e = translate kind context e in
        let context, e_list = translate_list kind context e_list in
          context, e :: e_list

and fby kind context e v e1 =
  let mk_fby c e =
    mk_exp ~loc:e.e_loc (Epre(Some c, e)) e.e_ty ~linearity:Ltop in
  let mk_pre e =
    mk_exp ~loc:e.e_loc (Epre(None, e)) e.e_ty ~linearity:Ltop in
  let context, e1 = translate ExtValue context e1 in
  match e1.e_desc, v with
    | Eapp({ a_op = Etuple } as app, e_list, r),
      Some { se_desc = Stuple se_list } ->
        let e_list = List.map2 mk_fby se_list e_list in
        let e = { e with e_desc = Eapp(app, e_list, r) } in
          translate kind context e
    | Econst { se_desc = Stuple se_list },
      Some { se_desc = Stuple v_list } ->
        let e_list = List.map2 mk_fby v_list
          (exp_list_of_static_exp_list se_list) in
        let e = { e with e_desc = Eapp(mk_app Etuple, e_list, None) } in
          translate kind context e
    | Eapp({ a_op = Etuple } as app, e_list, r), None ->
        let e_list = List.map mk_pre e_list in
        let e = { e with e_desc = Eapp(app, e_list, r) } in
          translate kind context e
    | Econst { se_desc = Stuple se_list }, None ->
        let e_list = List.map mk_pre (exp_list_of_static_exp_list se_list) in
        let e = { e with e_desc = Eapp(mk_app Etuple, e_list, None) } in
          translate kind context e
    | _ -> context, { e with e_desc = Epre(v, e1) }

(** transforms [if x then e1, ..., en else e'1,..., e'n]
    into [if x then e1 else e'1, ..., if x then en else e'n]  *)
and ifthenelse context e e1 e2 e3 =
  let context, e1 = translate ExtValue context e1 in
  let context, e2 = translate ExtValue context e2 in
  let context, e3 = translate ExtValue context e3 in
  let mk_ite_list e2_list e3_list =
    let mk_ite e'2 e'3 =
      mk_exp ~loc:e.e_loc
        (Eapp (mk_app Eifthenelse, [e1; e'2; e'3], None)) e'2.e_ty ~linearity:e'2.e_linearity
    in
    let e_list = List.map2 mk_ite e2_list e3_list in
      { e with e_desc = Eapp(mk_app Etuple, e_list, None) }
  in
    if is_list e2 then (
      let e2_list, context = add_list context ExtValue (e_to_e_list e2) in
      let e3_list, context = add_list context ExtValue (e_to_e_list e3) in
        context, mk_ite_list e2_list e3_list
    ) else
      context, { e with e_desc = Eapp (mk_app Eifthenelse, [e1; e2; e3], None) }

(** transforms [merge x (c1, (e11,...,e1n));...;(ck, (ek1,...,ekn))] into
    [merge x (c1, e11)...(ck, ek1),..., merge x (c1, e1n)...(ck, ekn)]    *)
and merge context e x c_e_list =
    let translate_tag context (tag, e) =
      let context, e = translate ExtValue context e in
        (tag, e), context
    in
    let rec mk_merge x c_list e_lists =
      let ty = (List.hd (List.hd e_lists)).e_ty in
      let lin = (List.hd (List.hd e_lists)).e_linearity in
      let rec build_c_e_list c_list e_lists =
        match c_list, e_lists with
        | [], [] -> [], []
        | c::c_l, (e::e_l)::e_ls ->
            let c_e_list, e_lists = build_c_e_list c_l e_ls in
            (c,e)::c_e_list, e_l::e_lists
        | _ -> assert false in
      let rec build_merge_list c_list e_lists =
        match e_lists with
          [] -> assert false
        | []::_ -> []
        | _ ::_ ->
            let c_e_list, e_lists = build_c_e_list c_list e_lists in
            let e_merge = mk_exp ~loc:e.e_loc (Emerge(x, c_e_list)) ty ~linearity:lin in
            let e_merge_list = build_merge_list c_list e_lists in
            e_merge::e_merge_list in
      build_merge_list c_list e_lists
    in
    let c_e_list, context = mapfold translate_tag context c_e_list in
      match c_e_list with
        | [] -> assert false
        | (_,e1)::_ ->
            if is_list e1 then (
              let c_list = List.map (fun (t,_) -> t) c_e_list in
              let e_lists = List.map (fun (_,e) -> e_to_e_list e) c_e_list in
              let e_lists, context =
                mapfold
                  (fun context e_list -> add_list context ExtValue e_list)
                  context e_lists in
              let e_list = mk_merge x c_list e_lists in
                context, { e with
                             e_desc = Eapp(mk_app Etuple, e_list, None) }
            ) else
              context, { e with
                           e_desc = Emerge(x, c_e_list) }

(* applies distribution rules *)
(* [(p1,...,pn) = (e1,...,en)] into [p1 = e1;...;pn = en] *)
and distribute ((d_list, eq_list) as context) eq pat e =
  let dist_e_list pat_list e_list =
    let mk_eq pat e =
      mk_equation (Eeq (pat, e))
    in
    let dis context eq = match eq.eq_desc with
      | Eeq (pat, e) -> distribute context eq pat e
      | _ -> assert false
    in
    let eqs = List.map2 mk_eq pat_list e_list in
      List.fold_left dis context eqs
  in
    match pat, e.e_desc with
      | Etuplepat(pat_list), Eapp({ a_op = Etuple }, e_list, _) ->
          dist_e_list pat_list e_list
      | Etuplepat(pat_list), Econst { se_desc = Stuple se_list } ->
          dist_e_list pat_list (exp_list_of_static_exp_list se_list)
      | _ ->
          let eq = mk_equation ~loc:eq.eq_loc (Eeq(pat, e)) in
            d_list,  eq :: eq_list

and translate_eq ((d_list, eq_list) as context) eq = match eq.eq_desc with
  | Eeq (pat, e) ->
      let context, e = translate Any context e in
        distribute context eq pat e
  | Eblock b ->
      let v, eqs = translate_eq_list [] b.b_equs in
      let eq =
        mk_equation ~loc:eq.eq_loc (Eblock { b with b_local = v @ b.b_local; b_equs = eqs})
      in
      d_list, eq :: eq_list
  | _ -> Misc.internal_error "normalize"

and translate_eq_list d_list eq_list =
  List.fold_left
    (fun context eq -> translate_eq context eq)
    (d_list, []) eq_list

let eq funs context eq =
  let context = translate_eq context eq in
    eq, context

let block funs _ b =
  let _, (v_acc, eq_acc) = Hept_mapfold.block funs ([],[]) b in
    { b with b_local = v_acc@b.b_local; b_equs = eq_acc}, ([], [])

let contract funs context c =
  let ({ c_block = b } as c), void_context =
    Hept_mapfold.contract funs context c in
  (* Non-void context could mean lost equations *)
  assert (void_context=([],[]));
  let context, e_a = translate ExtValue ([],[]) c.c_assume in
  let context, e_e = translate ExtValue context c.c_enforce in
  let (d_list, eq_list) = context in
  { c with
      c_assume = e_a;
      c_enforce = e_e;
      c_block = { b with
                    b_local = d_list@b.b_local;
                    b_equs = eq_list@b.b_equs; }
  }, void_context

let program p =
  let funs = { defaults with block = block; eq = eq; contract = contract } in
  let p, _ = Hept_mapfold.program funs ([], []) p in
    p
