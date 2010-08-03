(** {1 VHDL Backend}

    This is an experimental VHDL backend for MiniLS. It targets VHDL'87, as it
    is the best revision implemented in GHDL. It translates data-flow/MiniLS
    programs to VHDL programs, and associates a VHDL component to each node.

    Compilation model: translate a normalized and scheduled MiniLS node to a
    VHDL component with MiniLS variables defined by sequential equations (fby /
    pre) as VHDL signals. MiniLS equations will be translated to a VHDL process
    whose statement list is a translation of individual equations.

    Floating-point numbers are unsupported.
*)

open Names
open Misc
open Minils
open Idents
open Types
open Initial
open Static
open Vhdl
open Signature
open Mls_utils
open Location
open Clocks

(* TODO: find a better way to access type information *)
let tys = ref []

let mk_c cd = Ve_const (mk_static_exp cd)

(** {3 Conventions} *)

let zero = Ve_const (mk_static_exp (Sbool false))
let one = Ve_const (mk_static_exp (Sbool true))

let mk_o_s on = "o_" ^ on
let mk_o on = Vl_var (mk_o_s on)

let mk_arg_s s = "arg" ^ s
let mk_arg s = Vl_var (mk_arg_s s)

let mk_ck_s n = "arg_ck_" ^ string_of_int n
let mk_ck n = Vl_var (mk_ck_s n)

let mk_rs_n n = "arg_rs_" ^ string_of_int n
let mk_rs n = Vl_var (mk_rs_n n)

let ren_o s = { s with vs_name = mk_o_s s.vs_name; }

let bool_t = Tid pbool

let rst_e = mk_exp ~exp_ty:bool_t (Evar rs_n)

let eval_static_size se = Static.int_of_static_exp NamesEnv.empty se

module AddRst =
struct
  open Mls_mapfold

  let mk_or_rst ro = match ro with
    | None -> rst_e
    | Some x ->
        let e_x = mk_exp ~exp_ty:bool_t (Evar x) in
        { rst_e with
            e_desc = Eapp (mk_app (Efun (Modname { qual = "Pervasives";
                                                   id = "or"; })),
                           [rst_e; e_x],
                           None); }

  let add_rst_edesc funs () edesc =
    let (edesc, ()) = Mls_mapfold.edesc funs () edesc in
    match edesc with
      | Efby (Some c, e) ->
          (Eapp (mk_app Eifthenelse,
                 [rst_e;
                  { e with e_desc = Econst c; };
                  { e with e_desc = Efby (Some c, e); }],
                 None),
           ())
      | Eapp ({ a_op = Enode _; } as app, e_list, ro) ->
          (Eapp (app,
                 mk_or_rst ro :: e_list,
                 None),
           ())
      | Eiterator (it, ({ a_op = Enode _; } as app), se, e_list, ro) ->
          let rst_arr =
            let rst_e = mk_or_rst ro in
            let app = mk_app ~params:[se] Earray_fill in
            mk_exp ~exp_ty:(Tarray (bool_t, se)) (Eapp (app, [rst_e], None)) in
          (Eiterator (it, app, se, rst_arr :: e_list, None), ())
      | _ -> raise Fallback

  let add_rst_node_dec funs () nd =
    let (nd, ()) = Mls_mapfold.node_dec funs () nd in
    ({ nd with n_input = mk_var_dec rs_n bool_t :: nd.n_input; }, ())

  let program p =
    let funs = { Mls_mapfold.defaults with
                   edesc = add_rst_edesc;
                   node_dec = add_rst_node_dec; } in
    fst (Mls_mapfold.program funs () p)
end

module SimpCalls =
struct
  open Mls_mapfold

  let empty_acc = ([], [])

  let simp_calls_edesc funs (vars, equs) edesc = match edesc with
    | Eapp ({ a_op = Enode nn; } as app, e_list, None) ->
        let add_eq (vars, equs) e =
          let arg = Idents.fresh "arg" in
          let e_arg = mk_exp ~exp_ty:e.e_ty (Evar arg) in
          let vd_arg = mk_var_dec arg e.e_ty
          and eq_arg = mk_equation (Evarpat arg) e in
          (e_arg, (vd_arg :: vars, eq_arg :: equs)) in

        let e_list, acc = mapfold (Mls_mapfold.exp funs) (vars, equs) e_list in
        let e_list, acc = mapfold add_eq acc e_list in

        (Eapp (app, e_list, None), acc)
    | _ -> raise Fallback

  let simp_calls_node_dec funs acc nd =
    let (nd, (vars, equs)) = Mls_mapfold.node_dec funs acc nd in
    { nd with n_equs = equs @ nd.n_equs; n_local = vars @ nd.n_local; },
    empty_acc

  let program p =
    let funs = { Mls_mapfold.defaults with
                   edesc = simp_calls_edesc;
                   node_dec = simp_calls_node_dec; } in
    fst (Mls_mapfold.program funs empty_acc p)
end

module InlineIterators =
struct
  open Mls_mapfold

  let empty_acc = ([], [])

  let rec gen f init i = match i with
    | -1 -> init
    | n -> f i (gen f init (i - 1))

  let inline_iterator_eq funs (varl, equs) eq =
    let (eq, (varl, equs)) = Mls_mapfold.eq funs (varl, equs) eq in
    match eq.eq_rhs.e_desc with
      | Eiterator (it, app, ssize, y_l, rst) ->
          let ty_r = match (it, eq.eq_rhs.e_ty) with
            | (Imapfold, (Tprod [Tarray (ty, _); _] | ty)) -> ty
            | (_, (Tarray (ty, _) | ty)) -> ty in

          let ck = eq.eq_rhs.e_ck in

          let n = eval_static_size ssize in

          let select i e =
            let app = mk_app ~params:[mk_static_exp (Sint i)] Eselect in
            mk_exp ~exp_ty:ty_r ~clock:e.e_ck (Eapp (app, [e], None)) in

          (* creates y_1(i), ..., y_m(i) *)
          let mk_args y_l i = List.map (select i) y_l in

          let mk_new_var s =
            let z = Idents.fresh s in
            (z,
             mk_var_dec ~clock:ck z ty_r,
             mk_exp ~exp_ty:ty_r ~clock:ck (Evar z)) in
          let mk_new_z () = mk_new_var "z" in

          (match it with
             | Imap ->
                 (*
                    x = map f<<n>> (y_1, ..., y_m);

                    -->

                    z_1 = f(y_1(1), ..., y_m(1));
                    ...
                    z_n = f(y_1(n), ..., y_m(n));
                    x = [z_1, ..., z_n];
                 *)

                 let mk_eq i (z_l, (varl, equs)) =
                   let (z, z_var, z_e) = mk_new_z () in
                   let exp_f =
                     mk_exp ~exp_ty:ty_r ~clock:ck
                       (Eapp (app, mk_args y_l i, rst)) in
                   (z_e :: z_l,
                    (z_var :: varl, mk_equation (Evarpat z) exp_f :: equs)) in

                 let (zl, (varl, equs)) =
                   gen mk_eq ([], (varl, equs)) (n - 1) in
                 let new_eq_e =
                   { eq.eq_rhs with
                       e_desc = Eapp (mk_app Earray, zl, None); } in
                 ({ eq with eq_rhs = new_eq_e; }, (varl, equs))

             | Ifold ->
                 (*
                    x = fold f<<n>> (y_1, ..., y_m, acc);

                    -->

                    z_1 = f(y_1(n), ..., y_m(n), acc);
                    ...
                    z_n = f(y_1(1), ..., y_m(1), z_(n - 1));
                    x = z_n;
                 *)
                 let (y_l, acc) = split_last y_l in

                 let add_eq i (z_prev, varl, equs) =
                   let (z, z_var, z_e) = mk_new_z () in
                   let exp_f =
                     mk_exp ~exp_ty:ty_r ~clock:ck
                       (Eapp (app, (mk_args y_l i) @ [z_prev], rst)) in
                   let new_eq = mk_equation (Evarpat z) exp_f in
                   (z_e, z_var :: varl, new_eq :: equs) in

                 let (z_last, varl, equs) =
                   gen add_eq (acc, varl, equs) (n - 1) in
                 ({ eq with eq_rhs = z_last; }, (varl, equs))

             | Imapfold ->
                 (*
                   (x, acc_r) = mapfold f<<n>> (y_1, ..., y_m, acc);

                   -->

                    z_1, acc_1 = f(y_1(n), ..., y_m(n), acc);
                    ...
                    z_n, acc_n = f(y_1(1), ..., y_m(1), acc_(n - 1));
                    x = [z_1, ..., z_n];
                    acc_r = acc_n;
                 *)
                 let (y_l, acc) = split_last y_l in

                 let add_eq i (acc_prev, res_l, var_l, eq_l) =
                   let (z, z_var, z_e) = mk_new_z () in
                   let (acc, acc_var, acc_e) = mk_new_var "acc" in
                   let exp_f =
                     mk_exp
                       ~exp_ty:(match eq.eq_rhs.e_ty with
                                  | Tprod [_; ty] -> Tprod [ty_r; ty]
                                  | _ -> assert false)
                       ~clock:ck
                       (Eapp (app, (mk_args y_l i) @ [acc_prev], rst)) in
                   let new_eq =
                     mk_equation (Etuplepat [Evarpat z; Evarpat acc]) exp_f in
                   (acc_e, z_e :: res_l, z_var :: acc_var :: var_l,
                    new_eq :: eq_l) in

                 let (acc_last, resl, varl, equs) =
                   gen add_eq (acc, [], varl, equs) (n - 1) in
                 (match eq.eq_lhs with
                    | Etuplepat [Evarpat x; Evarpat acc] ->
                        (mk_equation
                           (Evarpat x)
                           (mk_exp
                              ~exp_ty:(Tarray (ty_r, ssize))
                              (Eapp (mk_app Earray, resl, None))),
                         (varl, mk_equation (Evarpat acc) acc_last :: equs))
                    | _ -> assert false))
      | _ -> (eq, (varl, equs))

  let inline_iterator_node_dec funs acc nd =
    let (nd, (varl, equs)) = Mls_mapfold.node_dec funs acc nd in
    ({ nd with n_local = varl @ nd.n_local; n_equs = equs @ nd.n_equs; },
     empty_acc)

  let program p =
    let funs = { Mls_mapfold.defaults with
                   eq = inline_iterator_eq;
                   node_dec = inline_iterator_node_dec; } in
    fst (Mls_mapfold.program funs empty_acc p)
end

(** {2 Translation from MiniLS programs to VHDL programs} *)

let rec trans_ty ty = match ty with
  | Tid (Name s | Modname { id = s; }) ->
      Vt_id (Name (try
                     let table =
                       [
                         ("int", "integer");
                         ("bool", "std_logic");
                       ] in
                     List.assoc s table
                   with Not_found -> s))
  | Tarray (ty, i) -> Vt_array (eval_static_size i - 1, trans_ty ty)
  | Tprod _ -> assert false

let signal_of_vardec mode vd =
  { vs_name = name vd.v_ident; vs_polarity = Some mode;
    vs_type = trans_ty vd.v_type; }

let interface_signals_of_node nd =
  let input_signals = List.map (signal_of_vardec Vp_in) nd.n_input in
  let output_signals =
    List.map (fun vd -> ren_o (signal_of_vardec Vp_out vd)) nd.n_output in
  (native_signals @ input_signals, output_signals)

let rec guard_exp ck = match ck with
  | Cbase | Cvar { contents = Cindex _; } ->
      Ve_funcall ("rising_edge", [mk_vare (name ck_n)])
  | Con (ck, ln, n) ->
      Ve_bop ("and",
              Ve_bop ("=",
                      Ve_const (mk_static_exp (Sconstructor ln)),
                      mk_vare (name n)),
              guard_exp ck)
  | Cvar { contents = Clink ck; } -> guard_exp ck

let rec make_clock ck = match ck with
  | Cbase -> mk_vare (name ck_n)
  | Con (ck, ln, n) ->
      Ve_bop ("and",
              Ve_funcall ("to_logic",
                          [Ve_bop ("=",
                                   Ve_const (mk_static_exp (Sconstructor ln)),
                                   mk_vare (name n))]),
              make_clock ck)
  | Cvar lr -> (match !lr with Clink ck -> make_clock ck | _ -> assert false)
      (* I do not know what Cindex constructors are! *)

let rec trad_exp e = match e.e_desc with
  | Econst c -> Ve_const c
  | Evar n -> mk_vare (name n)
  | Ewhen (e, _, _) -> trad_exp e
  | Estruct lnel -> Ve_record (List.map (fun (ln, e) -> (ln, trad_exp e)) lnel)
  | Eapp ({ a_op = op; a_params = pl; }, el, None) -> trad_app e op pl el
  | Eapp (_, _, Some _) -> assert false
  | Eiterator _ -> assert false
  | Emerge _ | Efby _ -> assert false

and trad_app e op pl el = match op, el, pl with
  | Enode _, _, _ -> assert false
  | Efun ln, _, _ ->
      let (vhdl_op, need_conv) =
        try List.assoc (fullname ln) op_table
        with Not_found ->
          Printf.eprintf "Unknown operator %s\n" (fullname ln);
          assert false in

      let mk e = if need_conv then Ve_funcall ("to_logic", [e]) else e in

      (match el with
         | [l; r] -> mk (Ve_bop (vhdl_op, trad_exp l, trad_exp r))
         | [e] -> mk (Ve_uop (vhdl_op, trad_exp e))
         | l ->
             Printf.eprintf "VHDL: unknown operator %s in\n"
               (fullname ln);
             raise Misc.Error)
  | Econcat, [l; r], _ -> Ve_concat (trad_exp l, trad_exp r)
  | Earray, _, _ -> Ve_array (List.map trad_exp el)
  | Eselect, [e], sl ->
      let cl =
        let mk c = Ve_const (mk_static_exp (Sint (eval_static_size c))) in
        List.map mk sl in
      Ve_array_index (trad_exp e, cl)
  | Eselect_slice, [e], [low; high] ->
      Ve_slice (eval_static_size low, eval_static_size high, trad_exp e)
  | Earray_fill, [e], [ssize] ->
      let n = eval_static_size ssize in
      Ve_array_repeat (n, trad_exp e)
  | Efield, [e], [{ se_desc = Sconstructor fn; }] ->
      Ve_field (trad_exp e, fn)
  | _ ->
      Printf.eprintf "Unexpected expression:\n";
      Mls_printer.print_exp stderr e;
      assert false

let rec trad_cexpr e dst = match e.e_desc with
  | Emerge (n, cel) | Ewhen ({ e_desc = Emerge (n, cel); }, _, _) ->
      let trad_cl (c, e) = (mk_static_exp (Sconstructor c), trad_cexpr e dst) in
      Vi_case (mk_vare (name n), List.map trad_cl cel)

  | Eapp ({ a_op = Eselect_dyn; }, arr :: def :: idxl, None) ->
      let rec acc idxl boundl (guardl, idxel) = match (idxl, boundl) with
        | ([], _) -> (guardl, idxel)
        | (idx :: idxl, bound :: bounds) ->
            let idxe = trad_exp idx in
            let b_i = eval_static_size bound in
            let guard = Ve_bop ("and",
                                Ve_bop(">", idxe, mk_c (Sint 0)),
                                Ve_bop("<", idxe, mk_c (Sint b_i))) in
            acc idxl boundl (guard :: guardl, idxe :: idxel)
        | (l, r) ->
            Printf.eprintf "%d %d\n" (List.length l) (List.length r);
            assert false in
      let (guardl, indl) = acc idxl (Mls_utils.bounds_list arr.e_ty) ([], []) in
      let guard = fold_right_1 (fun l r -> Ve_bop ("and", l, r)) guardl in
      let else_branch = Vi_affect (dst, trad_exp def) in
      Vi_if (guard, Vi_affect (dst, Ve_array_index (trad_exp arr, indl)),
             [], Some else_branch)

  | Eapp ({ a_op = Eupdate; a_params = idxl; }, [arr; newval], None) ->
      let mk_lhs idx lhs =
        Vl_arr (lhs, mk_c (Sint (eval_static_size idx))) in
      let lhs = List.fold_right mk_lhs idxl dst in
      Vi_seq [
        Vi_affect (dst, trad_exp arr);
        Vi_affect (lhs, trad_exp newval);
      ]

  | _ -> Vi_affect (dst, trad_exp e)

let trad_eq eq (n, is) = match (eq.eq_lhs, eq.eq_rhs.e_desc) with
  | (_, Eapp ({ a_op = Enode _; }, _, Some _)) -> assert false
  | (_, Eapp ({ a_op = Enode nn; }, argl, None)) ->
      let ck_assgn = Vi_assgn (mk_ck n, make_clock eq.eq_rhs.e_ck) in

      let mk_assgn e = match e.e_desc with
        | Evar vn -> Vi_assgn (mk_arg (name vn), mk_vare (name vn))
        | _ ->
            Printf.eprintf "Non-variable node argument\n";
            assert false in
      (n + 1, Vi_seq (ck_assgn :: List.map mk_assgn argl) :: is)
  | (Etuplepat _, _) ->
      Printf.eprintf "Non-normalized MiniLS equation\n";
      assert false
  | (Evarpat vn, Efby (co, e)) ->
      (*
        if hwrst = '1' then
          vn <- Trad(c);
        elsif guard_exp ck then
          vn <- Trad(e);
        end if;
      *)
      let (i_c, i_stm) =
        (guard_exp eq.eq_rhs.e_ck, Vi_assgn (Vl_var (name vn), trad_exp e)) in

      (n, (match co with
             | None -> Vi_if (i_c, i_stm, [], None)
             | Some c ->
                 Vi_if (Ve_bop ("=",
                                mk_vare (Idents.name hr_n),
                                one),
                        Vi_assgn (Vl_var (name vn), Ve_const c),
                        [(i_c, i_stm)], None)) :: is)
  | (Evarpat vn, _) -> (n, trad_cexpr eq.eq_rhs (Vl_var (name vn)) :: is)


(* env maps component names to arg lists *)
(* N.B. : a binding point between C1 and component C should appear AFTER
   the interface declaration for C: this is why we split declarations in
   pdecls and pbinds. *)
let gather_port_map env eq (n, pdecls, pbinds, pmaps) =
  match (eq.eq_lhs, eq.eq_rhs.e_desc) with
    | (pat, Eapp ({ a_op = Enode f; }, yl, None)) ->
        let inst_n = shortname f ^ string_of_int n in

        let (inp_s, out_s) = interface_signals_of_node (env f) in
        let sigs = inp_s @ out_s in

        let yl =
          let extr { e_desc = ed; } = match ed with
            | Evar vn -> name vn
            | _ -> assert false in
          List.map extr yl in
        let xl = List.rev (List.map name (Vars.vars_pat [] pat)) in

        let snames = List.map (fun s -> s.vs_name) sigs in

        let bindings =
          List.combine snames (mk_ck_s n :: name hr_n
                               :: List.map mk_arg_s yl @ xl) in

        (* FIXME: shortnames *)
        let new_pmap =
          Vdef_comp_inst (inst_n, shortname f, bindings) in

        let new_pdecl =
          let is_comp_decl d = match d with
            | Vd_component (f', _) -> f' = shortname f
            | _ -> false in
          if not (List.exists is_comp_decl pdecls)
          then [Vd_component (shortname f, sigs)] else [] in

        let new_bind = Vd_bind (inst_n, shortname f, { qual = "work";
                                                       id = shortname f; }) in

        (n + 1, new_pdecl @ pdecls, new_bind :: pbinds, new_pmap :: pmaps)

    | (_, _) -> (n, pdecls, pbinds, pmaps)


let extract_var_name e = match e.e_desc with
  | Evar vn -> vn
  | _ -> invalid_arg "extract_var_name: expected variable"

let is_combinatorial eq = match eq.eq_rhs.e_desc with
  | Efby _ | Eapp ({ a_op = Enode _; }, _, _) -> false
  | _ -> true

let defs_of eq =
  let rec mk_tyl ty tyl = match ty with
    | Tprod tyl -> List.fold_right mk_tyl tyl []
    | bty -> trans_ty bty :: tyl in

  let rec defs_pat p vl = match p with
    | Evarpat vn -> name vn :: vl
    | Etuplepat pl -> List.fold_right defs_pat pl vl in

  List.combine (defs_pat eq.eq_lhs []) (mk_tyl eq.eq_rhs.e_ty [])

let param_signals eq (n, sigs) = match eq.eq_rhs.e_desc with
  | Eapp ({ a_op = Enode f; }, yl, None) ->
      let add_sig y yl = match (y.e_ty, y.e_desc) with
        | (bty, Evar vn) ->
            (* TODO: more efficient *)
            if List.exists (fun (n, _) -> n = mk_arg_s (name vn)) sigs
            then yl else (mk_arg_s (name vn), trans_ty bty) :: yl
        | _ -> assert false (* call not simplified? *) in
      (n + 1, (mk_ck_s n, Vt_logic) :: List.fold_right add_sig yl [] @ sigs)
  | _ -> (n, sigs)

let trad_node env nd =
  let f = nd.n_name in

  let port =
    (* std_ulogic needed for rising_edge *)
    (* { vs_name = ck_n; vs_polarity = Some Vp_in; vs_type = Vt_ulogic; } *)
    native_signals
    @ List.map (signal_of_vardec Vp_in) nd.n_input
    @ List.map (fun o -> ren_o (signal_of_vardec Vp_out o)) nd.n_output in

  let signals =
    let not_comb eq = not (is_combinatorial eq) in
    List.concat (List.map defs_of (List.filter not_comb nd.n_equs)) in
  let (_, sig_args) = List.fold_right param_signals nd.n_equs (1, []) in

  let vars =
    List.concat (List.map defs_of (List.filter is_combinatorial nd.n_equs)) in

  let (_, pdecls, pbinds, ports) =
    List.fold_right (gather_port_map env) nd.n_equs (1, [], [], []) in

  let body =
    let mk_assg vd =
      Vi_assgn (mk_o (name vd.v_ident), mk_vare (name vd.v_ident)) in
    snd (List.fold_right trad_eq nd.n_equs (1, []))
    @ (List.map mk_assg nd.n_output) in

  let sens_l =
    let add_results resl eq = match eq.eq_rhs.e_desc with
      | Eapp ({ a_op = Enode _; }, _, _) ->
          List.map name (Vars.vars_pat [] eq.eq_lhs) @ resl
      | _ -> resl in
    let inputs = List.map (fun vd -> name vd.v_ident) nd.n_input in
    name ck_n :: name hr_n
    :: List.fold_left add_results inputs nd.n_equs in

  { vc_name = f;
    vc_entity = { ve_name = f;
                  ve_port = port;
                  ve_tydecls = []; }; (* TODO: ty decls *)
    vc_architecture =
      { va_name = "rtl";
        va_component = f;
        va_decls =
          (let mk_sig_decl (n, ty) = Vd_signal { vs_name = n;
                                                 vs_polarity = None;
                                                 vs_type = ty; } in
           List.map mk_sig_decl (signals @ sig_args) @ pdecls @ pbinds);
        va_body = Vdef_process { vp_name = Some "update";
                                 vp_sensitivity_list = sens_l;
                                 vp_vars = vars;
                                 vp_body = Vi_seq body; } :: ports; }; }

let mk_env prog n =
  try List.find (fun nd -> nd.n_name = shortname n) prog.p_nodes
  with Not_found ->
    Printf.eprintf "Could not find node %s\n" (shortname n);
    exit 1

(************)

let eqname eq = match eq.eq_lhs with
  | Evarpat vn -> vn
  | Etuplepat _ ->
      Printf.eprintf "VHDL: non-normalized equation found\n";
      assert false

let trans_opname opn = match opn with
  | Name id | Modname { qual = "Pervasives"; id = id; } -> id
  | Modname _ -> unimplemented ("operator " ^ fullname opn)

let trans_ty_dec tyd =
  let desc = match tyd.t_desc with
    | Type_enum nl -> Vty_enum nl
    | Type_struct nbtyl ->
        let mk_field { f_name = n; f_type = ty; } = (n, trans_ty ty) in
        Vty_record (List.map mk_field nbtyl)
    | Type_abs -> Vty_opaque in
  { vty_name = tyd.t_name;
    vty_desc = desc; }

(** [tb_node nd] generates a test-bench for node definition [nd]. [nd] should
    have no input parameters, only outputs. *)
let tb_node nd =
  (** Enforce the absence of input parameters. *)
  if (List.length nd.n_input > 1)
  then begin
    Printf.eprintf "VHDL: Cannot create a test-bench for node %s with inputs.\n"
      nd.n_name;
    exit 1;
  end;

  (** [tb_name] will be the name of our test-bench. *)
  let tb_name = bench_name nd.n_name in

  (** [ci_name] will be the name of our instantiated component. *)
  let ci_name = nd.n_name ^ "_0"

  (** [ent_name] is the name of our component/class to be tested. VHDL considers
      components in the current directory to be in a "work" module. *)
  and ent_name = { qual = "work"; id = nd.n_name; } in

  let (in_signals, out_signals) = interface_signals_of_node nd in

  (** Delay for clock cycle. *)
  let wait_i = Vi_wait_ns (period / 2) in

  (** We declare our component (correctly bound), and required signals. *)
  let decls =
    let sig_d s = Vd_signal { s with vs_polarity = None; } in
    Vd_component (nd.n_name, in_signals @ out_signals)
    :: Vd_bind (ci_name, nd.n_name, ent_name)
    :: List.map sig_d out_signals
    @ List.map sig_d base_signals in

  (** The test-bench initializes (reset) our component/class, and then
      indefinitely repeats clock cycles. *)
  let process_body =
    Vi_seq [Vi_assgn (Vl_var (name ck_n), zero);
            Vi_assgn (Vl_var (name hr_n), one);
            Vi_assgn (Vl_var (name rs_n), one);
            wait_i;
            Vi_assgn (Vl_var (name hr_n), zero);
            Vi_assgn (Vl_var (name rs_n), zero);
            wait_i;
            Vi_assgn (Vl_var (name ck_n), one);
            Vi_assgn (Vl_var (name hr_n), zero);
            wait_i;
            Vi_assgn (Vl_var (name ck_n), zero);
            wait_i;
            Vi_loop (Vi_seq [Vi_assgn (Vl_var (name ck_n), one);
                             wait_i;
                             Vi_assgn (Vl_var (name ck_n), zero);
                             wait_i])] in

  (** Correct instantiation for our component. *)
  let comp_inst =
    let mk_bind vd = (mk_o_s (name vd.v_ident), mk_o_s (name vd.v_ident)) in
    let bindl =
      (name ck_n, name ck_n)
      :: (name hr_n, name hr_n)
      :: (name rs_n, name rs_n)
      :: List.map mk_bind nd.n_output in
    Vdef_comp_inst (ci_name, nd.n_name, bindl) in

  { vc_name = tb_name;
    vc_entity = { ve_name = tb_name;
                  ve_port = [];
                  ve_tydecls = []; };
    vc_architecture = { va_name = "behav";
                        va_component = tb_name;
                        va_decls = decls;
                        va_body = [comp_inst;
                                   Vdef_process
                                     { vp_name = None;
                                       vp_sensitivity_list = [];
                                       vp_vars = [];
                                       vp_body = process_body; }] }; }

let package_of_types p =
  let tydl =
    [
      { vty_name = "integer_vector"; vty_desc = Vty_vector Vt_int; };
    ]
    @ List.map trans_ty_dec p.p_types in

  { vpack_name = "types";
    vpack_decls = List.map (fun tyd -> Vd_type tyd) tydl; }

let translate modn p =
  (* TODO: clean *)
  tys := p.p_types;
  modname := String.capitalize modn;
  if List.length p.p_opened > 0 then unimplemented "modules";
  let env = mk_env p in
  let res =
    Right (package_of_types p)
    :: List.map (fun nd -> Left (trad_node env nd)) p.p_nodes in
  (match !Misc.simulation_node with
     | None -> []
     | Some sn ->
         let nd_to_simulate =
           try List.find (fun nd -> nd.n_name = sn) p.p_nodes
           with Not_found ->
             Printf.eprintf "Unknown node to simulate: %s\n" sn;
             assert false in
         [Left (tb_node nd_to_simulate)]) @ res

open Compiler_utils

let program p =
  let filename = filename_of_name p.p_modname in
  let dirname = build_path (filename ^ "_vhdl") in
  let dir = clean_dir dirname in
  let vhdl_ast = translate (Filename.basename filename) p in
  Vhdl.print dir vhdl_ast
