(***********************************************************************)
(*                                                                     *)
(*                             Heptagon                                *)
(*                                                                     *)
(* Gwenael Delaval, LIG/INRIA, UJF                                     *)
(* Leonard Gerard, Parkas, ENS                                         *)
(* Adrien Guatto, Parkas, ENS                                          *)
(* Cedric Pasteur, Parkas, ENS                                         *)
(* Marc Pouzet, Parkas, ENS                                            *)
(*                                                                     *)
(* Copyright 2012 ENS, INRIA, UJF                                      *)
(*                                                                     *)
(* This file is part of the Heptagon compiler.                         *)
(*                                                                     *)
(* Heptagon is free software: you can redistribute it and/or modify it *)
(* under the terms of the GNU General Public License as published by   *)
(* the Free Software Foundation, either version 3 of the License, or   *)
(* (at your option) any later version.                                 *)
(*                                                                     *)
(* Heptagon is distributed in the hope that it will be useful,         *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of      *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the       *)
(* GNU General Public License for more details.                        *)
(*                                                                     *)
(* You should have received a copy of the GNU General Public License   *)
(* along with Heptagon.  If not, see <http://www.gnu.org/licenses/>    *)
(*                                                                     *)
(***********************************************************************)

(* Translation from Minils to Obc. *)
open Misc
open Containers
open Names
open Idents
open Signature
open Obc
open Obc_utils
open Obc_mapfold
open Types
open Clocks
open Initial
open Posixprep


let build_anon, find_anon =
  let anon_nodes = ref QualEnv.empty in
  let build_anon nodes =
    let build env nd = match nd with
      | Minils.Pnode nd ->
          if Itfusion.is_anon_node nd.Minils.n_name
          then QualEnv.add nd.Minils.n_name nd env
          else env
      | _ -> env
    in
    anon_nodes := List.fold_left build QualEnv.empty nodes
  in
  let find_anon qn = QualEnv.find qn !anon_nodes in
  build_anon, find_anon

let var_from_name map x =
  begin try
    Env.find x map
  with
      _ ->
        Format.eprintf
          "Internal compiler error: unknown identifier %a@."
          Global_printer.print_ident x;
        assert false
  end

let ext_value_exp_from_name map x = exp_of_pattern (var_from_name map x)

(* let lvar_from_name map ty x = mk_pattern ty (Lvar (var_from_name map x)) *)

let fresh_it () =
  let id = Idents.gen_var "mls2obc" "i" in
  id, mk_var_dec id Initial.tint

let clo_id = ref 0
let get_unique_clo_id () =
  let id = !clo_id in
  clo_id := !clo_id +1;
  id

let mKernelCall = ref Mls_utils.EqMap.empty
let get_kernel_call_id eq =
  try
    Mls_utils.EqMap.find eq !mKernelCall
  with Not_found ->
    let id = get_unique_clo_id () in
    mKernelCall := Mls_utils.EqMap.add eq id !mKernelCall;
    id


let gen_obj_ident n = Idents.gen_var "mls2obc" ((shortname n) ^ "_inst")
let fresh_for = fresh_for "mls2obc"
(*let copy_array = copy_array "mls2obc"*)

let op_from_string op = { qual = Pervasives; name = op; }

let pattern_of_idx_list p l =
  let rec aux p l = match Modules.unalias_type p.pat_ty, l with
    | _, [] -> p
    | Tarray (ty',_), idx :: l -> aux (mk_pattern ty' (Larray (p, idx))) l
    | _ -> internal_error "mls2obc"
  in
  aux p l

let rec exp_of_idx_list e l = match Modules.unalias_type e.w_ty, l with
  | _, [] -> e
  | Tarray (ty',_), idx :: l ->
    exp_of_idx_list (mk_ext_value ty' (Warray (e, idx))) l
  | _ -> internal_error "mls2obc exp_of_idx_list"

let rec extvalue_of_idx_list w l = match Modules.unalias_type w.w_ty, l with
  | _, [] -> w
  | Tarray (ty',_), idx :: l ->
    extvalue_of_idx_list (mk_ext_value ty' (Warray (w, idx))) l
  | _ -> internal_error "mls2obc extvalue_of_idx_list"

let ext_value_of_trunc_idx_list p l =
  let mk_between idx se =
    mk_exp_int (Eop (mk_pervasives "between", [idx; mk_ext_value_exp se.se_ty (Wconst se)]))
  in
  let rec aux p l = match Modules.unalias_type p.w_ty, l with
    | _, [] -> p
    | Tarray (ty', se), idx :: l -> aux (mk_ext_value ty' (Warray (p, mk_between idx se))) l
    | _ -> internal_error "mls2obc ext_value_of_trunc_idx_list"
  in
  aux p l

let rec ty_of_idx_list ty idx_list = match ty, idx_list with
  | _, [] -> ty
  | Tarray(ty, _), _idx::idx_list -> ty_of_idx_list ty idx_list
  | _, _ -> internal_error "mls2obc ty_of_idx_list"

let mk_static_array_power ty c params = match params with
  | [] -> mk_ext_value_exp ty (Wconst c)
  | _ ->
    let se = mk_static_exp ty (Sarray_power (c, params)) in
    mk_ext_value_exp ty (Wconst se)

let array_elt_of_exp idx e =
  match e.e_desc, Modules.unalias_type e.e_ty with
  | Eextvalue { w_desc = Wconst { se_desc = Sarray_power (c, _::new_params) }; }, Tarray (ty,_) ->
     mk_static_array_power ty c new_params
  | _, Tarray (ty,_) ->
      mk_ext_value_exp ty (Warray(ext_value_of_exp e, idx))
  | _ -> internal_error "mls2obc array_elt_of_exp"

let array_elt_of_exp_list idx_list e =
  match e.e_desc, Modules.unalias_type e.e_ty with
    | Eextvalue { w_desc = Wconst { se_desc = Sarray_power (c, params) } }, Tarray (ty,n) ->
      let new_params, _ = Misc.split_at (List.length params - List.length idx_list) params in
      let ty = ty_of_idx_list (Tarray(ty,n)) idx_list in
      mk_static_array_power ty c new_params
    | _ , t ->
        let rec ty id_l t = match id_l, Modules.unalias_type t with
          | [] , t -> t
          | _::id_l , Tarray (t,_) -> ty id_l t
          | _, _ -> internal_error "mls2obc ty"
        in
        mk_exp (ty idx_list t) (Eextvalue (extvalue_of_idx_list (ext_value_of_exp e) idx_list))


(** Creates the expression that checks that the indices
    in idx_list are in the bounds. If idx_list=[e1;..;ep]
    and bounds = [n1;..;np], it returns
    0<= e1 < n1 && .. && 0 <= ep < np *)
let rec bound_check_expr idx_list bounds =
  let mk_comp idx n =
        let e1 = mk_exp_bool (Eop (op_from_string "<",
                                 [idx; mk_ext_value_exp_int (Wconst n)])) in
        let e2 = mk_exp_bool (Eop (op_from_string "<=",
                                 [mk_ext_value_exp_int (Wconst (mk_static_int 0)); idx])) in
          mk_exp_bool (Eop (op_from_string "&", [e1;e2]))
  in
  match (idx_list, bounds) with
    | [idx], n::_ -> mk_comp idx n
    | (idx :: idx_list, n :: bounds) ->
        let e = mk_comp idx n in
          mk_exp_bool (Eop (op_from_string "&",
                           [e; bound_check_expr idx_list bounds]))
    | (_, _) -> internal_error "mls2obc"

let mk_plus_one e = match e.e_desc with
  | Eextvalue ({ w_desc = Wconst idx } as w) ->
      let idx_plus_one = mk_static_int_op (mk_pervasives "+") [idx; mk_static_int 1] in
        { e with e_desc = Eextvalue { w with w_desc = Wconst idx_plus_one; }; }
  | _ ->
      let idx_plus_one = Eop (mk_pervasives "+", [e; mk_exp_const_int 1]) in
        { e with e_desc = idx_plus_one }

(** Creates the action list that copies [src] to [dest],
    updating the value at index [idx_list] with the value [v]. *)
let rec ssa_update_array dest src idx_list v = match Modules.unalias_type dest.pat_ty, idx_list with
  | Tarray (t, n), idx::idx_list ->
      (*Body of the copy loops*)
      let copy i =
        let src_i = array_elt_of_exp i src in
        let dest_i = mk_pattern t (Larray (dest, i)) in
        [Aassgn(dest_i, src_i)]
      in
      (*Copy values < idx*)
      let a_lower = fresh_for (mk_exp_const_int 0) idx copy in
      (* Update the correct element*)
      let src_idx = array_elt_of_exp idx src in
      let dest_idx = mk_pattern t (Larray (dest, idx)) in
      let a_update = ssa_update_array dest_idx src_idx idx_list v in
      (*Copy values > idx*)
      let idx_plus_one = mk_plus_one idx in
      let a_upper = fresh_for idx_plus_one (mk_exp_static_int n) copy in
      [a_lower] @ a_update @ [a_upper]
  | _, _ ->
      [Aassgn(dest, v)]

(** Creates the action list that copies [src] to [dest],
    updating the value of field [f] with the value [v]. *)
let ssa_update_record dest src f v =
  let assgn_act { f_name = l; f_type = ty } =
    let dest_l = mk_pattern ty (Lfield(dest, l)) in
    let src_l = mk_ext_value_exp ty (Wfield(src, l)) in
    if f = l then
      Aassgn(dest_l, v)
    else
      Aassgn(dest_l, src_l)
  in
  let fields = match dest.pat_ty with
    | Tid n -> Modules.find_struct n
    | _ -> Misc.internal_error "mls2obc field of nonstruct"
  in
  List.map assgn_act fields

let rec control map ck s = match ck with
  | Clocks.Cbase | Cvar { contents = Cindex _ } -> s
  | Cvar { contents = Clink ck } -> control map ck s
  | Clocks.Con(ck, c, n)  ->
    let x = ext_value_exp_from_name map n in
    control map ck (Acase(x, [(c, mk_block [s])]))

let reinit o =
  Acall ([], o, Mreset, [])

let rec translate_pat map ty pat = match pat, ty with
  | Minils.Evarpat x, _ -> [ var_from_name map x ]
  | Minils.Etuplepat pat_list, Tprod ty_l  ->
      List.fold_right2 (fun ty pat acc -> (translate_pat map ty pat) @ acc)
        ty_l pat_list []
  | Minils.Etuplepat _, _ -> Misc.internal_error "Ill-typed pattern"

let translate_var_dec l =
  let one_var { Minils.v_ident = x; Minils.v_type = t; Minils.v_linearity = lin; v_loc = loc } =
    mk_var_dec ~loc:loc ~linearity:lin x t
  in
  List.map one_var l

let rec translate_extvalue map w = match w.Minils.w_desc with
  | Minils.Wvar x -> ext_value_of_pattern (var_from_name map x)
  | _ ->
    let desc = match w.Minils.w_desc with
      | Minils.Wconst v -> Wconst v
      | Minils.Wvar _ -> assert false
      | Minils.Wfield (w1, f) -> Wfield (translate_extvalue map w1, f)
      | Minils.Wwhen (w1, _, _) | Minils.Wreinit(_, w1)  -> (translate_extvalue map w1).w_desc
    in
    mk_ext_value w.Minils.w_ty desc

and translate_extvalue_to_exp map w =
  mk_exp ~loc:w.Minils.w_loc w.Minils.w_ty (Eextvalue (translate_extvalue map w))

(* [translate e = c] *)
let rec translate map e =
  let desc = match e.Minils.e_desc with
    | Minils.Eextvalue w ->
        let w = translate_extvalue map w in Eextvalue w
    | Minils.Eapp ({ Minils.a_op = Minils.Eequal }, w_list, _) ->
      Eop (op_from_string "=", List.map (translate_extvalue_to_exp map) w_list)
    | Minils.Eapp ({ Minils.a_op = Minils.Efun n }, e_list, _)
        when Mls_utils.is_op n ->
        Eop (n, List.map (translate_extvalue_to_exp map ) e_list)
    | Minils.Estruct f_e_list ->
        let type_name = (match e.Minils.e_ty with
                           | Tid name -> name
                           | _ -> assert false) in
        let f_e_list = List.map
          (fun (f, e) -> (f, (translate_extvalue_to_exp map e))) f_e_list in
          Estruct (type_name, f_e_list)
  (*Remaining array operators*)
    | Minils.Eapp ({ Minils.a_op = Minils.Earray }, e_list, _) ->
        Earray (List.map (translate_extvalue_to_exp map ) e_list)
    | Minils.Eapp ({ Minils.a_op = Minils.Eselect;
                     Minils.a_params = idx_list }, e_list, _) ->
        let e = translate_extvalue map (assert_1 e_list) in
        let idx_list = List.map mk_exp_static_int idx_list in
        Eextvalue (extvalue_of_idx_list e idx_list)
    | Minils.Ewhen(e,_,_) ->
        let e = translate map e in
        e.e_desc
  (* Already treated cases when translating the [eq] *)
    | Minils.Eiterator _ | Minils.Emerge _ | Minils.Efby _
    | Minils.Eapp ({Minils.a_op=(Minils.Enode _|Minils.Efun _|Minils.Econcat
                                |Minils.Eupdate|Minils.Eselect_dyn
                                |Minils.Eselect_trunc|Minils.Eselect_slice
                                |Minils.Earray_fill|Minils.Efield_update
                                |Minils.Eifthenelse)}, _, _) ->
        internal_error "mls2obc"
  in
    mk_exp e.Minils.e_ty desc

and translate_act_extvalue map pat w =
  match pat with
    | Minils.Evarpat n ->
        [Aassgn (var_from_name map n, translate_extvalue_to_exp map w)]
    | _ -> assert false

(* [translate pat act = si, d] *)
and translate_act map pat
    ({ Minils.e_desc = desc } as act) =
    match pat, desc with
   (* When Merge *)
    | pat, Minils.Ewhen (e,_,_) -> translate_act map pat e
    | Minils.Evarpat x, Minils.Emerge (y, c_act_list) ->
        let x = var_from_name map x in
        let translate_c_extvalue (c, w) =
          c, mk_block [Aassgn (x, translate_extvalue_to_exp map w)]
        in

        [Acase (ext_value_exp_from_name map y,
                List.map translate_c_extvalue c_act_list)]
   (* Array ops *)
    | Minils.Evarpat x,
        Minils.Eapp ({ Minils.a_op = Minils.Econcat }, [e1; e2], _) ->
        let cpt1, cpt1d = fresh_it () in
        let cpt2, cpt2d = fresh_it () in
        let x = var_from_name map x in
        let _t = x.pat_ty in
        (match e1.Minils.w_ty, e2.Minils.w_ty with
           | Tarray (t1, n1), Tarray (t2, n2) ->
               let e1 = translate_extvalue_to_exp map e1 in
               let e2 = translate_extvalue_to_exp map e2 in
               let a1 =
                 Afor (cpt1d, mk_exp_const_int 0, mk_exp_static_int n1,
                      mk_block [Aassgn (mk_pattern t1 (Larray (x, mk_evar_int cpt1)),
                                       array_elt_of_exp (mk_evar_int cpt1) e1)] ) in
               let idx = mk_exp_int (Eop (op_from_string "+",
                                         [ mk_exp_static_int n1; mk_evar_int cpt2])) in
               let p2 = array_elt_of_exp (mk_evar_int cpt2) e2 in
               let a2 = Afor (cpt2d, mk_exp_const_int 0, mk_exp_static_int n2,
                             mk_block [Aassgn (mk_pattern t2 (Larray (x, idx)), p2)] )
               in
               [a1; a2]
           | _ -> assert false)

    | Minils.Evarpat x,
          Minils.Eapp ({ Minils.a_op = Minils.Earray_fill; Minils.a_params = n_list }, [e], _) ->
        let e = translate_extvalue_to_exp map e in
        let x = var_from_name map x in
        let t = match x.pat_ty with
          | Tarray (t,_) -> t
          | _ -> Misc.internal_error "mls2obc select slice type"
        in

        let rec make_loop power_list replace = match power_list with
          | [] -> x, replace
          | p :: power_list ->
            let cpt, cptd = fresh_it () in
            let e, replace =
              make_loop power_list
                        (fun y -> [Afor (cptd, mk_exp_const_int 0,
                                         mk_exp_static_int p, mk_block (replace y))]) in
            let e = Larray (e, mk_evar_int cpt) in
            (mk_pattern t e, replace)
        in
        let e, b = make_loop n_list (fun y -> [Aassgn (y, e)]) in
        b e

    | Minils.Evarpat x,
            Minils.Eapp ({ Minils.a_op = Minils.Eselect_slice;
                           Minils.a_params = [idx1; idx2] }, [e], _) ->
        let cpt, cptd = fresh_it () in
        let e = translate_extvalue_to_exp map e in
        let x = var_from_name map x in
        let t = match x.pat_ty with
          | Tarray (t,_) -> t
          | _ -> Misc.internal_error "mls2obc select slice type"
        in
        let idx = mk_exp_int (Eop (op_from_string "+",
                                  [mk_evar_int cpt; mk_exp_static_int idx1 ])) in
        (* bound = (idx2 - idx1) + 1*)
        let bound = mk_static_int_op (op_from_string "+")
          [ mk_static_int 1; mk_static_int_op (op_from_string "-") [idx2;idx1] ] in
         [ Afor (cptd, mk_exp_const_int 0, mk_exp_static_int bound,
                mk_block [Aassgn (mk_pattern t (Larray (x, mk_evar_int cpt)),
                                  array_elt_of_exp idx e)] ) ]

    | Minils.Evarpat x, Minils.Eapp ({ Minils.a_op = Minils.Eselect_dyn }, e1::e2::idx, _) ->
        let x = var_from_name map x in
        let bounds = Mls_utils.bounds_list e1.Minils.w_ty in
        let e1 = translate_extvalue map e1 in
        let idx = List.map (translate_extvalue_to_exp map) idx in
        let w = extvalue_of_idx_list e1 idx in
        let true_act = Aassgn (x, mk_exp w.w_ty (Eextvalue w)) in
        let false_act = Aassgn (x, translate_extvalue_to_exp map e2) in
        let cond = bound_check_expr idx bounds in
          [ mk_ifthenelse cond [true_act] [false_act] ]

    | Minils.Evarpat x, Minils.Eapp ({ Minils.a_op = Minils.Eselect_trunc }, e1::idx, _) ->
        let x = var_from_name map x in
        let _bounds = Mls_utils.bounds_list e1.Minils.w_ty in
        let e1 = translate_extvalue map e1 in
        let idx = List.map (translate_extvalue_to_exp map) idx in
        let w = ext_value_of_trunc_idx_list e1 idx in
        [Aassgn (x, mk_exp w.w_ty (Eextvalue w))]

    | Minils.Evarpat x, Minils.Eapp ({ Minils.a_op = Minils.Eupdate }, e1::e2::idx, _) ->
        let x = var_from_name map x in
        let bounds = Mls_utils.bounds_list e1.Minils.w_ty in
        let idx = List.map (translate_extvalue_to_exp map) idx in
        let e1 = translate_extvalue_to_exp map e1 in
        let e2 = translate_extvalue_to_exp map e2 in
        let cond = bound_check_expr idx bounds in
        let copy = Aassgn (x, e1) in
        if !Compiler_options.strict_ssa
        then (
          let ssa_up = ssa_update_array x e1 idx e2 in
          [ mk_ifthenelse cond ssa_up [copy] ]
        ) else (
          let assgn = Aassgn (pattern_of_idx_list x idx, e2) in
          [copy; mk_if cond [assgn]]
        )

    | Minils.Evarpat x,
      Minils.Eapp ({ Minils.a_op = Minils.Efield_update;
                     Minils.a_params = [{ se_desc = Sfield f }] }, [e1; e2], _) ->
        let x = var_from_name map x in
        let e1' = translate_extvalue map e1 in
        let e2 = translate_extvalue_to_exp map e2 in
        if !Compiler_options.strict_ssa
        then ssa_update_record x e1' f e2
        else (
          let copy = Aassgn (x, translate_extvalue_to_exp map e1) in
          let action = Aassgn (mk_pattern (Types.Tid (Modules.find_field f)) (Lfield (x, f)), e2) in
          [copy; action]
        )
    | Minils.Evarpat n, _ ->
        [Aassgn (var_from_name map n, translate map act)]
    | _ ->
      Format.eprintf "%a The pattern %a should be a simple var to be translated to obc.@."
        Location.print_location act.Minils.e_loc Mls_printer.print_pat pat;
      assert false

(** In an iteration, objects used are element of object arrays *)
type obj_array = { oa_index : Obc.pattern list; oa_size : static_exp list }

(** A [None] context is normal, otherwise, we are in an iteration *)
type call_context = obj_array option

let mk_obj_call_from_context c n = match c with
  | None -> Oobj n
  | Some oa -> Oarray (n, oa.oa_index)

let size_from_call_context c = match c with
  | None -> None
  | Some oa -> Some (oa.oa_size)

let empty_call_context = None

(** [si] the initialization actions used in the reset method,
    [j] obj decs
    [s] the actions used in the step method.
    [v] var decs *)
let rec translate_eq map call_context odevid
  ({ Minils.eq_lhs = pat; Minils.eq_base_ck = ck; Minils.eq_rhs = e } as eq)
  (v, si, j, s) =
  let { Minils.e_desc = desc; Minils.e_loc = loc } = e in
  match (pat, desc) with
    | _pat, Minils.Ewhen (e,_,_) -> (
        assert(odevid==None);
        translate_eq map call_context None {eq with Minils.eq_rhs = e} (v, si, j, s)
    (* TODO Efby and Eifthenelse should be dealt with in translate_act, no ? *)
    )
    | Minils.Evarpat n, Minils.Efby (opt_c, e) ->
        let x = var_from_name map n in
        let si = (match opt_c with
                    | None -> si
                    | Some c -> (Aassgn (x, mk_ext_value_exp_static x.pat_ty c)) :: si) in
        let action = Aassgn (var_from_name map n, translate_extvalue_to_exp map e) in
        v, si, j, (control map ck action) :: s
    (* should be unnecessary
    | Minils.Etuplepat p_list,
        Minils.Eapp({ Minils.a_op = Minils.Etuple }, act_list, _) ->
        List.fold_right2
          (fun pat e ->
             translate_eq map call_context
               (Minils.mk_equation pat e))
          p_list act_list (v, si, j, s)
    *)
    | pat, Minils.Eapp({ Minils.a_op = Minils.Eifthenelse }, [e1;e2;e3], _) ->
        let cond = translate_extvalue_to_exp map e1 in
        let true_act = translate_act_extvalue map pat e2 in
        let false_act = translate_act_extvalue map pat e3 in
        let action = mk_ifthenelse cond true_act false_act in
        v, si, j, (control map ck action) :: s

    | _pat, Minils.Eapp({ Minils.a_op =
        Minils.Efun ({ qual = Module "Iostream"; name = "printf" | "fprintf" } as q)},
                       args, _) ->
      let action = Aop (q, List.map (translate_extvalue_to_exp map) args) in
      v, si, j, (control map ck action) :: s

    | pat, Minils.Eapp ({ Minils.a_op = Minils.Efun _ | Minils.Enode _ } as app, e_list, r) ->
        let name_list = translate_pat map e.Minils.e_ty pat in
        let c_list = List.map (translate_extvalue_to_exp map) e_list in
        let v', si', j', action = mk_node_call map call_context
          app loc name_list c_list e.Minils.e_ty odevid in
        let action = List.map (control map ck) action in
        let s = (match r, app.Minils.a_op with
                   | Some r, Minils.Enode _ ->
                       let ck = Clocks.Con (ck, Initial.ptrue, r) in
                       let ra = List.map (control map ck) si' in
                       ra @ action @ s
                   | _, _ -> action @ s) in
        v' @ v, si'@si, j'@j, s

    | pat, Minils.Eiterator (it, app, n_list, pe_list, e_list, reset) ->
        let name_list = translate_pat map e.Minils.e_ty pat in
        let p_list = List.map (translate_extvalue_to_exp map) pe_list in
        let c_list = List.map (translate_extvalue_to_exp map) e_list in
        let xl, xdl = List.split (List.map (fun _ -> fresh_it ()) n_list) in
        let call_context =
          Some { oa_index = List.map (fun x -> mk_pattern_int (Lvar x)) xl;
                 oa_size = n_list} in
        let n_list = List.map mk_exp_static_int n_list in
        let si', j', action = translate_iterator map call_context it
          name_list app loc n_list xl xdl p_list c_list e.Minils.e_ty in
        let action = List.map (control map ck) action in
        let s =
          (match reset, app.Minils.a_op with
             | Some r, Minils.Enode _ ->
                 let ck = Clocks.Con (ck, Initial.ptrue, r) in
                 let ra = List.map (control map ck) si' in
                   ra @ action @ s
             | _, _ -> action @ s)
        in (v, si' @ si, j' @ j, s)

    | (pat, _) ->
        let action = translate_act map pat e in
        let action = List.map (control map ck) action in
          v, si, j, action @ s

and translate_eq_list map call_context act_list =
  List.fold_right (translate_eq map call_context None) act_list ([], [], [], [])

and mk_node_call map call_context app loc (name_list : Obc.pattern list) args ty odevid =
  match app.Minils.a_op with
    | Minils.Efun f when Mls_utils.is_op f ->
        let act = match name_list with
          | [] -> Aop (f, args)
          | [name] ->
              let e = mk_exp ty (Eop(f, args)) in
              Aassgn (name, e)
          | _ ->
            Misc.unsupported "mls2obc: external function with multiple return values" in
        [], [], [], [act]

    | Minils.Enode f when Itfusion.is_anon_node f ->
        let add_input env vd =
          Env.add vd.Minils.v_ident
            (mk_pattern vd.Minils.v_type (Lvar vd.Minils.v_ident)) env in
        let build env vd a = Env.add vd.Minils.v_ident a env in
        let subst_act_list env act_list =
          let exp funs env e = match e.e_desc with
            | Eextvalue { w_desc = Wvar x } ->
                let e =
                  (try Env.find x env
                  with Not_found -> e) in
                  e, env
            | _ -> Obc_mapfold.exp funs env e
          in
          let funs = { Obc_mapfold.defaults with exp = exp } in
          let act_list, _ = mapfold (Obc_mapfold.act_it funs) env act_list in
            act_list
        in

        let nd = find_anon f in
        let map = List.fold_left add_input map nd.Minils.n_input in
        let map = List.fold_left2 build map nd.Minils.n_output name_list in
        let map = List.fold_left add_input map nd.Minils.n_local in
        let v, si, j, s = translate_eq_list map call_context nd.Minils.n_equs in
        let env = List.fold_left2 build Env.empty nd.Minils.n_input args in
          v @ nd.Minils.n_local, si, j, subst_act_list env s

    | Minils.Enode f | Minils.Efun f ->
        let id = match app.Minils.a_id with
          | None -> gen_obj_ident f
          | Some id -> id
        in
        let o = mk_obj_call_from_context call_context id in
        let obj =
          { o_ident = obj_ref_name o; o_class = f;
            o_params = app.Minils.a_params;
            o_size = size_from_call_context call_context; o_loc = loc } in
        let si = match app.Minils.a_op with
          | Minils.Efun _ -> []
          | Minils.Enode _ -> [reinit o]
          | _ -> assert false
        in

        (* If the funcall is a kernel, match it as an OpenCL kernel *)
        let (lobj, s) = if (Modules.check_kernel f) then
          (match app.Minils.a_cloption with
            | None ->
              Misc.unsupported "mls2obc: OpenCL kernel call with no cl option associated"
            | Some clo ->
              let (devid, id_clo, blaunch, brecover) = match odevid with
                | None ->
                  let kercallid = get_unique_clo_id () in
                  ("Default", kercallid, true, true)  (* Kernel launch outside of a parsched *)
                | Some (devid, kercallid, blaunch) ->
                (devid, kercallid, blaunch, not blaunch)
              in
              let nclo_launch = {
                Obc.copt_gl_worksize = clo.Minils.copt_gl_worksize;
                Obc.copt_loc_worksize = clo.Minils.copt_loc_worksize;
                Obc.copt_is_launch = true;
                Obc.copt_device_id = devid;
                Obc.copt_id = id_clo}
              in
              let nclo_recover = {
                Obc.copt_gl_worksize = clo.Minils.copt_gl_worksize;
                Obc.copt_loc_worksize = clo.Minils.copt_loc_worksize;
                Obc.copt_is_launch = false;
                Obc.copt_device_id = devid;
                Obc.copt_id = id_clo}
              in
              let lres = if blaunch then 
                  [Acall (name_list, o, Mkernel nclo_launch, args)]      (* Launch offload  *)
                else
                  []
              in
              let lres = if brecover then
                  lres @ [Acall (name_list, o, Mkernel nclo_recover, args)] (* Recover offload *)
                else
                  lres
              in

              (* To avoid duplicating the object if it is a offload recover *)
              let lobj = if brecover then [] else [obj] in
              (lobj, lres)
            )
          else
            ([obj], [Acall (name_list, o, Mstep, args)])
        in

        [], si, lobj, s
    | _ -> assert false

and translate_iterator map call_context it name_list app loc n_list xl xdl p_list c_list ty =
  let rec unarray n ty = match ty, n with
    | Tarray (t,_), 1 -> t
    | Tarray (t,_), n -> unarray (n-1) t
    | _ ->
        Format.eprintf "%a" Global_printer.print_type ty;
        internal_error "mls2obc"
  in
  let unarray = unarray (List.length n_list) in
  let array_of_output name_list ty_list =
    let rec aux l ty xl = match ty, xl with
      | _, [] -> l
      | Tarray(tyn, _), x :: xl -> aux (mk_pattern ~loc:loc tyn (Larray(l, mk_evar_int x))) tyn xl
      | _, _ -> assert false
    in
    List.map2 (fun l ty -> aux l ty xl) name_list ty_list
  in
  let array_of_input c_list =
    List.map (array_elt_of_exp_list (List.map mk_evar_int xl)) c_list
  in
  let mk_loop b xdl nl =
    let rec mk_loop b xdl nl = match xdl, nl with
      | xd::[], n::[] -> Afor (xd, mk_exp_const_int 0, n, b)
      | xd::xdl, n::nl -> mk_loop (mk_block [Afor (xd, mk_exp_const_int 0, n, b)]) xdl nl
      | _, _ -> assert false
    in
    mk_loop b (List.rev xdl) nl
  in
  match it with
    | Minils.Imap ->
        let c_list = array_of_input c_list in
        let ty_list = List.map unarray (Types.unprod ty) in
        let name_list = array_of_output name_list (Types.unprod ty) in
        let node_out_ty = Types.prod ty_list in
        let v, si, j, action = mk_node_call map call_context
          app loc name_list (p_list@c_list) node_out_ty None in
        let v = translate_var_dec v in
        let b = mk_block ~locals:v action in
        let bi = mk_block si in
          [mk_loop bi xdl n_list], j, [mk_loop b xdl n_list]

    | Minils.Imapi ->
        let c_list = array_of_input c_list in
        let ty_list = List.map unarray (Types.unprod ty) in
        let name_list = array_of_output name_list (Types.unprod ty) in
        let node_out_ty = Types.prod ty_list in
        let v, si, j, action = mk_node_call map call_context
          app loc name_list (p_list@c_list@(List.map mk_evar_int xl)) node_out_ty None in
        let v = translate_var_dec v in
        let b = mk_block ~locals:v action in
        let bi = mk_block si in
          [mk_loop bi xdl n_list], j, [mk_loop b xdl n_list]

    | Minils.Imapfold ->
        let (c_list, acc_in) = split_last c_list in
        let c_list = array_of_input c_list in
        let ty_list = Types.unprod ty in
        let ty_name_list, _ = Misc.split_last ty_list in
        let (name_list, acc_out) = Misc.split_last name_list in
        let name_list = array_of_output name_list ty_name_list in
        let node_out_ty = Types.prod (Misc.map_butlast unarray ty_list) in
        let v, si, j, action = mk_node_call map call_context app loc
          (name_list @ [ acc_out ])
          (p_list @ c_list @ [ exp_of_pattern acc_out ])
          node_out_ty None
        in
        let v = translate_var_dec v in
        let b = mk_block ~locals:v action in
        let bi = mk_block si in
          [mk_loop bi xdl n_list], j,
           [Aassgn (acc_out, acc_in); mk_loop b xdl n_list]

    | Minils.Ifold ->
        let (c_list, acc_in) = split_last c_list in
        let c_list = array_of_input c_list in
        let acc_out = last_element name_list in
        let v, si, j, action =
          mk_node_call map call_context app loc name_list
            (p_list @ c_list @ [ exp_of_pattern acc_out ]) ty None
        in
        let v = translate_var_dec v in
        let b = mk_block ~locals:v action in
        let bi = mk_block si in
          [mk_loop bi xdl n_list], j,
           [ Aassgn (acc_out, acc_in); mk_loop b xdl n_list]

    | Minils.Ifoldi ->
        let (c_list, acc_in) = split_last c_list in
        let c_list = array_of_input c_list in
        let acc_out = last_element name_list in
        let v, si, j, action = mk_node_call map call_context app loc name_list
          (p_list @ c_list @ (List.map mk_evar_int xl) @ [ exp_of_pattern acc_out ]) ty None
        in
        let v = translate_var_dec v in
        let b = mk_block ~locals:v action in
        let bi = mk_block si in
          [mk_loop bi xdl n_list], j,
           [ Aassgn (acc_out, acc_in); mk_loop b xdl n_list]

(* ---------------------------- *)
let build_signal_act mSynchVar sig_name =
  let (condvar, _, countvar, _) = try
      StringMap.find sig_name mSynchVar
    with Not_found ->
      failwith ("mls2obc::build_signal_act : synchro " ^ sig_name ^ "was not found in mSynchVar.")
  in

  (* Pattern: decrease_count_condvar(&cond_var, &count_var); *)
  let qderef_op = { qual = Pervasives; name = "&" } in
  let cond_var_eval = mk_ext_value ty_pthread_condvar (Wmem condvar) in
  let cond_var = mk_exp ty_pthread_condvar (Eextvalue cond_var_eval) in
  let cond_var_ref = mk_exp ty_pthread_condvar (Eop (qderef_op, [cond_var])) in
  
  let count_var_eval = mk_ext_value_int (Wmem countvar) in
  let count_var = mk_exp Initial.tint (Eextvalue count_var_eval) in
  let count_var_ref =  mk_exp Initial.tint (Eop (qderef_op, [count_var])) in

  let (largs : exp list) = cond_var_ref :: count_var_ref :: [] in
  let sig_act = Aop (Posixprep.signal_fun_call_qname, largs) in
  sig_act

let build_wait_act mSynchVar sig_name =
  let (condvar, mutvar, countvar, _) = try
      StringMap.find sig_name mSynchVar
    with Not_found ->
      failwith ("mls2obc::build_wait_act : synchro " ^ sig_name ^ "was not found in mSynchVar.")
  in

  (* Pattern: wait_count_condvar(count_var, &cond_var, &mut_var); *)
  let count_var_eval = mk_ext_value_int (Wmem countvar) in
  let count_var_exp = mk_exp Initial.tint (Eextvalue count_var_eval) in

  let qderef_op = { qual = Pervasives; name = "&" } in
  let cond_var_eval = mk_ext_value ty_pthread_condvar (Wmem condvar) in
  let cond_var = mk_exp ty_pthread_condvar (Eextvalue cond_var_eval) in
  let cond_var_ref = mk_exp ty_pthread_condvar (Eop (qderef_op, [cond_var])) in

  let mut_var_eval = mk_ext_value ty_pthread_mutvar (Wmem mutvar) in
  let mut_var = mk_exp ty_pthread_mutvar (Eextvalue mut_var_eval) in
  let mut_var_ref = mk_exp ty_pthread_mutvar (Eop (qderef_op, [mut_var])) in

  let (largs : exp list) = count_var_exp :: cond_var_ref :: mut_var_ref :: [] in
  let wait_act = Aop (Posixprep.wait_fun_call_qname, largs) in
  wait_act

let rec translate_parsched_comp map call_context mSynchVar parsched_comp (v, si, j, s) =
  match parsched_comp with
  | Minils.Comp_eq eq ->
    translate_eq map call_context None eq (v, si, j, s)
  | Minils.Comp_ocl_launch (eq, device_name) ->
    let kernel_call_id = get_kernel_call_id eq in
    translate_eq map call_context (Some (device_name, kernel_call_id, true)) eq (v, si, j, s)
  | Minils.Comp_ocl_recover (eq, device_name) ->
    let kernel_call_id = get_kernel_call_id eq in
    translate_eq map call_context (Some (device_name, kernel_call_id, false)) eq (v, si, j, s)
  | Minils.Comp_signal sig_name ->
    let act_signal = build_signal_act mSynchVar sig_name in
    (v, si, j, [act_signal] @ s)
  | Minils.Comp_wait (sig_name, _) ->
    let act_wait = build_wait_act mSynchVar sig_name in
    (v, si, j, [act_wait] @ s)

and translate_parsched_comp_list map call_context mSynchVar lparsched_comp =
  List.fold_right (translate_parsched_comp map call_context mSynchVar) lparsched_comp ([], [], [], [])

(* ---------------------------- *)

let remove m d_list =
  List.filter (fun { Minils.v_ident = n } -> not (List.mem_assoc n m)) d_list

let translate_contract map mem_var_tys =
  function
    | None -> ([], [], [], [], [])
    | Some
        {
          Minils.c_eq = eq_list;
          Minils.c_local = d_list;
        } ->
        let (v, si, j, s_list) = translate_eq_list map empty_call_context eq_list in
        let d_list = translate_var_dec (v @ d_list) in
        let m, d_list = List.partition
          (fun vd -> List.exists (fun (i,_) -> i = vd.v_ident) mem_var_tys) d_list in
         (m, si, j, s_list, d_list)

(** Returns a map, mapping variables names to the variables
    where they will be stored. *)
let subst_map inputs outputs controllables c_locals locals mem_tys =
  (* Create a map that simply maps each var to itself *)
  let map =
    List.fold_left
      (fun m { Minils.v_ident = x; Minils.v_type = ty } -> Env.add x (mk_pattern ty (Lvar x)) m)
      Env.empty (inputs @ outputs @ controllables @ c_locals @ locals)
  in
  List.fold_left (fun map (x, x_ty) -> Env.add x (mk_pattern x_ty (Lmem x)) map) map mem_tys

(* Same, but everything is in a memory state (used for translate_main_parallel_node) *)
let subst_map_all_mem inputs outputs controllables c_locals locals mem_tys =
  (* Create a map that simply maps each var to itself *)
  let map =
    List.fold_left
      (fun m { Minils.v_ident = x; Minils.v_type = ty } -> Env.add x (mk_pattern ty (Lmem x)) m)
      Env.empty (inputs @ outputs @ controllables @ c_locals @ locals)
  in
  List.fold_left (fun map (x, x_ty) -> Env.add x (mk_pattern x_ty (Lmem x)) map) map mem_tys


let build_init_mutex_meth mSynchVar =
  let null_id = Idents.gen_var "mls2obc" "NULL" in

  (* Build pthread_mutex_init(&mut_id, NULL); *)
  let generate_pthread_mutex_init_act bself mut_id =
    let mut_counts_id_eval = if (bself) then
        mk_ext_value ty_pthread_mutvar (Wmem mut_id)
      else
        mk_ext_value ty_pthread_mutvar (Wvar mut_id)
    in
    let mut_counts_id = mk_exp ty_pthread_mutvar (Eextvalue mut_counts_id_eval) in

    let qderef_op = { qual = Pervasives; name = "&" } in
    let mut_counts_id_ref = mk_exp ty_pthread_mutvar (Eop (qderef_op, [mut_counts_id])) in

    let null_extval = mk_ext_value_int (Wvar null_id) in
    let null_exp = mk_exp_int (Eextvalue null_extval) in

    let largs_init_mutex = [mut_counts_id_ref; null_exp] in
    Aop (Posixprep.qname_pthread_mut_init, largs_init_mutex)
  in
  (* Build pthread_cond_init(&cond_id, NULL); *)
  let generate_cond_init_act cond_id =
    let mut_counts_id_eval = mk_ext_value ty_pthread_mutvar (Wmem cond_id) in
    let mut_counts_id = mk_exp ty_pthread_mutvar (Eextvalue mut_counts_id_eval) in

    let qderef_op = { qual = Pervasives; name = "&" } in
    let mut_counts_id_ref = mk_exp ty_pthread_mutvar (Eop (qderef_op, [mut_counts_id])) in

    let null_extval = mk_ext_value_int (Wvar null_id) in
    let null_exp = mk_exp_int (Eextvalue null_extval) in

    let largs_init_mutex = [mut_counts_id_ref; null_exp] in
    Aop (Posixprep.qname_pthread_cond_init, largs_init_mutex)
  in

  (* First thing: pthread_mutex_init(&mut_counts, NULL); *)
  let mut_counts_id = Idents.gen_var "mls2obc" "mut_counts" in
  let lact_init_mutex = [generate_pthread_mutex_init_act false mut_counts_id ] in
  let lact_init_mutex = StringMap.fold (fun _ (condvarid, mutvarid, _, _) lacc ->
    (generate_cond_init_act condvarid)
      ::(generate_pthread_mutex_init_act true mutvarid)
      ::lacc
  ) mSynchVar lact_init_mutex in
  let init_mutex_meth = { m_name = Mother Posixprep.name_init_mutex_func;
      m_inputs = [];
      m_outputs = [];
      m_body = mk_block lact_init_mutex }
  in
  init_mutex_meth

let build_init_sync_counter_meth mSynchVar =
  let lact_sync_counter = StringMap.fold (fun _ (_,_, var_count_id, max_val) lacc ->
    (* var_count_id = max_val; *)
    let plhs = mk_pattern_int (Lmem var_count_id) in
    let erhs = mk_exp_static_int (Types.mk_static_exp Initial.tint (Sint max_val)) in
    (Aassgn (plhs, erhs))::lacc
  ) mSynchVar [] in
  let init_counter_meth = { m_name = Mother Posixprep.name_init_sync_counter_func;
      m_inputs = [];
      m_outputs = [];
      m_body = mk_block lact_sync_counter }
  in
  init_counter_meth

let translate_main_parallel_node
  ({ Minils.n_name = f; Minils.n_input = i_list; Minils.n_output = o_list;
    Minils.n_local = d_list; Minils.n_equs = _; Minils.n_stateful = stateful;
    Minils.n_contract = contract; Minils.n_params = params; Minils.n_loc = loc;
    Minils.n_mem_alloc = mem_alloc; Minils.n_parsched = oparsched;
  } as n) =
  
  (* Get the parallel schedule mapping *)
  let parsched = match oparsched with
    | None -> failwith "internal error: oparsched should not be None at that point"
    | Some p -> p
  in

  (* DEBUG
  Format.fprintf (Format.formatter_of_out_channel stdout)
    "parsched_mls = %a\n@?" Mls_printast.print_parsched_info parsched; *)

  (* Saving number of device/core used (will not change) *)
  Posixprep.rnum_thread := parsched.Minils.psch_ncore;
  (* Posixprep.rnum_device := parsched.Minils.psch_ndevice; *)

  Idents.enter_node f;
  let mem_var_tys = Mls_utils.node_memory_vars n in  (* Get memories (ex: fby) *)

  if (contract!=None) then
    failwith "mls2obc::translate_main_parallel_node : contract not supported for parallel CG"
  else
  (*let c_list, c_locals =
    match contract with
    | None -> [], []
    | Some c -> c.Minils.c_controllables, c.Minils.c_local in *)

  (* Mapping associating old vdecl to the new Lvar/Lmem (cf Obc.pattern) *)
  let (subst_map : Obc.pattern Env.t) = subst_map_all_mem i_list o_list [] [] (* c_list c_locals *)
    d_list mem_var_tys in

  (* Creating the counter variable/mutexes/cond var from all wait signal in parsched *)
  (* mSynchVar : signame |-> (condvar, mutvar, count, count_max) of the signal *)
  let mSynchVar = List.fold_left (fun mAcc lpsch_comp ->
      List.fold_left (fun mAcc psch_comp -> match psch_comp with
        | Minils.Comp_wait (nsig, max_val) ->
          (* Note: we assume that we have exactly 1 wait per signal *)
          let (condvarid,  mutvarid, countvarid) = Posixprep.get_ident_of_signal nsig in
          StringMap.add nsig (condvarid, mutvarid, countvarid, max_val) mAcc
        | _ -> mAcc
      ) mAcc lpsch_comp
    ) StringMap.empty parsched.Minils.psch_eqs
  in

  (* Translate the statements according to lparsched *)
  let (v, si, j, ls_thread) = List.fold_left
    (fun (v_acc, si_acc, j_acc, (ls_acc : (act list) list)) lparsched_comp ->
      let (nv, nsi, nj, (ns_list : act list)) = translate_parsched_comp_list
        subst_map empty_call_context mSynchVar lparsched_comp in
      (* Note: separation between the "step" statements of different threads *)
      let (nlact_thread : act list list) = [ns_list] in 
      ( (List.rev_append v_acc nv),
        si_acc @ nsi,
        (List.rev_append j_acc nj),
        nlact_thread @ ls_acc )
    ) ([],[],[],[]) parsched.Minils.psch_eqs
  in

  (* Translate contracts *)
  (* let (m_contr, si_contr, j_contr, s_list_contr, varloc_list_contr) =
    translate_contract subst_map mem_var_tys contract in *)
  (* s_list_constr can no longer go into a unified step function ===> contract disabled *)

  (* Assembling the new methods *)
  let init_mutex_meth = build_init_mutex_meth mSynchVar in
  let init_sync_counter_meth = build_init_sync_counter_meth mSynchVar in
  let lreset_meth =  if stateful then
      [ { m_name = Mreset; m_inputs = []; m_outputs = [];
        m_body = mk_block (si (* @ si_contr *) ) } ]
    else []
  in
  let lthread_id = List.mapi (fun thread_num (act_thr:act list) ->
    (* void* work_CPU_0(void* arg) { ... ; return NULL; } *)
    (*   => The particularity of inputs and outputs will be managed in cgen *)
    { m_name = Mthread thread_num;
      m_inputs = [];
      m_outputs = [];
      m_body = mk_block act_thr }
  ) (List.rev ls_thread) in
  let l_methods = init_mutex_meth :: init_sync_counter_meth :: (lreset_meth @ lthread_id) in

  (* Memory: put everything (all local vars included) inside lmem *)
  let i_list = translate_var_dec i_list in
  let o_list = translate_var_dec o_list in
  let d_list = translate_var_dec (v @ d_list) in
  let lmem = (* (List.rev_append *)
    (List.rev_append
      (List.rev_append i_list o_list)
    d_list)
    (* m_contr) *)
  in
  (* Adding cond var/mutex and count... in short all synchronisation variables *)
  let lmem = StringMap.fold (fun _ (condvarid, mutvarid, countvarid, _) lacc ->
    (Obc_utils.mk_var_dec condvarid Posixprep.ty_pthread_condvar)::
    (Obc_utils.mk_var_dec mutvarid Posixprep.ty_pthread_mutvar)::
    (Obc_utils.mk_var_dec countvarid Initial.tint)::lacc
  ) mSynchVar lmem in

  (* Final result - assembling the new class *)
  { cd_name = f; cd_stateful = stateful; cd_mems = lmem; cd_params = params;
    cd_objs = j (*@ j_contr*); cd_methods = l_methods; cd_loc = loc; cd_mem_alloc = mem_alloc }


let translate_node
  ({ Minils.n_name = f; Minils.n_input = i_list; Minils.n_output = o_list;
    Minils.n_local = d_list; Minils.n_equs = eq_list; Minils.n_stateful = stateful;
    Minils.n_contract = contract; Minils.n_params = params; Minils.n_loc = loc;
    Minils.n_mem_alloc = mem_alloc; Minils.n_parsched = oparsched;
  } as n) =
  (* If oparsched is not None, then activate the alternate code generation (scattered mainnode) *)
  if (oparsched!=None) then translate_main_parallel_node n else begin
    Idents.enter_node f;
    let mem_var_tys = Mls_utils.node_memory_vars n in
    let c_list, c_locals =
      match contract with
      | None -> [], []
      | Some c -> c.Minils.c_controllables, c.Minils.c_local in
    let subst_map = subst_map i_list o_list c_list c_locals d_list mem_var_tys in
    let (v, si, j, s_list) = translate_eq_list subst_map empty_call_context eq_list in
    let (m_c, si', j', s_list', d_list') = translate_contract subst_map mem_var_tys contract in

    let i_list = translate_var_dec i_list in
    let o_list = translate_var_dec o_list in
    let d_list = translate_var_dec (v @ d_list) in
    let m, d_list = List.partition
      (fun vd -> List.exists (fun (i,_) -> i = vd.v_ident) mem_var_tys) d_list in
    let m', o_list = List.partition
      (fun vd -> List.exists (fun (i,_) -> i = vd.v_ident) mem_var_tys) o_list in
    let s = s_list @ s_list' in
    let j = j' @ j in
    let si = si @ si' in

    let stepm = { m_name = Mstep; m_inputs = i_list; m_outputs = o_list;
                  m_body = mk_block ~locals:(d_list' @ d_list) s }
    in
    let resetm = { m_name = Mreset; m_inputs = []; m_outputs = []; m_body = mk_block si } in

    if stateful
    then { cd_name = f; cd_stateful = true; cd_mems = m' @ m @ m_c; cd_params = params;
           cd_objs = j; cd_methods = [stepm; resetm]; cd_loc = loc; cd_mem_alloc = mem_alloc }
    else (
      (* Functions won't have [Mreset] or memories,
         they still have [params] and instances (of functions) *)
      { cd_name = f; cd_stateful = false; cd_mems = []; cd_params = params;
        cd_objs = j; cd_methods = [stepm]; cd_loc = loc; cd_mem_alloc = mem_alloc }
    )
  end

let translate_ty_def { Minils.t_name = name; Minils.t_desc = tdesc;
                       Minils.t_loc = loc } =
  let tdesc = match tdesc with
    | Minils.Type_abs -> Type_abs
    | Minils.Type_alias ln -> Type_alias ln
    | Minils.Type_enum tag_name_list -> Type_enum tag_name_list
    | Minils.Type_struct field_ty_list -> Type_struct field_ty_list
  in
  { t_name = name; t_desc = tdesc; t_loc = loc }

let translate_const_def { Minils.c_name = name; Minils.c_value = se;
                          Minils.c_type = ty; Minils.c_loc = loc } =
  { Obc.c_name = name;
    Obc.c_value = se;
    Obc.c_type = ty;
    Obc.c_loc = loc }

let translate_classtype_dec { Minils.c_nameclass = nclass; Minils.c_insttypes = instty; Minils.c_loc = loc } =
  { Obc.c_nameclass = nclass; Obc.c_insttypes = instty; Obc.c_loc = loc }

let translate_kernel_def (k:Minils.kernel_dec) =
  { Obc.k_namekernel = k.Minils.k_namekernel;
    Obc.k_input = translate_var_dec k.Minils.k_input;
    Obc.k_output = translate_var_dec k.Minils.k_output;
    Obc.k_loc = k.Minils.k_loc;
    Obc.k_issource = k.Minils.k_issource;
    Obc.k_srcbin = k.Minils.k_srcbin;
    Obc.k_dim = k.Minils.k_dim;
    Obc.k_local = translate_var_dec k.Minils.k_local 
  }


let program { Minils.p_modname = p_modname; Minils.p_opened = p_o; Minils.p_desc = pd; } =
  build_anon pd;

  let program_desc pd acc = match pd with
    | Minils.Pnode n when not (Itfusion.is_anon_node n.Minils.n_name) ->
        Pclass (translate_node n) :: acc
    (* dont't translate anonymous nodes, they will be inlined *)
    | Minils.Pnode _ -> acc
    | Minils.Ptype t -> Ptype (translate_ty_def t) :: acc
    | Minils.Pconst c -> Pconst (translate_const_def c) :: acc
    | Minils.Pclasstype _ -> acc (* Not needed anymore *)
    | Minils.Pkernel k -> Pkernel (translate_kernel_def k) :: acc
  in
  let p_desc = List.fold_right program_desc pd [] in
  { p_modname = p_modname;
    p_opened = p_o;
    p_desc = p_desc }


let signature s =
  { sig_name = s.Minils.sig_name;
    sig_inputs = s.Minils.sig_inputs;
    sig_stateful = s.Minils.sig_stateful;
    sig_outputs = s.Minils.sig_outputs;
    sig_params = s.Minils.sig_params;
    sig_param_constraints = s.Minils.sig_param_constraints;
    sig_loc = s.Minils.sig_loc }

let interface i =
  let interface_decl id = match id with
    | Minils.Itypedef td -> Itypedef (translate_ty_def td)
    | Minils.Iconstdef cd -> Iconstdef (translate_const_def cd)
    | Minils.Isignature s -> Isignature (signature s)
    | Minils.Iclasstype c -> Iclasstype (translate_classtype_dec c)
  in
  { i_modname = i.Minils.i_modname;
    i_opened = i.Minils.i_opened;
    i_desc = List.map interface_decl i.Minils.i_desc }
