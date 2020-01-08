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
open Misc
open Idents
open Location
open Heptagon
open Hept_utils
open Hept_mapfold
open Types
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

(* Utilities concerning patterns and variable declaration *)
let rec get_first_var pat = match pat with
  | Etuplepat pl ->
    if pl=[] then None else get_first_var (List.hd pl)
  | Evarpat vid -> Some vid

let rec get_list_var pat = match pat with
  | Etuplepat pl ->
    List.fold_left (fun acc p -> (get_list_var p)@acc) [] pl
  | Evarpat vid -> [vid]

 let rec search_vd vid lvdm = match lvdm with  (* TODO: optimise that with a map? *)
  | [] -> raise Not_found
  | h::t ->
    if (h.vm_ident=vid) then h else search_vd vid t



let se_to_se_list se =  match se.se_desc with
  | Stuple se_list -> se_list
  | _ -> assert false

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
  let flatten e =
    if is_list e then
      e_to_e_list e
    else
      [e]
  in
    List.flatten (List.map flatten l)


let var2per = ref Env.empty 

let is_block_model = ref true

(** Creates a new equation x = e, adds x to d_list
    and the equation to eq_list. *)
let equation (d_list, eq_list) e oper =
  let add_one_var ty lin d_list =
    let n = Idents.gen_var "normalize" "v" in
    (if (!is_block_model) then
      let per = match oper with
        | None -> failwith "No period in block model expression"
        | Some per -> per
      in
      var2per := Env.add n per !var2per
    );
    let d_list = (mk_var_dec n ty ~linearity:lin) :: d_list in
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
            (fun n ty lin -> mk_exp (Evar n) ty ~linearity:lin) var_list ty_list lin_list in
          let e = Eapp(mk_app Etuple, e_list, None) in
            (d_list, eq_list), e
      | _ ->
          let n, d_list = add_one_var e.e_ty e.e_linearity d_list in
          let eq_list = (mk_equation (Eeq (Evarpat n, e))) :: eq_list in
            (d_list, eq_list), Evar n

(* [(e1,...,ek) when C(n) = (e1 when C(n),...,ek when C(n))] *)
let whenc context e c n e_orig =
  let when_on_c c n context e =
    (* If memalloc is activated, there cannot be a stateful exp inside a when. Indeed,
       the expression inside the when will be called on a fast rhythm and write its result
       in a variable that is slow because of the when. Although this value won't be used,
       we have to be careful not to share this variable with another on the same clock as
       the value of the latter will be overwritten.  *)
    let context, e =
      if !Compiler_options.do_mem_alloc && Stateful.exp_is_stateful e then
        let context, n = equation context e None in
        context, { e with e_desc = n }
      else
        context, e
    in
    { e_orig with e_desc = Ewhen(e, c, n) }, context
  in
  if is_list e then (
    let e_list, context = Misc.mapfold (when_on_c c n) context (e_to_e_list e) in
        context, { e_orig with e_desc = Eapp(mk_app Etuple, e_list, None) }
  ) else
    let e, context = when_on_c c n context e in
    context, e

let whencmodel context e (ph, per) oper e_orig =
  let when_cmodel_aux (ph, per) oper context e =
    let context, e =
      if !Compiler_options.do_mem_alloc && Stateful.exp_is_stateful e then
        let context, n = equation context e oper in
        context, { e with e_desc = n }
      else
        context, e
    in
    { e_orig with e_desc = Ewhenmodel(e, (ph, per)) }, context
  in
  if is_list e then
    let e_list, context = Misc.mapfold (when_cmodel_aux (ph, per) oper) context (e_to_e_list e) in
    context, { e_orig with e_desc = Eapp(mk_app Etuple, e_list, None) }
  else
    let e, context = when_cmodel_aux (ph, per) oper context e in
    context, e

let currentcmodel context seInit e (ph, per) oper e_orig =
  let currentcmodel_aux (ph, per) oper context (e, seInit) =
    let context, e =
      if !Compiler_options.do_mem_alloc && Stateful.exp_is_stateful e then
        let context, n = equation context e oper in
        context, { e with e_desc = n }
      else
        context, e
    in
    { e_orig with e_desc = Ecurrentmodel ((ph, per), seInit, e) }, context
  in
  if is_list e then
    let elist = e_to_e_list e in
    let seInitlist = se_to_se_list seInit in
    let eseInitlist = List.combine elist seInitlist in
    let e_list, context = Misc.mapfold (currentcmodel_aux (ph, per) oper) context eseInitlist in
    context, { e_orig with e_desc = Eapp(mk_app Etuple, e_list, None) }
  else
    let e, context = currentcmodel_aux (ph, per) oper context (e, seInit) in
    context, e

let delaymodel context e d oper e_orig =
  let delaymodel_aux d oper context e =
    let context, e =
      if !Compiler_options.do_mem_alloc && Stateful.exp_is_stateful e then
        let context, n = equation context e oper in
        context, { e with e_desc = n }
      else
        context, e
    in
    { e_orig with e_desc = Edelay(d, e) }, context
  in
  if is_list e then
    let e_list, context = Misc.mapfold (delaymodel_aux d oper) context (e_to_e_list e) in
    context, { e_orig with e_desc = Eapp(mk_app Etuple, e_list, None) }
  else
    let e, context = delaymodel_aux d oper context e in
    context, e

let delayfbymodel context seInit e d oper e_orig =
  let delayfbymodel_aux d oper context (seInit, e) =
    let context, e =
      if !Compiler_options.do_mem_alloc && Stateful.exp_is_stateful e then
        let context, n = equation context e oper in
        context, { e with e_desc = n }
      else
        context, e
    in
    { e_orig with e_desc = Edelayfby (d, seInit, e) }, context
  in
  if is_list e then
    let seInitlist = se_to_se_list seInit in
    let elist = e_to_e_list e in
    let seInitelist = List.combine seInitlist elist in
    let e_list, context = Misc.mapfold (delayfbymodel_aux d oper) context seInitelist in
    context, { e_orig with e_desc = Eapp(mk_app Etuple, e_list, None) }
  else
    let e, context = delayfbymodel_aux d oper context (seInit, e) in
    context, e

let buffer context e oper e_orig =
  let buffer_aux oper context e =
    let context, e =
      if !Compiler_options.do_mem_alloc && Stateful.exp_is_stateful e then
        let context, n = equation context e oper in
        context, { e with e_desc = n }
      else
        context, e
    in
    { e_orig with e_desc = Ebuffer e }, context
  in
  if is_list e then
    let e_list, context = Misc.mapfold (buffer_aux oper) context (e_to_e_list e) in
    context, { e_orig with e_desc = Eapp(mk_app Etuple, e_list, None) }
  else
    let e, context = buffer_aux oper context e in
    context, e

let bufferfby context seInit e oper e_orig =
  let bufferfby_aux oper context (seInit, e) =
    let context, e =
      if !Compiler_options.do_mem_alloc && Stateful.exp_is_stateful e then
        let context, n = equation context e oper in
        context, { e with e_desc = n }
      else
        context, e
    in
    { e_orig with e_desc = Ebufferfby (seInit, e) }, context
  in
  if is_list e then
    let seInitlist = se_to_se_list seInit in
    let elist = e_to_e_list e in
    let seInitelist = List.combine seInitlist elist in
    let e_list, context = Misc.mapfold (bufferfby_aux oper) context seInitelist in
    context, { e_orig with e_desc = Eapp(mk_app Etuple, e_list, None) }
  else
    let e, context = bufferfby_aux oper context (seInit, e) in
    context, e

let bufferlat context e lat oper e_orig =
  let bufferlat_aux lat oper context e =
    let context, e =
      if !Compiler_options.do_mem_alloc && Stateful.exp_is_stateful e then
        let context, n = equation context e oper in
        context, { e with e_desc = n }
      else
        context, e
    in
    { e_orig with e_desc = Ebufferlat(lat, e) }, context
  in
  if is_list e then
    let e_list, context = Misc.mapfold (bufferlat_aux lat oper) context (e_to_e_list e) in
    context, { e_orig with e_desc = Eapp(mk_app Etuple, e_list, None) }
  else
    let e, context = bufferlat_aux lat oper context e in
    context, e

let fbyq context seInit e oper e_orig =
  let fbyq_aux seInit oper context e =
    let context, e =
      if !Compiler_options.do_mem_alloc && Stateful.exp_is_stateful e then
        let context, n = equation context e oper in
        context, { e with e_desc = n }
      else
        context, e
    in
    { e_orig with e_desc = Efbyq(seInit, e) }, context
  in
  if is_list e then
    let e_list, context = Misc.mapfold (fbyq_aux seInit oper) context (e_to_e_list e) in
    context, { e_orig with e_desc = Eapp(mk_app Etuple, e_list, None) }
  else
    let e, context = fbyq_aux seInit oper context e in
    context, e

let whenqcmodel context e min max ratio oper e_orig =
  let whenq_cmodel_aux min max ratio oper context e =
    let context, e =
      if !Compiler_options.do_mem_alloc && Stateful.exp_is_stateful e then
        let context, n = equation context e oper in
        context, { e with e_desc = n }
      else
        context, e
    in
    { e_orig with e_desc = Ewhenq(e, (min,max), ratio) }, context
  in
  if is_list e then
    let e_list, context = Misc.mapfold (whenq_cmodel_aux min max ratio oper) context (e_to_e_list e) in
    context, { e_orig with e_desc = Eapp(mk_app Etuple, e_list, None) }
  else
    let e, context = whenq_cmodel_aux min max ratio oper context e in
    context, e

let currentqcmodel context seInit e min max ratio oper e_orig =
  let currentqcmodel_aux min max ratio oper context (e, seInit) =
    let context, e =
      if !Compiler_options.do_mem_alloc && Stateful.exp_is_stateful e then
        let context, n = equation context e oper in
        context, { e with e_desc = n }
      else
        context, e
    in
    { e_orig with e_desc = Ecurrentq (ratio, (min,max), seInit, e) }, context
  in
  if is_list e then
    let elist = e_to_e_list e in
    let seInitlist = se_to_se_list seInit in
    let eseInitlist = List.combine elist seInitlist in
    let e_list, context = Misc.mapfold (currentqcmodel_aux min max ratio oper) context eseInitlist in
    context, { e_orig with e_desc = Eapp(mk_app Etuple, e_list, None) }
  else
    let e, context = currentqcmodel_aux min max ratio oper context (e, seInit) in
    context, e

let bufferfbyq context seInit e oper e_orig = 
  let bufferfbyq_aux oper context (seInit, e) =
    let context, e =
      if !Compiler_options.do_mem_alloc && Stateful.exp_is_stateful e then
        let context, n = equation context e oper in
        context, { e with e_desc = n }
      else
        context, e
    in
    { e_orig with e_desc = Ebufferfbyq (seInit, e) }, context
  in
  if is_list e then
    let seInitlist = se_to_se_list seInit in
    let elist = e_to_e_list e in
    let seInitelist = List.combine seInitlist elist in
    let e_list, context = Misc.mapfold (bufferfbyq_aux oper) context seInitelist in
    context, { e_orig with e_desc = Eapp(mk_app Etuple, e_list, None) }
  else
    let e, context = bufferfbyq_aux oper context (seInit, e) in
    context, e


(* ===== *)


type kind = ExtValue | Any

(** Creates an equation and add it to the context if necessary. *)
let add context oper expected_kind e =
  let up = match e.e_desc, expected_kind with
     (* static arrays and records should be normalized to simplify code generation *)
    | Econst { se_desc = Sarray _ | Sarray_power _ | Srecord _ }, ExtValue -> true
    | (Evar _ | Eapp ({ a_op = Efield | Etuple | Ereinit }, _, _) | Ewhen _
          | Econst _) , ExtValue -> false
    | _ , ExtValue -> true
    | _ -> false in
  if up then
    let context, n = equation context e oper in
      context, { e with e_desc = n }
  else
    context, e

let add_list context oper expected_kind e_list =
  let aux context e =
    let context, e = add context oper expected_kind e in
      e, context
  in
    mapfold aux context e_list

let rec translate kind context oper e =
  let context, e' = match e.e_desc with
    | Econst _
    | Evar _ -> context, e (* TODO : check oper? *)
    | Epre(v, e1) -> fby kind context oper e v e1
    | Efby({ e_desc = Econst v }, e1) -> fby kind context oper e (Some v) e1
    | Estruct l ->
        let translate_field context (f, e) =
          let context, e = translate ExtValue context oper e in
            (f, e), context
        in
        let l, context = mapfold translate_field context l in
          context, { e with e_desc = Estruct l }
    | Ewhen(e1, c, n) ->
        assert(oper=None);
        let context, e1 = translate kind context None e1 in
        whenc context e1 c n e
    | Ecurrent _ -> 
      failwith "Normalization : current should have been removed"
    | Emerge(n, tag_e_list) ->
      assert(oper=None);
      merge context oper e n tag_e_list

    (* Model expressions *)
    | Ewhenmodel (e1, (ph, per)) ->
      let pere = match oper with
        | None -> failwith "No period in block model expression"
        | Some pere -> pere
      in
      (* DEBUG
      Format.fprintf (Format.formatter_of_out_channel stdout) "pere = %i | per = %i | e = %a\n@?"
        pere per Hept_printer.print_exp e; *)
      assert(pere mod per = 0);
      let context, e1 = translate ExtValue context (Some (pere/per)) e1 in
      whencmodel context e1 (ph, per) oper e
    | Ecurrentmodel ((ph, per), seInit, e1) ->
      let pere = match oper with
        | None -> failwith "No period in block model expression"
        | Some pere -> pere
      in
      let context, e1 = translate ExtValue context (Some (pere*per)) e1 in
      currentcmodel context seInit e1 (ph, per) oper e
    | Edelay (d, e1) ->
      let context, e1 = translate kind context oper e1 in
      delaymodel context e1 d oper e
    | Edelayfby (d, seInit, e1) ->
      let context, e1 = translate kind context oper e1 in
      delayfbymodel context seInit e1 d oper e
    
    | Ebuffer e1 ->
      let context, e1 = translate kind context oper e1 in
      buffer context e1 oper e

    | Ebufferfby (seInit, e1) ->
      let context, e1 = translate kind context oper e1 in
      bufferfby context seInit e1 oper e

    | Ebufferlat (lat, e1) ->
      let context, e1 = translate kind context oper e1 in
      bufferlat context e1 lat oper e

    | Efbyq (seInit, e1) ->
      let context, e1 = translate kind context oper e1 in
      fbyq context seInit e1 oper e

    | Ewhenq (e1, (min,max), ratio) ->
      let pere = match oper with
        | None -> failwith "No period in block model expression"
        | Some pere -> pere
      in
      (* DEBUG
      Format.fprintf (Format.formatter_of_out_channel stdout) "pere = %i | per = %i | e = %a\n@?"
        pere per Hept_printer.print_exp e; *)
      assert(pere mod ratio = 0);
      let context, e1 = translate ExtValue context (Some (pere/ratio)) e1 in
      whenqcmodel context e1 min max ratio oper e

    | Ecurrentq (ratio, (min,max), seInit, e1) ->
      let pere = match oper with
        | None -> failwith "No period in block model expression"
        | Some pere -> pere
      in
      let context, e1 = translate ExtValue context (Some (pere*ratio)) e1 in
      currentqcmodel context seInit e1 min max ratio oper e

    | Ebufferfbyq (seInit, e1) ->
      let context, e1 = translate kind context oper e1 in
      bufferfbyq context seInit e1 oper e

    | Eapp({ a_op = Eifthenelse }, [e1; e2; e3], _) ->
        ifthenelse context oper e e1 e2 e3
    (* XXX Huge hack to avoid comparing tuples... (temporary, until this is
       fixed where it should be) *)
    | Eapp({ a_op = (Efun ({ Names.qual = Names.Pervasives; Names.name = "=" }) as op)},
           [x;y], reset) when is_list x ->
        let x = e_to_e_list x and y = e_to_e_list y in
        let xy = List.fold_left2 (fun acc x y ->
          let cmp = mk_exp (mk_op_app op [x; y] ~reset) Initial.tbool ~linearity:Ltop in
          mk_exp (mk_op_app (Efun Initial.pand) [acc; cmp] ~reset) Initial.tbool ~linearity:Ltop)
          dtrue
          x y
        in
        translate kind context oper xy
    | Eapp(app, e_list, r) ->
        let context, e_list = translate_list ExtValue context oper e_list in
          context, { e with e_desc = Eapp(app, flatten_e_list e_list, r) }
    | Eiterator (it, app, n, pe_list, e_list, reset) ->
        let context, pe_list = translate_list ExtValue context oper pe_list in
        let context, e_list = translate_list ExtValue context oper e_list in
        context, { e with e_desc = Eiterator(it, app, n, flatten_e_list pe_list,
                                             flatten_e_list e_list, reset) }
    | Esplit (x, e1) ->
        let context, e1 = translate ExtValue context oper e1 in
        let context, x = translate ExtValue context oper x in
        let id = match x.e_desc with Evar x -> x | _ -> assert false in
        let mk_when c = mk_exp ~linearity:e1.e_linearity (Ewhen (e1, c, id)) e1.e_ty in
          (match x.e_ty with
            | Tid t ->
                (match Modules.find_type t with
                  | Signature.Tenum cl ->
                      let el = List.map mk_when cl in
                        context, { e with e_desc = Eapp(mk_app Etuple, el, None) }
                  | _ -> Misc.internal_error "normalize split")
            | _ -> Misc.internal_error "normalize split")

    | Elast _ | Efby _ ->
        Error.message e.e_loc Error.Eunsupported_language_construct
  in add context oper kind e'

and translate_list kind context oper e_list =
  match e_list with
    | [] -> context, []
    | e :: e_list ->
        let context, e = translate kind context oper e in
        let context, e_list = translate_list kind context oper e_list in
          context, e :: e_list

and fby kind context oper e v e1 =
  let mk_fby c e =
    mk_exp ~loc:e.e_loc (Epre(Some c, e)) e.e_ty ~linearity:Ltop in
  let mk_pre e =
    mk_exp ~loc:e.e_loc (Epre(None, e)) e.e_ty ~linearity:Ltop in
  let context, e1 = translate ExtValue context oper e1 in
  match e1.e_desc, v with
    | Eapp({ a_op = Etuple } as app, e_list, r),
      Some { se_desc = Stuple se_list } ->
        let e_list = List.map2 mk_fby se_list e_list in
        let e = { e with e_desc = Eapp(app, e_list, r) } in
          translate kind context oper e
    | Econst { se_desc = Stuple se_list },
      Some { se_desc = Stuple v_list } ->
        let e_list = List.map2 mk_fby v_list
          (exp_list_of_static_exp_list se_list) in
        let e = { e with e_desc = Eapp(mk_app Etuple, e_list, None) } in
          translate kind context oper e
    | Eapp({ a_op = Etuple } as app, e_list, r), None ->
        let e_list = List.map mk_pre e_list in
        let e = { e with e_desc = Eapp(app, e_list, r) } in
          translate kind context oper e
    | Econst { se_desc = Stuple se_list }, None ->
        let e_list = List.map mk_pre (exp_list_of_static_exp_list se_list) in
        let e = { e with e_desc = Eapp(mk_app Etuple, e_list, None) } in
          translate kind context oper e
    | _ -> context, { e with e_desc = Epre(v, e1) }

(** transforms [if x then e1, ..., en else e'1,..., e'n]
    into [if x then e1 else e'1, ..., if x then en else e'n]  *)
and ifthenelse context oper e e1 e2 e3 =
  let context, e1 = translate ExtValue context oper e1 in
  let context, e2 = translate ExtValue context oper e2 in
  let context, e3 = translate ExtValue context oper e3 in
  let mk_ite_list e2_list e3_list =
    let mk_ite e'2 e'3 =
      mk_exp ~loc:e.e_loc
        (Eapp (mk_app Eifthenelse, [e1; e'2; e'3], None)) e'2.e_ty ~linearity:e'2.e_linearity
    in
    let e_list = List.map2 mk_ite e2_list e3_list in
      { e with e_desc = Eapp(mk_app Etuple, e_list, None) }
  in
    if is_list e2 then (
      let e2_list, context = add_list context oper ExtValue (e_to_e_list e2) in
      let e3_list, context = add_list context oper ExtValue (e_to_e_list e3) in
        context, mk_ite_list e2_list e3_list
    ) else
      context, { e with e_desc = Eapp (mk_app Eifthenelse, [e1; e2; e3], None) }

(** transforms [merge x (c1, (e11,...,e1n));...;(ck, (ek1,...,ekn))] into
    [merge x (c1, e11)...(ck, ek1),..., merge x (c1, e1n)...(ck, ekn)]    *)
and merge context oper e x c_e_list =
    let translate_tag context (tag, e) =
      let context, e = translate ExtValue context oper e in
        (tag, e), context
    in
    let mk_merge x c_list e_lists =
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
                  (fun context e_list -> add_list context oper ExtValue e_list)
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
    let dis context eq = match eq.eq_desc with
      | Eeq (pat, e) -> distribute context eq pat e
      | _ -> assert false
    in
    let eqs = List.map2 mk_simple_equation pat_list e_list in
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

and translate_eq ((d_list, eq_list) as context) oper eq = match eq.eq_desc with
  | Eeq (pat, e) ->
      let context, e = translate ExtValue context oper e in
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
    (fun context eq -> translate_eq context None eq)
    (d_list, []) eq_list

let eq _funs context eq =
  let context = translate_eq context None eq in
    eq, context

let eq_model _funs context eqm =
  (* Trick - convert eqm into a eq *)
  let dummyeq = mk_simple_equation eqm.eqm_lhs eqm.eqm_rhs in
  let per = Clocks.get_period_ock eqm.eqm_clk in
  let context = translate_eq context (Some per) dummyeq in
  eqm, context


(* ------- *)

(* === Management of latency chains === *)

(* Get the list of variable from the lhs *)
let rec get_vars_lhs plhs = match plhs with
  | Etuplepat pl -> List.fold_left (fun lacc p ->
      (get_vars_lhs p) @ lacc
    ) [] pl
  | Evarpat vid -> vid::[]

(* Get the list of *present* variable used in the rhs of a model equation *)
let get_lvar_used eqm =
  let exp_lvar_used funs lacc exp = match exp.e_desc with
    | Evar vid | Elast vid -> exp, vid::lacc        (* Variable use detected ! *)
    | _ -> Hept_mapfold.exp funs lacc exp           (* Other cases: just do a recursion *)
  in
  let funs_lvar_used = { Hept_mapfold.defaults with exp = exp_lvar_used } in
  let _, lvar = funs_lvar_used.eq_model funs_lvar_used [] eqm in
  lvar

(* Add the new intermediate variables introduced by the normalization in the chains *)
let convert_latency_chain vm_acc eqm_acc latency lchain =
  assert((List.length lchain)>= 2);

  (* l_chain_repeated : (l_chain[1], l_chain[0]), (l_chain[2], l_chain[1]), ... , (l_chain[n], l_chain[n-1]) *)
  let (_,lchain_repeated) = List.fold_left (fun (last_elem, lacc) elem ->
    (elem, (elem, last_elem)::lacc)
  ) (List.hd lchain, []) (List.tl lchain) in

  (* Getting the dependence graph from eqm_list *)
  (* mVar2VarUsed: var_id -> var_id used by equations *)
  let mVar2VarUsed = List.fold_left (fun macc eqm ->
    let lvarlhs = get_vars_lhs eqm.eqm_lhs in
    List.fold_left (fun macc varid ->
      let lvarUsed = get_lvar_used eqm in
      Idents.Env.add varid lvarUsed macc
    ) macc lvarlhs
  ) Idents.Env.empty eqm_acc in

  (* Set of nodes added by the transformation *)
  let sAdded_by_norm = List.fold_left (fun sacc vm ->
    Idents.IdentSet.add vm.vm_ident sacc
  ) Idents.IdentSet.empty vm_acc in

  let rec explore_graph mVar2VarUsed sAdded_by_norm vid_end isFirst vid_current =
    (* DEBUG
    Format.fprintf (Format.formatter_of_out_channel stdout) "vid_current = %a\n@?"
      print_ident vid_current; *)

    (* Termination condition: path found *)
    if (vid_current=vid_end) then Some [vid_end] else

    (* If we are going outside of the area of the old equation *)
    if ((not isFirst) && (not (Idents.IdentSet.mem vid_current sAdded_by_norm))) then None else

    (* We explore further *)
    let lsucc = try
        Idents.Env.find vid_current mVar2VarUsed
      with Not_found -> []  (* We have an input -> No successor *)
    in

    (* Recursion *)
    let opath = List.fold_left (fun oacc vid_succ ->
      let onpath = explore_graph mVar2VarUsed sAdded_by_norm vid_end false vid_succ in
      match (oacc, onpath) with
      | (None, None) -> None
      | (None, Some npath) -> Some (vid_current::npath)
      | (_, None) -> oacc
      | (Some _, Some _) -> failwith ("Error -latency chain: double occurence of " ^
            (Idents.name vid_end) ^ " in its chain of equation (accessible from " ^
            (Idents.name vid_current) ^ " )")
    ) None lsucc in
    opath
  in

  let (nlchain_repeated : var_ident list list) = List.map (fun (vid_start, vid_end) ->
    (* Idea: we explore the dependence tree starting from vid_start, until we encounter vid_end
      Note: if we have a node not from sAdded_by_norm, then stop the exploration
        => Because vid_end should occurs exactly ONCE in the original equation, it is a tree
    *)
    let ofound_path = explore_graph mVar2VarUsed sAdded_by_norm vid_end true vid_start in
    match ofound_path with
    | None -> failwith ("Internal error - latency chain: path from " ^ (Idents.name vid_start) ^ " to "
                        ^ (Idents.name vid_end) ^ " not found after normalization.")
    | Some path -> path
  ) lchain_repeated in

  (* DEBUG
  let print_nlchain_repeated ff llchain =
    Format.fprintf ff "[[[";
    List.iter (fun lchain ->
      Format.fprintf ff "[";
      List.iter (fun elem ->
        Format.fprintf ff "%a, " print_ident elem
      ) lchain;
      Format.fprintf ff "];\n@?"
    ) llchain;
    Format.fprintf ff "]]]"
  in
  Format.fprintf (Format.formatter_of_out_channel stdout) "nlchain_repeated = %a\n@?"
    print_nlchain_repeated nlchain_repeated; *)


  (* We reform the chain of dependence, in the right direction *)
  (* Exemple of nlchain_repeated: (d->x->c) (c->w->b) (b->v->a)  *)
  let (nlchain,_) = List.fold_left (fun (lacc, isfirst) lpath ->
    (* lpath needs to be inverted *)
    let nlacc = if (isfirst) then (
      assert(lacc=[]);
      List.rev lpath
    ) else
      let lpath_minus_start = List.tl lpath in
      List.rev_append lpath_minus_start lacc
    in
    (nlacc, false)
  ) ([], true) nlchain_repeated in

  let annm_desc = Ann_latchain (latency, nlchain) in
  Hept_utils.mk_annot_model annm_desc


(* ------- *)

let block funs context b =
  is_block_model := false;
  let _, (v_acc, eq_acc) = Hept_mapfold.block funs context b in
    { b with b_local = v_acc@b.b_local; b_equs = eq_acc}, ([], [])

let block_model funs context bm =
  var2per := Env.empty;
  is_block_model := true;

  (* Getting the eqm clock here *)
  let get_ock_from_var llocs pat =
    match get_first_var pat with
    | None -> (* If an equation does not have any lhs, then put it in base clock *)
      Clocks.base_osynch_clock
    | Some vid ->
      try 
        let vdm = search_vd vid llocs in
        vdm.vm_clock
      with (* The variable is not a local variable ==> base clock *)
        Not_found -> Clocks.base_osynch_clock
  in

  (* Step 0 - Updating/creating eqm clock here , so that the eq_model function get the right "oper" *)
  let nleqs = List.map (fun eqm ->
      { eqm with eqm_clk = (get_ock_from_var bm.bm_local eqm.eqm_lhs)}
    ) bm.bm_eqs
  in
  let bm = { bm with bm_eqs = nleqs } in

  (* Step 0.5 - keeping track of the annotations of the equations *)
  (* mannoteq : varname => annot_eq_model list *)
  let mannoteq = List.fold_left (fun macc eqm ->
    if (eqm.eqm_annot = []) then macc else

    let plist = get_list_var eqm.eqm_lhs in
    if (plist=[]) then
      failwith "Annotation on model equations with no lhs forbidden.";

    (* Label goes to the first one *)
    let lannot_nlabel = List.filter (fun eqmann -> match eqmann.anneqm_desc with
      | Anneqm_label _ -> false
      | _ -> true
    ) eqm.eqm_annot in
    let first_varid = List.hd plist in

    let macc = Env.add first_varid eqm.eqm_annot macc in
    let macc = List.fold_left (fun macc vid ->
      Env.add vid lannot_nlabel macc
    ) macc (List.tl plist) in
    macc
  ) Env.empty bm.bm_eqs in


  (* Step 1 - Recursion *)
  let _, (v_acc, eq_acc) = Hept_mapfold.block_model funs context bm in

  (* Step 2 - rebuilding the equation model after the normalisation *)
  let vm_acc = List.map (fun vd ->
    let per = try 
        Env.find vd.v_ident !var2per
      with Not_found ->
        failwith ("Period of newly created variable " ^ (Idents.name vd.v_ident) ^ " was not found.")
    in
    let ock = Clocks.fresh_osynch_period per in
    mk_var_dec_model ~clock:ock vd.v_ident vd.v_type
  ) v_acc in

  (* We convert the equations "eq" back to "eqm" *)
  (* By construction, the only variable in v_acc have fresh clocks *)
  (*  ===> We can translate "v_acc" to model variable declaration *)
  let llocs = List.rev_append vm_acc bm.bm_local in 
  let eqm_acc = List.map (fun eq ->
    match eq.eq_desc with
    | Eeq (p, e) ->

      (* Get annotation of the equation from record previously established *)
      (* All eq annotations are distributed. Label goes to the first term of the plhs *)
      (* Because normalisation does not create tuple, looking for first of pat is enough *)
      let vidfirst = List.hd (get_list_var p) in
      let lanneqm = try
        Env.find vidfirst mannoteq
      with
        | Not_found -> []
      in

      let ock = get_ock_from_var llocs p in
      mk_equation_model p e ~clock:ock lanneqm eq.eq_stateful ~loc:eq.eq_loc
    | _ -> failwith "Internal normalize error : Translated eqm equation should be in Eeq form"
  ) eq_acc in

  (* DEBUG
  Format.fprintf (Format.formatter_of_out_channel stdout) "eqm_acc = %a\n@?"
    Hept_printer.print_eq_model_list eqm_acc; *)

  (* Step 3 - updating the latency chain constraints *)
  (*  Normalization step might have introduce new local var in the middle of an old equation
    => We add these variables to the chain of latency *)
  let n_bm_annot = List.map (fun blannot -> match blannot.annm_desc with
    | Ann_latchain (latency, lchain) -> (* We need to add the inserted variable inside lchain *)
      convert_latency_chain vm_acc eqm_acc latency lchain
    | _ -> blannot
  ) bm.bm_annot in

  { bm with bm_local = llocs; bm_eqs = eqm_acc; bm_annot = n_bm_annot }, ([], [])



let contract funs context c =
  let ({ c_block = b } as c), void_context =
    Hept_mapfold.contract funs context c in
  (* Non-void context could mean lost equations *)
  assert (void_context=([],[]));
  let context, e_a = translate ExtValue ([],[]) None c.c_assume in
  let context, e_e =
    mapfold_right
      (fun o context ->
         let context, e = translate ExtValue context None o.o_exp in
	 context, { o with o_exp = e })
      c.c_objectives context in
  let local_context, e_a_loc = translate ExtValue ([],[]) None c.c_assume_loc in
  let local_context, e_e_loc = translate ExtValue local_context None c.c_enforce_loc in
  let (d_list, eq_list) = context in
  { c with
      c_assume = e_a;
      c_objectives = e_e;
      c_assume_loc = e_a_loc;
      c_enforce_loc = e_e_loc;
      c_block = { b with
                    b_local = d_list@b.b_local;
                    b_equs = eq_list@b.b_equs; }
  }, local_context

let node_dec nd =
  let funs = { defaults with block = block; block_model = block_model;
                eq = eq; eq_model = eq_model; contract = contract } in
  let nd, _ = Hept_mapfold.node_dec funs ([], []) nd in
  nd

let model_dec md =
  let funs = { defaults with block = block; block_model = block_model;
                eq = eq; eq_model = eq_model; contract = contract } in
  let md, _ = Hept_mapfold.model_dec funs ([], []) md in
  md


let program p =
  let funs = { defaults with block = block; block_model = block_model;
                eq = eq; eq_model = eq_model; contract = contract } in
  let p, _ = Hept_mapfold.program funs ([], []) p in
    p
