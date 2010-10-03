 (**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* Generic mapred over Obc Ast *)
open Misc
open Errors
open Global_mapfold
open Obc

type 'a obc_it_funs = {
  exp:        'a obc_it_funs -> 'a -> Obc.exp -> Obc.exp * 'a;
  edesc:      'a obc_it_funs -> 'a -> Obc.exp_desc -> Obc.exp_desc * 'a;
  lhs:        'a obc_it_funs -> 'a -> Obc.lhs -> Obc.lhs * 'a;
  lhsdesc:    'a obc_it_funs -> 'a -> Obc.lhs_desc -> Obc.lhs_desc * 'a;
  act:        'a obc_it_funs -> 'a -> Obc.act -> Obc.act * 'a;
  block:      'a obc_it_funs -> 'a -> Obc.block -> Obc.block * 'a;
  var_dec:    'a obc_it_funs -> 'a -> Obc.var_dec -> Obc.var_dec * 'a;
  var_decs:   'a obc_it_funs -> 'a -> Obc.var_dec list
                                   -> Obc.var_dec list * 'a;
  obj_dec:    'a obc_it_funs -> 'a -> Obc.obj_dec -> Obc.obj_dec * 'a;
  obj_decs:   'a obc_it_funs -> 'a -> Obc.obj_dec list
                                   -> Obc.obj_dec list * 'a;
  method_def: 'a obc_it_funs -> 'a -> Obc.method_def -> Obc.method_def * 'a;
  class_def:  'a obc_it_funs -> 'a -> Obc.class_def -> Obc.class_def * 'a;
  const_dec:  'a obc_it_funs -> 'a -> Obc.const_dec -> Obc.const_dec * 'a;
  type_dec:   'a obc_it_funs -> 'a -> Obc.type_dec -> Obc.type_dec * 'a;
  tdesc:      'a obc_it_funs -> 'a -> Obc.tdesc -> Obc.tdesc * 'a;
  program:    'a obc_it_funs -> 'a -> Obc.program -> Obc.program * 'a;
  global_funs:'a Global_mapfold.global_it_funs }


let rec exp_it funs acc e = funs.exp funs acc e
and exp funs acc e =
  let ed, acc = edesc_it funs acc e.e_desc in
  { e with e_desc = ed }, acc


and edesc_it funs acc ed =
  try funs.edesc funs acc ed
  with Fallback -> edesc funs acc ed
and edesc funs acc ed = match ed with
  | Elhs l ->
     let l, acc = lhs_it funs acc l in
        Elhs l, acc
  | Econst se ->
      let se, acc = static_exp_it funs.global_funs acc se in
        Econst se, acc
  | Eop (op, args) ->
       let args, acc = mapfold (exp_it funs) acc args in
         Eop (op, args), acc
  | Estruct(tyn, f_e_list) ->
      let aux acc (f,e) =
        let e, acc = exp_it funs acc e in
          (f,e), acc in
      let f_e_list, acc = mapfold aux acc f_e_list in
        Estruct(tyn, f_e_list), acc
  | Earray args ->
      let args, acc = mapfold (exp_it funs) acc args in
        Earray args, acc


and lhs_it funs acc l = funs.lhs funs acc l
and lhs funs acc l =
  let ld, acc = lhsdesc_it funs acc l.l_desc in
  { l with l_desc = ld }, acc


and lhsdesc_it funs acc ld =
  try funs.lhsdesc funs acc ld
  with Fallback -> lhsdesc funs acc ld
and lhsdesc funs acc ld = match ld with
  | Lvar x -> Lvar x, acc
  | Lmem x -> Lmem x, acc
  | Lfield(lhs, f) ->
      let lhs, acc = lhs_it funs acc lhs in
        Lfield(lhs, f), acc
  | Larray(lhs, e) ->
      let lhs, acc = lhs_it funs acc lhs in
      let e, acc = exp_it funs acc e in
        Larray(lhs, e), acc


and act_it funs acc a =
  try funs.act funs acc a
  with Fallback -> act funs acc a
and act funs acc a = match a with
  | Aassgn(lhs, e) ->
      let lhs, acc = lhs_it funs acc lhs in
      let e, acc = exp_it funs acc e in
        Aassgn(lhs, e), acc
  | Acall(lhs_list, obj, n, args) ->
      let lhs_list, acc = mapfold (lhs_it funs) acc lhs_list in
      let args, acc = mapfold (exp_it funs) acc args in
        Acall(lhs_list, obj, n, args), acc
  | Acase(x, c_b_list) ->
      let aux acc (c,b) =
        let b, acc = block_it funs acc b in
          (c,b), acc in
      let c_b_list, acc = mapfold aux acc c_b_list in
        Acase(x, c_b_list), acc
  | Afor(x, idx1, idx2, b) ->
      let idx1, acc = static_exp_it funs.global_funs acc idx1 in
      let idx2, acc = static_exp_it funs.global_funs acc idx2 in
      let b, acc = block_it funs acc b in
        Afor(x, idx1, idx2, b), acc

and block_it funs acc b = funs.block funs acc b
and block funs acc b =
  let b_locals, acc = var_decs_it funs acc b.b_locals in
  let b_body, acc = mapfold (act_it funs) acc b.b_body in
    { b with b_locals = b_locals; b_body = b_body }, acc

and var_dec_it funs acc vd = funs.var_dec funs acc vd
and var_dec funs acc vd =
  let v_type, acc = ty_it funs.global_funs acc vd.v_type in
  { vd with v_type = v_type }, acc

and var_decs_it funs acc vds = funs.var_decs funs acc vds
and var_decs funs acc vds = mapfold (var_dec_it funs) acc vds


and obj_dec_it funs acc od = funs.obj_dec funs acc od
and obj_dec funs acc od =
  let o_size, acc = optional_wacc
    (static_exp_it funs.global_funs) acc od.o_size in
  { od with o_size = o_size }, acc

and obj_decs_it funs acc ods = funs.obj_decs funs acc ods
and obj_decs funs acc ods = mapfold (obj_dec_it funs) acc ods


and method_def_it funs acc md = funs.method_def funs acc md
and method_def funs acc md =
  let m_inputs, acc = var_decs_it funs acc md.m_inputs in
  let m_outputs, acc = var_decs_it funs acc md.m_outputs in
  let m_body, acc = block_it funs acc md.m_body in
  { md with
      m_inputs = m_inputs; m_outputs = m_outputs; m_body = m_body }
  , acc


and class_def_it funs acc cd = funs.class_def funs acc cd
and class_def funs acc cd =
  let cd_mems, acc = var_decs_it funs acc cd.cd_mems in
  let cd_objs, acc = obj_decs_it funs acc cd.cd_objs in
  let cd_params, acc = mapfold (param_it funs.global_funs) acc cd.cd_params in
  let cd_methods, acc = mapfold (method_def_it funs) acc cd.cd_methods in
  { cd with
      cd_mems = cd_mems; cd_objs = cd_objs;
      cd_params = cd_params; cd_methods = cd_methods }
  , acc


and const_dec_it funs acc c = funs.const_dec funs acc c
and const_dec funs acc c =
  let ty, acc = ty_it funs.global_funs acc c.c_type in
  let se, acc = static_exp_it funs.global_funs acc c.c_value in
  { c with c_type = ty; c_value = se }, acc


and type_dec_it funs acc t = funs.type_dec funs acc t
and type_dec funs acc t =
  let tdesc, acc = tdesc_it funs acc t.t_desc in
    { t with t_desc = tdesc }, acc


and tdesc_it funs acc td =
  try funs.tdesc funs acc td
  with Fallback -> tdesc funs acc td
and tdesc funs acc td = match td with
  | Type_struct s ->
      let s, acc = structure_it funs.global_funs acc s in
        Type_struct s, acc
  | _ -> td, acc


and program_it funs acc p = funs.program funs acc p
and program funs acc p =
  let td_list, acc = mapfold (type_dec_it funs) acc p.p_types in
  let cd_list, acc = mapfold (const_dec_it funs) acc p.p_consts in
  let nd_list, acc = mapfold (class_def_it funs) acc p.p_defs in
  { p with p_types = td_list; p_consts = cd_list; p_defs = nd_list }, acc


let defaults = {
  lhs = lhs;
  lhsdesc = lhsdesc;
  exp = exp;
  edesc = edesc;
  act = act;
  block = block;
  var_dec = var_dec;
  var_decs = var_decs;
  obj_dec = obj_dec;
  obj_decs = obj_decs;
  method_def = method_def;
  class_def = class_def;
  const_dec = const_dec;
  type_dec = type_dec;
  tdesc = tdesc;
  program = program;
  global_funs = Global_mapfold.defaults }
