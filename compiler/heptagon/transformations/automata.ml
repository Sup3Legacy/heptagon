(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* removing automata statements *)

open Misc
open Types
open Names
open Idents
open Heptagon
open Hept_mapfold
open Initial

let mk_var_exp n ty =
  mk_exp (Evar n) ty

let mk_pair e1 e2 =
  mk_exp (mk_op_app Etuple [e1;e2]) (Tprod [e1.e_ty; e2.e_ty])

let mk_reset_equation eq_list e =
  mk_equation (Ereset (mk_block eq_list, e))

let mk_switch_equation e l =
  mk_equation (Eswitch (e, l))

let mk_exp_fby_false e =
  mk_exp (Epre (Some (mk_static_bool false), e))
    (Tid Initial.pbool)

let mk_constructor constr ty =
  mk_static_exp ~ty:ty (Sconstructor constr)

(* Be sure that [initial] is of the right type [e.e_ty] before using this *)
let mk_exp_fby_state initial e =
  { e with e_desc = Epre (Some (mk_constructor initial e.e_ty), e) }

(* the list of enumerated types introduced to represent states *)
let state_type_dec_list = ref []

let intro_type states =
  let list env = NamesEnv.fold (fun _ state l -> state :: l) env [] in
  let n = gen_symbol () in
  let state_type = "st" ^ n in
  state_type_dec_list :=
    (mk_type_dec state_type (Type_enum (list states))) :: !state_type_dec_list;
  Name(state_type)

(** Allows to classify an automaton :
    Moore automatons doesn't have strong transitions,
    Mealy automatons may have some. *)
let no_strong_transition state_handlers =
  let handler no_strong { s_unless = l } = no_strong & (l = []) in
  List.fold_left handler true state_handlers


let translate_automaton v eq_list handlers =
  let states =
    let suffix = gen_symbol () in
    List.fold_left
      (fun env { s_state = n } -> NamesEnv.add n (n ^ suffix) env)
      NamesEnv.empty handlers in

  let statetype = intro_type states in
  let tstatetype = Tid statetype in
  let initial = Name(NamesEnv.find (List.hd handlers).s_state states) in

  let statename = Idents.fresh "s" in
  let next_statename = Idents.fresh "ns" in
  let resetname = Idents.fresh "r" in
  let next_resetname = Idents.fresh "nr" in
  let pre_next_resetname = Idents.fresh "pnr" in

  let name n = Name(NamesEnv.find n states) in
  let state n =
    mk_exp (Econst (mk_constructor (name n) tstatetype)) tstatetype in
  let statevar n = mk_var_exp n tstatetype in
  let boolvar n = mk_var_exp n (Tid Initial.pbool) in

  let escapes n s rcont =
    let escape { e_cond = e; e_reset = r; e_next_state = n } cont =
      mk_ifthenelse e (mk_pair (state n) (if r then dtrue else dfalse)) cont
    in
    List.fold_right escape s (mk_pair (state n) rcont)
  in

  let strong { s_state = n; s_unless = su } =
    let defnames = Env.add resetname (Tid Initial.pbool) Env.empty in
    let defnames = Env.add statename tstatetype defnames in
    let st_eq = mk_simple_equation
      (Etuplepat[Evarpat(statename); Evarpat(resetname)])
      (escapes n su (boolvar pre_next_resetname)) in
    mk_block ~defnames:defnames [mk_reset_equation [st_eq]
                                   (boolvar pre_next_resetname)]
  in

  let weak { s_state = n; s_block = b; s_until = su } =
    let defnames = Env.add next_resetname (Tid Initial.pbool) b.b_defnames in
    let defnames = Env.add next_statename tstatetype defnames in
    let ns_eq = mk_simple_equation
      (Etuplepat[Evarpat(next_statename); Evarpat(next_resetname)])
      (escapes n su dfalse) in
    { b with b_equs =
        [mk_reset_equation (ns_eq::b.b_equs) (boolvar resetname)];
        (* (or_op (boolvar pre_next_resetname) (boolvar resetname))]; *)
        b_defnames = defnames;
    }
  in

  let v =
    (mk_var_dec next_statename (Tid(statetype))) ::
      (mk_var_dec resetname (Tid Initial.pbool)) ::
      (mk_var_dec next_resetname (Tid Initial.pbool)) ::
      (mk_var_dec pre_next_resetname (Tid Initial.pbool)) :: v in
  if no_strong_transition handlers
  then (* Only weak transitions : a Moore automaton. *)
    let switch_e = mk_exp_fby_state initial (statevar next_statename) in
    let switch_handlers =
      List.map (fun ({ s_state = n } as case) ->
                  { w_name = name n; w_block = weak case })
               handlers in
    let switch_eq = mk_switch_equation switch_e switch_handlers in
    let nr_eq =
      mk_simple_equation (Evarpat pre_next_resetname)
                         (mk_exp_fby_false (boolvar (next_resetname))) in
    let pnr_eq =
      mk_simple_equation (Evarpat resetname) (boolvar pre_next_resetname) in
    v, switch_eq :: nr_eq :: pnr_eq :: eq_list
  else (* General case,
          two switch to generate statename variable used and defined *)
    let v = (mk_var_dec statename (Tid statetype)) :: v in
    let ns_switch_e = mk_exp_fby_state initial (statevar next_statename) in
    let ns_switch_handlers =
      List.map (fun ({ s_state = n } as case) ->
                  { w_name = name n; w_block = strong case })
               handlers in
    let ns_switch_eq = mk_switch_equation ns_switch_e ns_switch_handlers in
    let switch_e = statevar statename in
    let switch_handlers =
      List.map (fun ({ s_state = n } as case) ->
                  { w_name = name n; w_block = weak case })
               handlers in
    let switch_eq = mk_switch_equation switch_e switch_handlers in
    let pnr_eq =
      mk_simple_equation (Evarpat pre_next_resetname)
                         (mk_exp_fby_false (boolvar (next_resetname))) in
    v, ns_switch_eq :: switch_eq :: pnr_eq :: eq_list

let rec eq funs (v, eq_list) eq =
  let eq, (v, eq_list) = Hept_mapfold.eq funs (v, eq_list) eq in
    match eq.eq_desc with
      | Eautomaton state_handlers ->
          eq, translate_automaton v eq_list state_handlers
      | _ -> eq, (v, eq::eq_list)

let block funs acc b =
  let b, (v, acc_eq_list) = Hept_mapfold.block funs ([], []) b in
    { b with b_local = v @ b.b_local; b_equs = acc_eq_list }, acc

let program p =
  let funs = { Hept_mapfold.defaults
               with eq = eq; block = block } in
  let p, _ = Hept_mapfold.program_it funs ([],[]) p in
    { p with p_types = !state_type_dec_list @ p.p_types }
