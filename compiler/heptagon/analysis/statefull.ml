(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* Checks that a node declared stateless is stateless, and set possible nodes as stateless. *)
open Names
open Location
open Signature
open Modules
open Heptagon
open Hept_mapfold

type error =
  | Eshould_be_a_node
  | Eexp_should_be_stateless

let message loc kind =
  begin match kind with
    | Eshould_be_a_node ->
        Format.eprintf "%aThis node is stateful \
                       but was declared stateless.@."
          print_location loc
    | Eexp_should_be_stateless ->
        Format.eprintf "%aThis expression should be stateless.@."
          print_location loc
  end;
  raise Errors.Error


let stateful_mapfold f acc l =
  let map_or (l,acc) e =
    let e,acc' = f false e in
    e::l, acc or acc'
  in
  let l,acc = List.fold_left map_or ([],acc) l in
  List.rev l, acc


let last _ stateful l = match l with
  | Var -> l, stateful
  | Last _ -> l, true

(* Returns whether the exp is stateful.
   Replaces node calls with the correct Efun or Enode depending on the node signature. *)
let edesc funs stateful ed =
  let ed, stateful = Hept_mapfold.edesc funs stateful ed in
    match ed with
      | Efby _ | Epre _ -> ed, true
      | Eapp({ a_op = Earrow }, _, _) -> ed, true
      | Eapp({ a_op = (Enode f | Efun f) } as app, e_list, r) ->
          let ty_desc = find_value f in
          let op = if ty_desc.node_stateful then Enode f else Efun f in
          Eapp({ app with a_op = op }, e_list, r), ty_desc.node_stateful or stateful
      | _ -> ed, stateful

(* Automatons have an hidden state whatever *)
let eqdesc funs stateful eqd =
  let eqd, stateful = Hept_mapfold.eqdesc funs stateful eqd in
  let is_automaton = match eqd with | Eautomaton _ -> true | _ -> false in
  eqd, stateful or is_automaton

(* update eq_stateful field *)
let eq funs acc eq =
  let eq, stateful = Hept_mapfold.eq funs false eq in
    { eq with eq_stateful = stateful }, stateful or acc

(* update b_stateful field *)
let block funs acc b =
  let b, stateful = Hept_mapfold.block funs false b in
    { b with b_stateful = stateful }, acc or stateful

(* Strong preemption should be decided with stateles expressions *)
let escape_unless funs acc esc =
  let esc, stateful = Hept_mapfold.escape funs false esc in
    if stateful then
      message esc.e_cond.e_loc Eexp_should_be_stateless;
    esc, acc or stateful

(* Present conditions should be stateless *)
let present_handler funs acc ph =
  let p_cond, stateful = Hept_mapfold.exp_it funs false ph.p_cond in
    if stateful then
      message ph.p_cond.e_loc Eexp_should_be_stateless;
  let p_block, acc = Hept_mapfold.block_it funs acc ph.p_block in
    { ph with p_cond = p_cond; p_block = p_block }, acc


(* Funs with states are rejected, nodes without state are set as funs *)
let node_dec funs _ n =
  Idents.enter_node n.n_name;
  let n, stateful = Hept_mapfold.node_dec funs false n in
  if stateful & (not n.n_stateful) then message n.n_loc Eshould_be_a_node;
  if not stateful & n.n_stateful (* update the global env if stateful is not necessary *)
  then Modules.replace_value n.n_name
         { (Modules.find_value n.n_name) with Signature.node_stateful = false };
  { n with n_stateful = stateful }, false (* set stateful only if needed *)

let funs =
  { Hept_mapfold.defaults with
      edesc = edesc;
      escape_unless = escape_unless;
      present_handler = present_handler;
      eqdesc = eqdesc;
      last = last;
      eq = eq;
      block = block;
      node_dec = node_dec; }

let program p =
  let p, _ = Hept_mapfold.program_it funs false p in
  p
