(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* removing reset statements *)

(* REQUIRES automaton stateful present *)

open Misc
open Heptagon
open Hept_utils
open Signature

(* e1 -> e2 is translated into if (true fby false) then e1 else e2 *)
(* fby are translated to pre *)
(* Remove reset blocks by marking node calls and fby
     with corresponding reset condition *)


let fresh () = Idents.gen_var "reset" ~reset:true "reset"

(* get e and return r, var_dec_r, r = e *)
let reset_var_from_exp e = match e with
| {e_desc = Evar _ } -> e,[],[]
| _ ->
  let r = fresh() in
  { e with e_desc = Evar r },
  [mk_var_dec r (Tid Initial.pbool) Linearity.Ltop],
  [mk_equation (Eeq(Evarpat r, e))]

(** Merge two reset conditions *)
let merge_resets res1 res2 = res1@res2

let init loc =
  mk_exp (Efby (Some(dtrue),[],dfalse,[]))
    ~loc:loc (Tid Initial.pbool) Linearity.Ltop


(** Keep whenever possible the initialization value *)
let default e =
  match e.e_desc with
    | Econst c -> Some c
    | _ -> None


let edesc funs ((res,_) as acc) ed = match ed with
    | Efby (e1, p, e2, c) ->
      (* reset c is added only to the register, not his arguments.*)
        let e1,_ = optional_wacc (Hept_mapfold.exp_it funs) acc e1 in
        let e2,_ = Hept_mapfold.exp_it funs acc e2 in
        let c,_ = mapfold (Hept_mapfold.exp_it funs) acc c in
        let res = merge_resets res c in
        Efby (e1, p, e2, res), acc
    | Eapp({ a_op = Earrow }, [e1;e2], c) ->
        let e1,_ = Hept_mapfold.exp_it funs acc e1 in
        let e2,_ = Hept_mapfold.exp_it funs acc e2 in
        let c,_ = mapfold (Hept_mapfold.exp_it funs) acc c in
        let res = merge_resets res c in
        (match res, e1, e2 with
         (*optimize 4 -> (0 fby e)  in  4 fby e *)
         | [], {e_desc = Econst _}, {e_desc = Efby(_,[],e3,c)} ->
            Efby(Some(e1),[],e3,c), acc
         | _ ->
            let cond_init, acc = Hept_mapfold.exp_it funs acc (init e2.e_loc) in
            mk_op_app Eifthenelse [cond_init; e1; e2], acc)
    | Eapp({ a_op = Enode _ } as op, e_list, re) ->
        let args,_ = mapfold (Hept_mapfold.exp_it funs) acc e_list in
        let re,_ = mapfold (Hept_mapfold.exp_it funs) acc re in
        Eapp(op, args, merge_resets res re), acc
    | Eiterator(it, ({ a_op = Enode _ } as op), n, pe_list, e_list, re) ->
        let pargs,_ = mapfold (Hept_mapfold.exp_it funs) acc pe_list in
        let args,_ = mapfold (Hept_mapfold.exp_it funs) acc e_list in
        let re,_ = mapfold (Hept_mapfold.exp_it funs) acc re in
        Eiterator(it, op, n, pargs, args, merge_resets res re), acc
    | Eapp({ a_op = Efun _ } as op, e_list, _) ->
        let args,_ = mapfold (Hept_mapfold.exp_it funs) acc e_list in
        Eapp(op, args, []), acc (* funs don't need resets *)
    | Eiterator(it, ({ a_op = Efun _ } as op), n, pe_list, e_list, _) ->
        let pargs,_ = mapfold (Hept_mapfold.exp_it funs) acc pe_list in
        let args,_ = mapfold (Hept_mapfold.exp_it funs) acc e_list in
        Eiterator(it, op, n, pargs, args, []), acc (* funs don't need resets *)
    | _ -> raise Errors.Fallback

let eq funs (res,_) eq =
  Hept_mapfold.eq funs (res,eq.eq_stateful) eq

let block funs (res,_) b =
  Hept_mapfold.block funs (res,b.b_stateful) b

(* Transform reset blocks in blocks with reseted exps,
   create a var to store the reset condition evaluation if not already a var. *)
let eqdesc funs (res,stateful) = function
  | Ereset(b, ({ e_desc = Evar _ } as e)) ->
        let r = if stateful then merge_resets [e] res else res in
        let b, _ = Hept_mapfold.block_it funs (r,stateful) b in
        Eblock(b), (res,stateful)
  | Ereset(b, e) ->
      if stateful then (
        let e, _ = Hept_mapfold.exp_it funs (res,stateful) e in
        let e, vd, eq = reset_var_from_exp e in
        let r = merge_resets [e] res in
        let b, _ = Hept_mapfold.block_it funs (r,stateful) b in
        let b = { b with b_equs = eq@b.b_equs; b_local = vd@b.b_local; b_stateful = true } in
        Eblock(b), (res,stateful))
      else ( (* recursive call to remove useless resets *)
        let b, _ = Hept_mapfold.block_it funs (res,stateful) b in
        Eblock(b), (res,stateful))
  | Eautomaton _ | Epresent _ ->
      Format.eprintf "[reset] should be done after [automaton present]";
      assert false
  | _ -> raise Errors.Fallback


let funs = { Hept_mapfold.defaults with Hept_mapfold.eq = eq;
                                        Hept_mapfold.block = block;
                                        Hept_mapfold.eqdesc = eqdesc;
                                        Hept_mapfold.edesc = edesc }

let program p =
  let p, _ = Hept_mapfold.program_it funs ([],true) p in
  p
