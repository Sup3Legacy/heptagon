
(* Transformation which breaks the tuple:
 "(Var1, Var2, ..., VarN) = (exp1, ... , expN)"
	=> Var1 = exp1 / ... / VarN = expN

  Tuple might be added from HE expansion in particular (ex: sequenceur management)
	*)
(* Author: Guillaume I *)

open Heptagon
open Hept_utils

exception Equation_not_in_Eeq_form

let get_lhs_rhs_eq e = match e.eq_desc with
  | Eeq (lhs, rhs) -> (lhs, rhs)
  | _ -> raise Equation_not_in_Eeq_form

let rec get_list_vid plhs = match plhs with
  | Etuplepat pl -> List.fold_left (fun acc p1 -> acc@(get_list_vid p1)) [] pl
  | Evarpat vid -> vid::[]


(* ============================================================================= *)


(* Core function *)
let rec break_tuple_leq lres leq = match leq with
  | [] -> lres
  | eq::t ->
  let (plhs, erhs) = get_lhs_rhs_eq eq in
  let lvid = get_list_vid plhs in

  (* If no tuple is produced => skip *)
  if (List.length lvid=1) then break_tuple_leq (eq::lres) t else

  (* Is the rhs in tuple form? *)
  match erhs.e_desc with
  | Eapp (a, lsexp, _) -> begin
    if (a.a_op!=Etuple) then break_tuple_leq (eq::lres) t else (

    (* We have a tuple => breaking it! *)
    assert((List.length lsexp) == (List.length lvid));

    let nlbrkeq = List.map2 (fun vid sexp ->
      let plhsbrk = Evarpat vid in
      let erhsbrk = sexp in
      Hept_utils.mk_equation (Eeq (plhsbrk,erhsbrk))
    ) lvid lsexp in

    let nlres = List.rev_append nlbrkeq lres in
    break_tuple_leq nlres t
    )
    end
  | _ -> break_tuple_leq (eq::lres) t 


(* ============================================================================= *)

(* AST management *)
let block bl =
  let nleq = break_tuple_leq [] bl.b_equs in
  { bl with b_equs = nleq }

let node nd =
  let nbl = block nd.n_block in
  { nd with n_block = nbl }

let program p =
  let nlpdesc = List.map
    (fun pdesc -> match pdesc with
      | Pnode n -> Pnode (node n)
      | _ -> pdesc
    ) p.p_desc in
  { p with p_desc = nlpdesc }
