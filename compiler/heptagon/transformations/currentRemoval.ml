
open Signature
open Heptagon
open Hept_utils


(* Remove all occurence of "current" in the program *)
(* Author : Guillaume I *)

exception TypeDefForClockUnespected


(* Phase 1 (edesc) : iterate over the whole program and replace the current
    by fresh variables. Also log the association "fresh var, current_clk, current_sub_expr" *)
let edesc funs acc ed = match ed with
  | Ecurrent (constr, id, e) ->
    let fresh_ident = Idents.gen_var "currRem" "var" in
    Evar(fresh_ident), (fresh_ident, (constr, id, e) )::acc
  | _ -> Hept_mapfold.edesc funs acc ed (* Default recursion case *)


(* Phase 2 (node_dec): use the logs to create the new local variables *)
let flatten_type_def tydesc = match tydesc with
  | Tabstract | Tstruct _ -> raise TypeDefForClockUnespected
  | Talias _ -> []				(* No recursion possible? (ex: calling another enum type?) *)
  | Tenum l_c_name -> l_c_name

let block funs acc bl =
  let (bl,logs) = Hept_mapfold.block funs acc bl in
  
  let bl = List.fold_left
    (fun bl elemLog ->
      (* Given an equation " ... = ... current(consCk(idCk), subExpr)", we build the following objects: *)
      (* New var/eq: "currRem_var = merge idCk (consCk -> subExpr when consCk) ( ??? -> pre(currRem_var))" *)
      (* The "???" constructors are the alternatives versions of the constructor *)
      
      let (ident, (consCk, idCk, subExpr) ) = elemLog in
      let ck = Clocks.Con (Clocks.Cbase, consCk, idCk) in (* Not sure about the Cbase *)
      
      (* Check the global environment for the type definition of the clock containing the constructor consCk *)
      (* There is a sub-case for when the clock is boolean*)
      let l_constr =
        if ((consCk=Initial.ptrue) || (consCk = Initial.pfalse)) then [Initial.ptrue; Initial.pfalse] else
        begin
          let tydef_name = Modules.find_constrs consCk in
          (*Needed? => open_module tydef_name.qual;*)
          let tydef = Modules.find_type tydef_name in
          flatten_type_def tydef
        end in
      let l_constr_br_false = List.filter (fun elem -> elem<>consCk) l_constr in
      
      let n_var_dec = mk_var_dec ~clock:ck ident subExpr.e_ty ~linearity:Linearity.Ltop in
      
      let dWhen_merge_true = Ewhen (subExpr, consCk, idCk) in
      let branch_merge_true = mk_exp dWhen_merge_true Types.Tinvalid ~linearity:Linearity.Ltop in (* We are before the typing *)
      
      (* Building all the false branches *)
      let l_branch_merge_false = List.map
        (fun constr_false ->
          let dVar_merge_false = Evar ident in
          let expVar_merge_false = mk_exp dVar_merge_false Types.Tinvalid ~linearity:Linearity.Ltop in
          
          let dPre_merge_false = Epre (None, expVar_merge_false) in
          let exprPre_merge_false = mk_exp dPre_merge_false Types.Tinvalid ~linearity:Linearity.Ltop in
          
          let dWhen_merge_false =  Ewhen (exprPre_merge_false, constr_false , idCk) in
          let branch_merge_false = mk_exp dWhen_merge_false Types.Tinvalid ~linearity:Linearity.Ltop in
          (constr_false, branch_merge_false)
        ) l_constr_br_false in
      
      let deq_rhs = Emerge (idCk, (consCk, branch_merge_true) :: l_branch_merge_false ) in
      let eq_rhs = mk_exp deq_rhs Types.Tinvalid ~linearity:Linearity.Ltop in
      
      let n_eq = mk_equation (Eeq (Evarpat ident, eq_rhs)) in
      
      { bl with b_local = n_var_dec::bl.b_local; b_equs = n_eq::bl.b_equs }
    ) bl logs in
  bl, []

(* Note: other ideas I had to solve this problem *)
(* 1) Iterate over all complementary constructors ? (how to get them?) *)
(* ====> we can get them through the environment (because they are qualified) :) *)
(* 2) Allow negation in the constructor side? (heavy modification of the compiler) => how to generate code? *)
(* 3) Build a new constructor for the negation? (unification issue?) *)
(* 4) Option "default" for the merge? => does it work with clock calculus? (heavy modif of the compiler) *)
(* Whenot = Ewhen( ..., pfalse, ...) *)

(* Main function *)
let program p =
  let funs = { Hept_mapfold.defaults with edesc = edesc; block = block} in
  let (p, _) = Hept_mapfold.program funs [] p in
  p


