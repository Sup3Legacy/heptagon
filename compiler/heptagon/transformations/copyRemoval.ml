(* Identity equation contraction *)
(* When there is an equation "locVar1 = locVar2", where both are local variables,
     we replace all occurences of "locVar1" by "locVar2" *)

(* Author: Guillaume I *)

open Heptagon
open Global_mapfold
open Hept_mapfold

(* Contract a local variable "var1" in the program, by replacing its occurence by "var2" *)
let eqdesc_contract funs acc eqdesc = match eqdesc with
  | Eeq (p, exp) ->
    let exp, acc = funs.exp funs acc exp in
    Eeq(p, exp), acc
  | _ -> Hept_mapfold.eqdesc funs acc eqdesc

let edesc_contract funs htblLocalVarContracted edesc = match edesc with
  | Evar var1 -> begin
    try
      let var2 = Hashtbl.find htblLocalVarContracted var1 in
      Evar var2, htblLocalVarContracted
    with Not_found -> Evar var1, htblLocalVarContracted
    end
  | _ -> Hept_mapfold.edesc funs htblLocalVarContracted edesc

(* let var_ident_contract _ htblLocalVarContracted vi =
  try
    let var2 = Hashtbl.find htblLocalVarContracted vi in
    var2, htblLocalVarContracted
  with Not_found -> vi, htblLocalVarContracted *)


(* Remove the equation defining "var" from the list of equation of 
      the node declaration "nd" + its declaration (as a local var) *)
let remove_variables htblLocalVarContracted bl =
  let rec remove_local_vars htblLocalVarContracted lvardec = match lvardec with
    | [] -> []
    | vd::r -> if (Hashtbl.mem htblLocalVarContracted vd.v_ident) then
                  remove_local_vars htblLocalVarContracted r          (* Removed *)
               else vd::(remove_local_vars htblLocalVarContracted r)
  in
  let rec remove_equation htblLocalVarContracted lEqs =
    let rec aux_pattern htblLocalVarContracted eq r p =  match p with
      | Evarpat v ->
         if (Hashtbl.mem htblLocalVarContracted v) then
            remove_equation htblLocalVarContracted r               (* Removed *)
          else eq::(remove_equation htblLocalVarContracted r)
      | Etuplepat lp ->
         if ((List.length lp)=1) then
           aux_pattern htblLocalVarContracted eq r (List.hd lp)
         else
           eq::(remove_equation htblLocalVarContracted r)
    in
    match lEqs with
    | [] -> []
    | eq::r -> begin
      match eq.eq_desc with
        | Eeq (p, _) -> aux_pattern htblLocalVarContracted eq r p
        | _ -> eq::(remove_equation htblLocalVarContracted r)
      end
  in
  
  (* Removing the local declaration of nd *)
  let nlLocVar = remove_local_vars htblLocalVarContracted bl.b_local in
  
  (* Removing the equation of nd *)
  let nEqs = remove_equation htblLocalVarContracted bl.b_equs in
  let nBl = Hept_utils.mk_block ~stateful:bl.b_stateful
          ~defnames:bl.b_defnames ~locals:nlLocVar nEqs in
  nBl


let contractLocalVars nd lLocalVarContracted =
  let list_to_htbl l =
    let h = Hashtbl.create (List.length l) in
    List.iter (fun (var1, var2) -> Hashtbl.add h var1 var2) l;
    h
  in

  (* Can be done in parallel instead of in sequence *)
  let htblLocalVarContracted = list_to_htbl lLocalVarContracted in
  let funs = {Hept_mapfold.defaults with
                       eqdesc = eqdesc_contract;
                       edesc = edesc_contract;
                       (* global_funs = {Global_mapfold.defaults with var_ident = var_ident_contract } *)
            } in
  let nd, _ = Hept_mapfold.node_dec funs htblLocalVarContracted nd in
  let nbl = remove_variables htblLocalVarContracted nd.n_block in
  {nd with n_block = nbl }


(* ======================================================================= *)

(* Identify the local variables to be contracted *)
(* Returns a list of (var_ident * var_ident) = (to_be_substituted, replacement) *)
let getContractedLocalVar nd =
  let is_local_var varId nd =
    let rec is_local_var_aux varId lvarLoc = match lvarLoc with
      | [] -> false
      | vd::r -> if (vd.v_ident=varId) then true
              else is_local_var_aux varId r
    in
    is_local_var_aux varId nd.n_block.b_local
  in
  
  let lcontrInfo = List.fold_left
    (fun acc eq -> match eq.eq_desc with
      | Eeq (p, rhs) ->
        begin
        (* Criterions:
           (i) p must be a single "Evarpat varId"
           (ii) This varId must be a local variable
           (iii) rhs must be a single "Evar of varId" *)
        match p with
          | Evarpat varId1 ->
            if (not (is_local_var varId1 nd)) then acc else
            begin
            match rhs.e_desc with
              | Evar varId2 -> (varId1, varId2) :: acc
              | _ -> acc
            end
          | _ -> acc
        end
      | _ -> acc
    ) [] nd.n_block.b_equs in
  lcontrInfo



(* Becausethe previously list might have entries like (c,a) (d,c) (e,c)
   where "c" might disappear after the first substitution, we need to propagate 
     this substitution to the later entries *)
let transitivityContrLocVar lLocalVarContracted =
  (* Propagation of a single substitution *)
  let rec propagate_substitution varId1 varId2 l = match l with
    | [] -> []
    | (vl1, vl2)::rl -> if (vl2=varId1)
      then (vl1,varId2)::(propagate_substitution varId1 varId2 rl)
      else (vl1, vl2)::(propagate_substitution varId1 varId2 rl)
  in
  let rec transitivityContrLocVar prev_l next_l = match next_l with
    | [] -> prev_l
    | (varId1, varId2)::rl ->
      let nprev_l = propagate_substitution varId1 varId2 prev_l in
      let nrl = propagate_substitution varId1 varId2 rl in
      transitivityContrLocVar ((varId1, varId2)::nprev_l) nrl
  in
  transitivityContrLocVar [] lLocalVarContracted


(* ======================================================================= *)

(* DEBUG function *)
let print_lLocalVarContracted ff lLocalVarContracted =
  let rec print_lLocalVarContracted_aux ff l = match l with
    | [] -> ()
    | (varId1,varId2)::t -> Format.fprintf ff "(%a, %a); "
           Global_printer.print_ident varId1  Global_printer.print_ident varId2;
      print_lLocalVarContracted_aux ff t
  in
  Format.fprintf ff "lLocalVarContracted = [";
  print_lLocalVarContracted_aux ff lLocalVarContracted;
  Format.fprintf ff "]\n@?"

(* Main function *)
let program p =
  let npdesc = List.map
    (fun pdesc -> match pdesc with
      | Pnode nd ->
        let lLocalVarContracted = getContractedLocalVar nd in
        (* Propagate the earlier substitution to the rest of the list *)
        let lLocalVarContracted = transitivityContrLocVar lLocalVarContracted in
        
        (* TODO DEBUG
        print_lLocalVarContracted (Format.formatter_of_out_channel stdout) lLocalVarContracted; *)
        
        let nd = contractLocalVars nd lLocalVarContracted in

        Pnode nd
      | _ -> pdesc
    ) p.p_desc in
  { p with p_desc = npdesc }

(* TODO: copy equation on outputs to be managed *)

