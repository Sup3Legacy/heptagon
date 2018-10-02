(* Identity equation contraction *)
(* When there is an equation "locVar1 = locVar2", where both are local variables,
     we replace all occurences of "locVar1" by "locVar2" *)

(* Author: Guillaume I *)

open Idents
open Heptagon
open Global_mapfold
open Hept_mapfold


let debug_copy_removal = false (* TODO DEBUG *)

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
  let rec remove_local_vars htblLocalVarContracted res lvardec = match lvardec with
    | [] -> res
    | vd::r -> if (Hashtbl.mem htblLocalVarContracted vd.v_ident) then
                remove_local_vars htblLocalVarContracted res r          (* Removed *)
               else
                remove_local_vars htblLocalVarContracted (vd::res) r
  in
  let rec remove_equation htblLocalVarContracted res lEqs =
    let rec aux_pattern htblLocalVarContracted eq r p =  match p with
      | Evarpat v ->
         if (Hashtbl.mem htblLocalVarContracted v) then
            remove_equation htblLocalVarContracted res r               (* Removed *)
          else remove_equation htblLocalVarContracted (eq::res) r
      | Etuplepat lp ->
         if ((List.length lp)=1) then
           aux_pattern htblLocalVarContracted eq r (List.hd lp)
         else
           remove_equation htblLocalVarContracted (eq::res) r
    in
    match lEqs with
    | [] -> res
    | eq::r -> begin
      match eq.eq_desc with
        | Eeq (p, _) -> aux_pattern htblLocalVarContracted eq r p
        | _ -> remove_equation htblLocalVarContracted (eq::res) r
      end
  in
  
  (* Removing the local declaration of nd *)
  let nlLocVar = remove_local_vars htblLocalVarContracted [] bl.b_local in
  
  (* Removing the equation of nd *)
  let nEqs = remove_equation htblLocalVarContracted [] bl.b_equs in
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
  (* In order to speed-up this function "is_local_var", we have 2 versions:
      One which looks at the local variables defs, and one whihc looks at the in/outputs defs *)
  let is_local_var_locals varId nd =
    let rec is_local_var_aux varId lvarLoc = match lvarLoc with
      | [] -> false
      | vd::r -> if (vd.v_ident=varId) then true
              else is_local_var_aux varId r
    in
    is_local_var_aux varId nd.n_block.b_local
  in
  let is_local_var_inouts varId nd =
    let rec is_local_var_aux varId lvarLoc = match lvarLoc with
      | [] -> false
      | vd::r -> if (vd.v_ident=varId) then true
              else is_local_var_aux varId r
    in
    if (is_local_var_aux varId nd.n_input) then false else
    not (is_local_var_aux varId nd.n_output)
  in

  let is_local_var =
    let bswitch = ( (List.length nd.n_block.b_local)
        < ((List.length nd.n_input) + (List.length nd.n_output)))
    in
    if (bswitch) then is_local_var_locals else is_local_var_inouts
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
  let rec propagate_substitution varId1 varId2 result l = match l with
    | [] -> result
    | (vl1, vl2)::rl -> if (vl2=varId1)
      then propagate_substitution varId1 varId2 ((vl1, varId2)::result) rl
      else propagate_substitution varId1 varId2 ((vl1, vl2)::result)   rl
  in
  let rec transitivityContrLocVar_aux prev_l next_l = match next_l with
    | [] -> prev_l
    | (varId1, varId2)::rl ->
      let nprev_l = propagate_substitution varId1 varId2 [] prev_l in
      let nrl = propagate_substitution varId1 varId2 [] rl in
      transitivityContrLocVar_aux ((varId1, varId2)::nprev_l) nrl
  in
  transitivityContrLocVar_aux [] lLocalVarContracted


(* Type of map whose key is a var_ident *)
module IdentMap = Map.Make (struct type t = var_ident let compare = compare end)


(* Much faster heuristic: we do front and back propagation until stability (ie, no change) *)
(* We use maps in order to speed up the computation *)
(* let transitivityContrLocVar_heuristic lLocalVarContracted = 
  let mLocVarContr = List.fold_left (fun macc (v1, v2) ->
      IdentMap.add v1 v2 macc
    ) IdentMap.empty lLocalVarContracted
  in

  let rec single_pass mnLocVar mLocVar = 
    (* TODO: how to do that? *)

    mnLocVar
  in

  (* TODO: use single_pass in one direction, then another until stability... :/ *)
  (* Need to use lists to do that, with a map built everytimes to do the quick searchs? :/ *)



  (* TODO *)
  transitivityContrLocVar lLocalVarContracted *)





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

        if (debug_copy_removal) then
          Format.fprintf (Format.formatter_of_out_channel stdout)
            "ping copyRemoval - localVarContracted obtained\n@?";

        (* Propagate the earlier substitution to the rest of the list *)
        let lLocalVarContracted = transitivityContrLocVar lLocalVarContracted in

        if (debug_copy_removal) then
          Format.fprintf (Format.formatter_of_out_channel stdout)
            "ping copyRemoval - transitivity done\n@?";
        
        (* TODO DEBUG
        print_lLocalVarContracted (Format.formatter_of_out_channel stdout) lLocalVarContracted; *)
        
        let nd = contractLocalVars nd lLocalVarContracted in

        Pnode nd
      | _ -> pdesc
    ) p.p_desc in
  { p with p_desc = npdesc }


