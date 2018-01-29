(* Array destruction transformation *)

(* Author: Guillaume I *)

(* Criterion of which array should we destruct:
   - Must be a local variable
   - Must not have an associated Linearity (i.e., a specific reused memory location for the array)
   - Must NOT be the argument/output of a function/node call
   - Must only used with a Eselect, with a constant inside
   
  Substitution performed:
   - For each cell of the array A, introduce a new local variable A_k
   - On the rhs, replace A[k] by A_k
   - On the lhs, replace the definition of A as a tuple, by size(A) equations (one per elements)
  *)

open Misc
open Names
open Idents
open Types
open Heptagon
open Hept_mapfold

(* Determine if a type is an array of constant size (or a tuple) *)
let get_array_const_size ty = match ty with
  | Tarray (tyarr, size) -> begin
    match size.se_desc with
      | Sint i -> Some (i, tyarr)             (* Array of constant size detected! *)
      | _ -> None
    end
  | Tprod _ -> None                 (* TODO: tuple management ? *)
  | Tid _ -> None                   (* Note: alias management managed previously *)
  | Tclasstype _ | Tinvalid -> None



(* Type of map whose key is a var_ident *)
module IdentMap = Map.Make (struct type t = var_ident let compare = compare end)


(* Substitution part of the transformation *)
(* acc = new list of equations *)

(* A[k] -> A_k if A is a valid to-be-destroyed array *)
let edesc_subst_array mArrayVar funs acc ed = match ed with
  | Eapp (ap, lsexpr, _) -> begin
     match ap.a_op with
       | Eselect ->          (* We have a A[i] here ! *)
         begin
         let expArr = assert_1 lsexpr in
         let stExpIndex = assert_1 ap.a_params in
         
         let arrId = match expArr.e_desc with
           | Evar vId -> vId
           | _ -> failwith "ArrayDestruct: subexpression of a Eselect is not a variable."
         in
         
         (* If the array is not to be destroyed... *)
         if (not (IdentMap.mem arrId mArrayVar)) then
           Hept_mapfold.edesc funs acc ed
         else
         
         let index = match stExpIndex.se_desc with
           | Sint i -> i
           | _ -> failwith "ArrayDestruct: parameter of a Eselect is not an integer."
         in
         (* Getting the associated local variable *)
         try
           let lAssoc = IdentMap.find arrId mArrayVar in
           let varDecl = List.assoc index lAssoc in
           (Evar varDecl.v_ident), acc
         with Not_found ->
           failwith ("ArrayDestruct: " ^ (Idents.name arrId) ^
           "[" ^ (string_of_int index) ^ "] does not have a corresponding entry in the map.")
         end
       | _ -> Hept_mapfold.edesc funs acc ed
    end
  | _ -> Hept_mapfold.edesc funs acc ed


let create_new_eq_from_tuple vidLhs mArrayVar lexp =
  let rec create_new_eq_from_tuple_aux lvlhs lexp = match (lvlhs, lexp) with
    | ([],[]) -> []
    | (vlhs::r_lvlhs, exp::r_lexp) -> 
      let nEqs = create_new_eq_from_tuple_aux r_lvlhs r_lexp in
      let neq = Hept_utils.mk_equation (Eeq (Evarpat vlhs, exp)) in
      neq::nEqs
    | _ -> failwith "internal error: lvlhs and lexp have different lengths."
  in
  let lkVar = IdentMap.find vidLhs mArrayVar in
  
  (* We use the "k" to build the list in the right order *)
  let arrTemp = Array.make (List.length lkVar) None in
  let arrTemp = List.fold_left
    (fun acc (k,vd) ->
      let kAdapted = if (!Compiler_options.safran_handling) then k-1 else k in
      Array.set acc kAdapted (Some vd);
      acc
    )
    arrTemp lkVar in
  let lvlhs = Array.to_list arrTemp in
  let lvlhs = List.map (fun opt -> match opt with
    | None -> failwith "internal error: no hole in that array should happens"
    | Some vd -> vd.v_ident
  ) lvlhs in
  create_new_eq_from_tuple_aux lvlhs lexp


let rec duplicate_k_times exp k =
  assert(k>=0);
  match k with
  | 0 -> []
  | _ -> exp::(duplicate_k_times exp (k-1))


(* A = [ .... ] => A_0 = ... / A_1 = ... / ... *)
let eq_subst_array mArrayVar funs acc eq =
  (* Recursion first, to manage the A[i] on the rhs *)
  let eq, acc = Hept_mapfold.eq funs acc eq in
  match eq.eq_desc with
    | Eeq (lhs, rhs) -> begin
      (* Detect if the equation is of the form "A = [ .... ]" where A is an array *)
      match lhs with
       | Etuplepat _ -> eq, eq::acc
       | Evarpat vidLhs ->
         if (IdentMap.mem vidLhs mArrayVar) then begin
           (* We have an array on the left (vidLhs)
              => we must have a tuple / Sarray_power or Stuple or Sarray on the right *)
           match rhs.e_desc with
             | Eapp (ap, lexp, _) when (ap.a_op=Etuple || ap.a_op=Earray) ->
                 eq, (create_new_eq_from_tuple vidLhs mArrayVar lexp)@acc
             | Econst sexpRhs -> begin match sexpRhs.se_desc with
               | Sarray lsexp | Stuple lsexp ->
                 let nlexp = List.map
                    (fun stexp -> Hept_utils.mk_exp (Econst stexp) (* ~level_ck:rhs.e_level_ck *)
                                     rhs.e_ty ~linearity:rhs.e_linearity 
                    ) lsexp in
                 eq, (create_new_eq_from_tuple vidLhs mArrayVar nlexp)@acc
               | Sarray_power (sexp_value, lsexp_power) ->
                 let numDupl = List.length (IdentMap.find vidLhs mArrayVar) in
                 let exp_value = Hept_utils.mk_exp (Econst sexp_value) (* ~level_ck:rhs.e_level_ck *)
                                     rhs.e_ty ~linearity:rhs.e_linearity in
                 let nlexp = duplicate_k_times exp_value numDupl in
                 eq, (create_new_eq_from_tuple vidLhs mArrayVar nlexp)@acc
               | _ -> Format.fprintf (Format.formatter_of_out_channel stdout)
                             "Rhs of an equation defining a selected array not expected (const).\n\tEquation is %a\n@?"
                                 Hept_printer.print_eq eq;
                      failwith "arrayDestruct: unexpected destroyed array equation."
               end
             | _ -> Format.fprintf (Format.formatter_of_out_channel stdout)
                             "Rhs of an equation defining a selected array not expected.\n\tEquation is: %a\n@?"
                                 Hept_printer.print_eq eq;
                      failwith "arrayDestruct: unexpected destroyed array equation."
           end
         else eq, eq::acc
      end
    | _ -> eq, eq::acc


let var_ident_subst_array mArrayVar funs acc vid =
  try
    let lvd = IdentMap.find vid mArrayVar in
    let (_,vd) = List.hd lvd in
    vd.v_ident, acc
  with
  | Not_found -> vid, acc
  

let subst_array_var mArrayVar lequs =
  let funs_subst_array = { Hept_mapfold.defaults with
      eq = (eq_subst_array mArrayVar);         (* A = [ .... ] => A_0 = ... / A_1 = ... / ... *)
      edesc = (edesc_subst_array mArrayVar);   (* A[k] -> A_k *)
(*      global_funs = {Global_mapfold.defaults with var_ident = (var_ident_subst_array mArrayVar)} *)
    }
  in
  let subst_array_var_eq acc equ =
    let _, nEqus = funs_subst_array.eq funs_subst_array acc equ in
    nEqus
  in
  let nlequs = List.fold_left subst_array_var_eq [] lequs in
  nlequs




(* ============================================================================= *)

(* Pretty-printer for debug *)
let print_mArrayVar ff mArrayVar =
  let rec print_lvarDecl ff lv = match lv with
    | [] -> ()
    | (k, vd)::r -> Format.fprintf ff "(%i, %a), " k Global_printer.print_ident vd.v_ident;
       print_lvarDecl ff r
  in
  Format.fprintf ff "mArrayVar =\n%a\n@?"
    (fun ff mArrVar -> IdentMap.iter
        (fun id lvd ->
          Format.fprintf ff "\t%a -> [%a]\n"
           Global_printer.print_ident id  print_lvarDecl lvd
        )
      mArrVar)
    mArrayVar


let rec remove_local_vars larrIdToDestroy res lvdLoc =
  let rec remove_varid vid res larrIdToDestroy = match larrIdToDestroy with
    | [] -> (res, false)
    | h::t ->
      let (vid_h, _, _) = h in
      if (vid_h.v_ident=vid) then (t@res, true) else
      remove_varid vid (h::res) t
  in
  match lvdLoc with
  | [] -> res
  | vdLoc :: r ->
    let (larrIdToDestroy, isRemoved) = remove_varid vdLoc.v_ident [] larrIdToDestroy in
    if (isRemoved) then remove_local_vars larrIdToDestroy res r
      else remove_local_vars larrIdToDestroy (vdLoc::res) r

let get_var_rhs eq = match eq.eq_desc with
  | Eeq (plhs, erhs) -> begin
      match erhs.e_desc with
      | Evar vid -> Some vid
      | _ -> None
    end
  | _ -> None

let get_array_rhs eq = match eq.eq_desc with
  | Eeq (plhs, erhs) -> begin
      match erhs.e_desc with
        | Eapp (a, le, _) -> begin
          match a.a_op with
          | Eselect ->
            let expArr = List.hd le in
            begin match expArr.e_desc with
              | Evar vid -> Some vid
              | _ -> None
            end
          | _ -> None
        end
        | _ -> None
    end
  | _ -> None

let rec search_equation vid leqs =
  let rec pattern_contain vid p = match p with
    | Etuplepat pl ->
      List.fold_left (fun acc p1 ->
        acc || (pattern_contain vid p1)
      ) false pl
    | Evarpat vidp -> (vidp=vid)
  in
  let eq_defines vid eq = match eq.eq_desc with
    | Eeq (prhs,_) -> pattern_contain vid prhs
    | _ -> false
  in
  match leqs with
  | [] -> failwith "search_equation : equation not found"
  | h::t ->
    if (eq_defines vid h) then h
    else search_equation vid t

let rec replace_equation eq nEq leq = match leq with
  | [] -> failwith "replace_equation : Equation not found"
  | h::t -> if (h=eq) then nEq::t else h::(replace_equation eq nEq t)


let destroyArrays nd larrIdToDestroy =
  let rec create_var_decl_aux arrId sizeArr tyArr = match sizeArr with
    | 0 -> []
    | _ -> begin
      assert(sizeArr>0);
      let strNameVarDec = (Idents.name arrId) ^ "__" ^ (string_of_int sizeArr) in
      let nameVarDec = Idents.gen_var "arrayDestruct" (strNameVarDec) in
      
      let vardec = Hept_utils.mk_var_dec nameVarDec tyArr ~linearity:Linearity.Ltop in
      (sizeArr, vardec)::(create_var_decl_aux arrId (sizeArr-1) tyArr)
    end
  in
  
  let bl = nd.n_block in
  
  (* Creation of the new local variables
      + log them in a map "mArrayVar: arrId |-> list of (i * varDecl)"
      the latter couple is an association list *)
  let mArrayVar = IdentMap.empty in
  
  let (mArrayVar, lnew_loc_var) = List.fold_left
    (fun (mArrVar, lnVar) (arrVarDecl, sizeArr, tyArr) ->
      let lnVarDecl = create_var_decl_aux arrVarDecl.v_ident sizeArr tyArr in
      
      let addlnVar = List.map (fun (_,vdec) -> vdec) lnVarDecl in
      let lnVar = addlnVar@lnVar in
      let mArrVar = IdentMap.add arrVarDecl.v_ident lnVarDecl mArrVar in
      
      (mArrVar,lnVar)
    ) (mArrayVar,[]) larrIdToDestroy in
  
  
  (* DEBUG
  print_mArrayVar (Format.formatter_of_out_channel stdout) mArrayVar; *)
  
  (* Substitution of these variables in the program *)
  let nleqs = subst_array_var mArrayVar bl.b_equs in

  (* Updating the data structures *)
  let nlLocVar = remove_local_vars larrIdToDestroy [] bl.b_local in
  let nlLocVar = nlLocVar @ lnew_loc_var in

  (* TODO DEBUG
  let num_var_created = List.fold_left (fun acc (_, sizeArr, _) -> sizeArr + acc ) 0 larrIdToDestroy in
  Format.fprintf (Format.formatter_of_out_channel stdout) "num_var_created = %i\n@?" num_var_created;
  Format.fprintf (Format.formatter_of_out_channel stdout) "bl.b_local.lenght = %i\n@?" (List.length bl.b_local);
  Format.fprintf (Format.formatter_of_out_channel stdout) "l_new_loc_var.lenght = %i\n@?" (List.length lnew_loc_var);
  Format.fprintf (Format.formatter_of_out_channel stdout) "nlLocVar.lenght = %i\n@?" (List.length nlLocVar); *)

  let nbl = { bl with
         b_local = nlLocVar;
         b_equs = nleqs } in
  let nd = { nd with n_block = nbl } in

  (* Replace all instances of the removed variables by one of the new ones *)
  let funs_subst_vid = { Hept_mapfold.defaults with
      Hept_mapfold.global_funs = {Global_mapfold.defaults with Global_mapfold.var_ident = (var_ident_subst_array mArrayVar)}
      } in
  let nd, _ = funs_subst_vid.node_dec funs_subst_vid mArrayVar nd in

  (* Output arrays (might have been modified by prev array - TODO SPECIFIC TO SAFRAN !!! ) *)
  (* Out = var_elem / var_elem = arr[...]  (wrong)  ===> Out = arr *)
  
  (* OLD
  let nd = List.fold_left (fun nd outvd ->

    if ((get_array_const_size outvd.v_type)=None) then nd else
    (* The output is an array *)
    let eqOut = search_equation outvd.v_ident nd.n_block.b_equs in

    let varrhsOpt = get_var_rhs eqOut in
    match varrhsOpt with
      | None -> nd
      | Some varrhs ->
    (* The rhs of the equation defining the output is a variable *)
    (* => job to do here! *)

    (* TODO: DEBUG *)
    Format.fprintf (Format.formatter_of_out_channel stdout) "varrhs = %a\n@?"
      Global_printer.print_ident varrhs;

    let eqVarElem = search_equation varrhs nd.n_block.b_equs in
    let varArrOpt = get_array_rhs eqVarElem in
    match varArrOpt with
      | None ->
        (* TODO: DEBUG *)
        Format.fprintf (Format.formatter_of_out_channel stdout) "\t ... rhs not valid\n@?";
        nd
      (* Not a recognized structure of equation *)
      | Some varArr ->
      let rhsEdesc = Evar varArr in
      let rhsNEq = Hept_utils.mk_exp rhsEdesc outvd.v_type ~linearity:Linearity.Ltop in
      let nEqOut = Hept_utils.mk_simple_equation (Evarpat outvd.v_ident) rhsNEq in
      let nleqs = replace_equation eqOut nEqOut nd.n_block.b_equs in
      let nbl = {bl with b_equs = nleqs} in
      {nd with n_block = nbl}
  ) nd nd.n_output in
  *)

  (* DEBUG
  Hept_printer.print_node (Format.formatter_of_out_channel stdout) nd; *)
  
  nd





(* ============================================================================= *)
(* Selection part of the transformation *)

(* Get the local arrays with no linearity *)
let get_local_arrays nd =
  let lloc = nd.n_block.b_local in
  
  (* Get the arrays and their size*)
  let lloc = List.map
    (fun vdec ->
      let ty = vdec.v_type in
      let optSize = get_array_const_size ty in
      (vdec, optSize)
    ) lloc in
  
  let llocArray = List.fold_left
    (fun acc (vdec, optSize) -> match optSize with
      | None -> acc
      | Some (size, ty) -> (vdec, size, ty)::acc
    ) [] lloc in
  
  (* Remove the ones with linearity *)
  let llocArrayNoLin = List.filter
    (fun (vdec,_,_) -> vdec.v_linearity=Linearity.Ltop)
    llocArray in
  llocArrayNoLin


(* Note for the visitor: the system is normalised at that point *)
(* Visitor gather the var name which are in/outputs of node calls
     + which are used with something else than a Eselect *)
let getVariable_edescinspect acc sexpr = match sexpr.e_desc with
  | Evar vid -> vid::acc
  | _ -> acc


let edesc_inspect funs acc ed = match ed with
  | Eapp (ap, lsexpr, _) ->
    begin
    match ap.a_op with
      | Etuple | Eifthenelse | Earrow
          | Efield | Efield_update | Ereinit
          | Eselect
             -> Hept_mapfold.edesc funs acc ed (* Non-array ops / allowed expr *)
      
      | Earray | Earray_fill | Eselect_dyn
        | Eselect_trunc | Eselect_slice
        | Eupdate | Econcat
        | Efun _ | Enode _ -> begin
          (* We track the variables in "lsexpr" *)
          let n_remove = List.fold_left getVariable_edescinspect [] lsexpr in
          ed, n_remove@acc
        end
    end
  | _ -> Hept_mapfold.edesc funs acc ed
  

let is_fun_call exp = match exp.e_desc with
  | Eapp (ap, _, _) -> begin
    match ap.a_op with
      | Efun _ -> true
      | Enode _ -> true
      | _ -> false
    end
  | _ -> false


let is_const_exp exp = match exp.e_desc with
  | Econst _ -> true
  | _ -> false


let rec extract_varId p = match p with
  | Evarpat vid -> [vid]
  | Etuplepat pl ->
    let llvid = List.map extract_varId pl in
    let lvid = List.flatten llvid in
    lvid


let eqdesc_inspect funs acc eqd = match eqd with
  | Eeq (p, rhs) ->
    (* Note: const which are arrays are not inlined (but could be) *)
    if (is_fun_call rhs || is_const_exp rhs) then
      begin
      let _, nacc = Hept_mapfold.eqdesc funs acc eqd in   (* Recursion *)
      let n_remove = extract_varId p in                            (* Remove vars from the lhs *)
      
      let nacc = n_remove@nacc in
      eqd, nacc
      end
    else eqd, acc
  | _ -> Hept_mapfold.defaults.eqdesc funs acc eqd


(* Remove the variable declaration inside "lArrVarDecl" whose name
    appears as the output or the input of a function call *)
let remove_if_in_func_call_or_not_Eselect nd lArrVarDecl =
  (* Step 1: To avoid going through the whole program AST several times,
     we perform a single inspection to figure out the variables to be
     removed from the optimisation list *)
  let funs_inspect = { Hept_mapfold.defaults with
       eqdesc = eqdesc_inspect;
       edesc = edesc_inspect;
     } in
  let _, lToRemove = funs_inspect.node_dec funs_inspect [] nd in
  
  (* Step 2: We filter the variables of "lArrVarDecl" by using "lToRemove" *)
  let lArrVarDecl = List.filter
    (fun (varDecl,_,_) -> not (List.mem varDecl.v_ident lToRemove))
    lArrVarDecl
  in
  lArrVarDecl

(* Remove the variable declaration inside "lArrVarDecl" which
    is used in a copy equation, with an output on the lhs *)
let remove_if_used_as_output nd lArrVarDecl =
  let lToRemove = List.fold_left (fun acc outvd ->
    if ((get_array_const_size outvd.v_type)=None) then acc else
    (* The output is an array *)
    let eqOut = search_equation outvd.v_ident nd.n_block.b_equs in

    let varrhsOpt = get_var_rhs eqOut in
    match varrhsOpt with
      | None -> acc
      | Some varrhs ->
      (* The rhs of the equation defining the output is a variable *)
      varrhs::acc
  ) [] nd.n_output in
  let lArrVarDecl = List.filter
    (fun (varDecl,_,_) -> not (List.mem varDecl.v_ident lToRemove))
    lArrVarDecl
  in
  lArrVarDecl
  (* TODO *)

(* Pretty-printer for debugging *)
let print_arrToDestroy ff arrToDestroy =
  Format.fprintf ff "[\n";
  List.iter (fun (arrName, arrSize, arrTy) ->
      Format.fprintf ff "\t* %a (%a ^ %i)\n"
        Global_printer.print_ident arrName.v_ident
        Global_printer.print_type arrTy
        arrSize
    ) arrToDestroy;
  Format.fprintf ff "]\n"


(* Get the list of (array_name, size, ty) which can be removed *)
let findArrayToDestroy nd =
  let lArrVarDecl = get_local_arrays nd in
  let lArrVarDecl = remove_if_in_func_call_or_not_Eselect nd lArrVarDecl in
  let lArrVarDecl = remove_if_used_as_output nd lArrVarDecl in

  lArrVarDecl


(* ============================================================================= *)  

(* Getting infos about aliased type declarations *)
(* tyAliasInfo: (qualname * ty) list *)
let getTyAliasInfo p =
  let tyAliasInfo = List.fold_left
    (fun acc pdesc -> match pdesc with
      | Ptype td -> begin
        match td.t_desc with
          | Type_alias ty -> (td.t_name, ty)::acc
          | _ -> acc
        end
      | _ -> acc
    ) [] p.p_desc in
  tyAliasInfo

(* Iterate over all local variables and replace their type with the aliased expression, if needed *)
let aliasSubstitution tyAliasInfo nd =
  let rec find_aliasInfo tyAliasInfo tid = match tyAliasInfo with
    | [] -> None
    | (nty, ty)::r ->
      if (tid.name = nty.name) then Some ty
      else find_aliasInfo r tid
  in
  let replaceAliasType tyAliasInfo varLoc =
    let tyVarLoc = varLoc.v_type in
    match tyVarLoc with
      | Tid tid ->
        begin
        let optTy = find_aliasInfo tyAliasInfo tid in
        match optTy with
          | None -> varLoc
          | Some ty -> { varLoc with v_type = ty }
        end
      | _ -> varLoc
  in
  let lVarLoc = nd.n_block.b_local in
  let nlVarLoc = List.map (replaceAliasType tyAliasInfo) lVarLoc in
  let nbl = { nd.n_block with b_local = nlVarLoc } in

  let nlVarIn = List.map (replaceAliasType tyAliasInfo) nd.n_input in
  let nlVarOut = List.map (replaceAliasType tyAliasInfo) nd.n_output in

  { nd with n_block = nbl; n_input = nlVarIn; n_output = nlVarOut }

(* Main function *)
let node tyAliasInfo nd =
  let nd = aliasSubstitution tyAliasInfo nd in
  let arrToDestroy = findArrayToDestroy nd in
  
  (* DEBUG
  Format.fprintf (Format.formatter_of_out_channel stdout) "arrToDestroy = %a\n@?"
    print_arrToDestroy arrToDestroy; *)
  
  let nd = destroyArrays nd arrToDestroy in
  nd

let program p =
  let tyAliasInfo = getTyAliasInfo p in
  
  let npdesc = List.map
    (fun pdesc -> match pdesc with
      | Pnode nd -> Pnode (node tyAliasInfo nd)
      | _ -> pdesc 
    ) p.p_desc in
  { p with p_desc = npdesc }

