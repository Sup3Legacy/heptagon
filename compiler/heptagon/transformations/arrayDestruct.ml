(* Array destruction transformation *)

(* Criterion of which array should we destruct:
   - Must be a local variable
   - Must not have an associated Linearity (i.e., a specific reused memory location for the array)
   - Must NOT be the argument/output of a function/node call
   - Must only used with a Eselect, with a constant inside
   
  Substitution performed:
   - For each cell of the array A, introduce a new local variable A_k
   - On the rhs, replace A[k] by A_k
   - On the lhs, replace the definition of A as a tuple by size(A) equations
  *)

open Misc
open Names
open Idents
open Types
open Heptagon
open Hept_mapfold

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
                    (fun stexp -> Hept_utils.mk_exp (Econst stexp) ~level_ck:rhs.e_level_ck
                                     ~ct_annot:rhs.e_ct_annot  ~loc:rhs.e_loc rhs.e_ty ~linearity:rhs.e_linearity 
                    ) lsexp in
                 eq, (create_new_eq_from_tuple vidLhs mArrayVar nlexp)@acc
               | Sarray_power (sexp_value, lsexp_power) ->
                 let numDupl = List.length (IdentMap.find vidLhs mArrayVar) in
                 let exp_value = Hept_utils.mk_exp (Econst sexp_value) ~level_ck:rhs.e_level_ck
                                     ~ct_annot:rhs.e_ct_annot  ~loc:rhs.e_loc rhs.e_ty ~linearity:rhs.e_linearity in
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



let subst_array_var mArrayVar lequs =
  let funs_subst_array = { Hept_mapfold.defaults with
      eq = (eq_subst_array mArrayVar);         (* A = [ .... ] => A_0 = ... / A_1 = ... / ... *)
      edesc = (edesc_subst_array mArrayVar);   (* A[k] -> A_k *)
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


let destroyArrays nd larrIdToDestroy =
  let rec create_var_decl_aux arrId sizeArr tyArr = match sizeArr with
    | 0 -> []
    | _ -> begin
      assert(sizeArr>0);
      let strNameVarDec = (Idents.name arrId) ^ (string_of_int sizeArr) in
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
  
  
  (* DEBUG *)
  (* print_mArrayVar (Format.formatter_of_out_channel stdout) mArrayVar; *)
  
  (* Substitution of these variables in the program *)
  let nleqs = subst_array_var mArrayVar bl.b_equs in
  
  (* Updating the data structures *)
  let nlLocVar = lnew_loc_var @ bl.b_local in
  
  let nbl = { bl with
         b_local = nlLocVar;
         b_equs = nleqs } in
  let nd = { nd with n_block = nbl } in
  
  (* DEBUG
  Hept_printer.print_node (Format.formatter_of_out_channel stdout) nd; *)
  
  nd





(* ============================================================================= *)
(* Selection part of the transformation *)

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

let rec extract_varId p = match p with
  | Evarpat vid -> [vid]
  | Etuplepat pl ->
    let llvid = List.map extract_varId pl in
    let lvid = List.flatten llvid in
    lvid

let eqdesc_inspect funs acc eqd = match eqd with
  | Eeq (p, rhs) ->
    if (is_fun_call rhs) then
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
  lArrVarDecl


(* ============================================================================= *)  

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
  { nd with n_block = nbl }


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
  (* Getting infos about aliased type declarations *)
  (* tyAliasInfo: (qualname * ty) list *)
  let tyAliasInfo = List.fold_left
    (fun acc pdesc -> match pdesc with
      | Ptype td -> begin
        match td.t_desc with
          | Type_alias ty -> (td.t_name, ty)::acc
          | _ -> acc
        end
      | _ -> acc
    ) [] p.p_desc in
  
  let npdesc = List.map
    (fun pdesc -> match pdesc with
      | Pnode nd -> Pnode (node tyAliasInfo nd)
      | _ -> pdesc 
    ) p.p_desc in
  { p with p_desc = npdesc }

