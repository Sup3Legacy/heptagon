
open Idents
open Names
open Types
open Heptagon
open Hept_mapfold

exception Data_produced_twice
exception Equation_not_in_Eeq_form

let rec remove_all_list lToRemove res l = match l with
 | [] -> res
 | h::t ->
  if (List.mem h lToRemove) then (remove_all_list lToRemove res t)
  else (remove_all_list lToRemove (h::res) t)

(* ============================================================================= *)
(* DataTable construction*)

(* Copy n times an element
   Note: not valid if there is mutable inside x *)
let rec copy_n_times n x = match n with
  | 0 -> []
  | _ -> x::(copy_n_times (n-1) x)

let assert_int stexp = match stexp.se_desc with
  | Sint i -> i
  | _ -> failwith "assert_int : not an integer"

(* Getter to pattern-match an equation *)
let get_lhs_rhs_eq e = match e.eq_desc with
  | Eeq (lhs, rhs) -> (lhs, rhs)
  | _ -> raise Equation_not_in_Eeq_form

let extract_data_in eq =
  let edesc_extract_data_in funs acc edesc = match edesc with
    | Evar vid -> edesc, vid::acc
    | _ -> Hept_mapfold.edesc funs acc edesc
  in
  let (_, rhs) = get_lhs_rhs_eq eq in
  let funs_data_in = { Hept_mapfold.defaults with edesc = edesc_extract_data_in} in
  let _, acc = funs_data_in.exp funs_data_in [] rhs in
  acc

let rec get_list_vid plhs = match plhs with
  | Etuplepat pl -> List.fold_left (fun acc p1 -> acc@(get_list_vid p1)) [] pl
  | Evarpat vid -> vid::[]

let extract_data_out eq =
  let (lhs, _) = get_lhs_rhs_eq eq in
  get_list_vid lhs

let buildDataTable nd =
  let dataTable = Hashtbl.create (List.length nd.n_block.b_local) in
  List.iter (fun eq ->
    let eqDataIn = extract_data_in eq in
    let eqDataOut = extract_data_out eq in

    (* Update information per variables *)
    List.iter (fun nvarin ->
      try
        let (info_prod, info_cons) = Hashtbl.find dataTable nvarin in
        Hashtbl.replace dataTable nvarin (info_prod, eq::info_cons)
      with Not_found ->
       Hashtbl.add dataTable nvarin ([],eq::[])
    ) eqDataIn;
    List.iter (fun nvarout ->
      try
        let (info_prod, info_cons) = Hashtbl.find dataTable nvarout in
        if (info_prod!=[]) then raise Data_produced_twice else
        Hashtbl.replace dataTable nvarout (eq::[],info_cons)
      with Not_found ->
       Hashtbl.add dataTable nvarout (eq::[],[])
    ) eqDataOut
  ) nd.n_block.b_equs;
  dataTable


(* ============================================================================= *)
(* Useless variable removal *)

module SetVarId = Set.Make(struct type t = var_ident let compare = Pervasives.compare end)


let get_varNotUsed dataTable nd =
  let rec remove_inout_varNotUsed lToRemove res l = match l with
   | [] -> res
   | (h,leqProd)::t ->
    if (List.mem h lToRemove) then (remove_inout_varNotUsed lToRemove res t)
    else (remove_inout_varNotUsed lToRemove ((h,leqProd)::res) t)
  in

  let varNotUsed = Hashtbl.fold (fun vid (leqProd, leqCons) acc ->
    if (leqCons=[]) then (vid, leqProd)::acc else acc
  ) dataTable [] in
  
  (* + only local variables *)
  let lvid_input = List.map (fun vd -> vd.v_ident) nd.n_input in
  let lvid_output = List.map (fun vd -> vd.v_ident) nd.n_output in
  let varNotUsed = remove_inout_varNotUsed (lvid_input @ lvid_output) [] varNotUsed in

  (* + part of equation whose output are also never used *)
  let setVarUnused = List.fold_left (fun acc (vid,_) ->
    SetVarId.add vid acc
  ) SetVarId.empty varNotUsed in
  let varNotUsed = List.fold_left (fun accRes (vid, leqProd) -> 
    let eqProd = Misc.assert_1 leqProd in
    let ldataOutProd = extract_data_out eqProd in

    (* Are all elements of ldataOutProd inside lVarUnused? *)
    let belim = List.fold_left (fun acc vidDataOut ->
      acc && (SetVarId.mem vidDataOut setVarUnused)
    ) true ldataOutProd in
    if (belim) then (vid, eqProd)::accRes else accRes
  ) [] varNotUsed in

  (* TODO DEBUG *)
  Format.fprintf (Format.formatter_of_out_channel stdout) "varNotUsed.size = %i\n@?"
    (List.length varNotUsed);

  varNotUsed

let remove_varNotUsed varNotUsed nd =
  let rec remove_all_local_var lToRemove res l = match l with
    | [] -> res
    | locvd::t ->
    if (List.mem locvd.v_ident lToRemove) then (remove_all_local_var lToRemove res t)
    else (remove_all_local_var lToRemove (locvd::res) t)
  in
	let (lLocVarToRemove, lEqToRemove) = List.split varNotUsed in
  let nequs = remove_all_list lEqToRemove [] nd.n_block.b_equs in
  
  let nloc = remove_all_local_var lLocVarToRemove [] nd.n_block.b_local in
  let bl = {nd.n_block with b_local = nloc; b_equs = nequs } in
  let nd = {nd with n_block = bl} in
  nd

(* Useless local var removal *)
let useless_locvar_removal nd =
  let dataTable = buildDataTable nd in
  let varNotUsed = get_varNotUsed dataTable nd in
  let nd = remove_varNotUsed varNotUsed nd in
  nd


(* Useless local var removal - Applied until nothing more can be removed *)
let rec closure_useless_locvar_removal nd =
  let dataTable = buildDataTable nd in
  let varNotUsed = get_varNotUsed dataTable nd in
  if (varNotUsed = []) then nd else
  let nd = remove_varNotUsed varNotUsed nd in
  closure_useless_locvar_removal nd

(* ============================================================================= *)
(* Constant propagation, inclusing array accessed to these constants *)

(* constmap : string -> const_dec *)
module MapString = Map.Make(struct type t = string let compare = Pervasives.compare end)
module MapVarId = Map.Make(struct type t = var_ident let compare = Pervasives.compare end)


let rec extract_mem_cell_value stexpArr lindstExp = match lindstExp with
  | [] -> stexpArr
  | ind::rIndStExp ->
    let i = match ind.se_desc with
      | Sint si -> si
      | _ -> failwith "Static indice not an integer"
    in
    let lstelem = match stexpArr.se_desc with
      | Sarray lstelem | Stuple lstelem -> lstelem
      | _ -> failwith "Not an array or a tuple"
    in
    extract_mem_cell_value (List.nth lstelem i) rIndStExp

let edesc_const_prop_array funs acc edesc = match edesc with
  | Econst stexp -> begin
    match stexp.se_desc with
    | Svar cname ->
      let cdec = MapString.find cname.name acc in
      (Econst cdec.c_value), acc
    | _ -> Hept_mapfold.edesc funs acc edesc
    end
  | Eapp (a, le, _) -> begin
    match a.a_op with
    | Eselect -> (
     let eArr = Misc.assert_1 le in
     (* We check if eArr is a constant *)
     match eArr.e_desc with
       | Econst stexp -> begin
        match stexp.se_desc with
          | Svar cname ->
            let cdec = MapString.find cname.name acc in
            (* Get the corresponding array cell from cdec.c_value *)
            let arrCellVal = extract_mem_cell_value cdec.c_value a.a_params in
            (Econst arrCellVal), acc
          | _ -> Hept_mapfold.edesc funs acc edesc
        end
        | _ -> Hept_mapfold.edesc funs acc edesc
      )
    | _ -> Hept_mapfold.edesc funs acc edesc
  end
  | _ -> Hept_mapfold.edesc funs acc edesc

(* --- *)

let detect_const_array_power leq =
  let mVarArr = List.fold_left (fun acc eq ->
    let (lhs,rhs) = get_lhs_rhs_eq eq in
    
    (* Do we have a single output *)
    let lvidLhs = get_list_vid lhs in
    if ((List.length lvidLhs)!=1) then acc else
    let vidLhs = List.hd lvidLhs in

    (* Is the rhs of the form "const^size" *)
    match rhs.e_desc with
    | Econst stexp -> begin
      match stexp.se_desc with
        | Sarray_power (const, sizes) ->
          MapVarId.add vidLhs (const, sizes) acc
        | _ -> acc
      end
    | _ -> acc
  ) MapVarId.empty leq in
  mVarArr

let edesc_const_array_power_repl funs acc edesc = match edesc with
 | Eapp (a, le, _) -> begin
    match a.a_op with
    | Eselect -> (
      let eArr = Misc.assert_1 le in
      (* We check if eArr is a var inside acc *)
      match eArr.e_desc with
        | Evar vid ->
          if (MapVarId.mem vid acc) then
            let (elem, _ ) = MapVarId.find vid acc in
            (Econst elem), acc
          else Hept_mapfold.edesc funs acc edesc
        | _ -> Hept_mapfold.edesc funs acc edesc
      )
    | _ -> Hept_mapfold.edesc funs acc edesc
  end
  | _ -> Hept_mapfold.edesc funs acc edesc


(* --- *)
let detect_const_array_tuple leq =
  let mVarArr = List.fold_left (fun acc eq ->
    let (lhs,rhs) = get_lhs_rhs_eq eq in
    
    (* Do we have a single output *)
    let lvidLhs = get_list_vid lhs in
    if ((List.length lvidLhs)!=1) then acc else
    let vidLhs = List.hd lvidLhs in

    (* Is the rhs of the form "const^size" *)
    match rhs.e_desc with
    | Econst stexp -> begin
      match stexp.se_desc with
         | Stuple lelem | Sarray lelem ->
          MapVarId.add vidLhs lelem acc
        | _ -> acc
      end
    | _ -> acc
  ) MapVarId.empty leq in
  mVarArr

let edesc_const_array_tuple funs acc edesc = match edesc with
 | Eapp (a, le, _) -> begin
    match a.a_op with
    | Eselect -> (
      let eArr = Misc.assert_1 le in
      (* We check if eArr is a var inside acc *)
      match eArr.e_desc with
        | Evar vid ->
          if (MapVarId.mem vid acc) then
            let lelem = MapVarId.find vid acc in
            let access_int = assert_int (Misc.assert_1 a.a_params) in
            let elem = List.nth lelem (access_int-1) in (* NOTE! Safran numerotation !!! *)
            (Econst elem), acc
          else Hept_mapfold.edesc funs acc edesc
        | _ -> Hept_mapfold.edesc funs acc edesc
      )
    | _ -> Hept_mapfold.edesc funs acc edesc
  end
  | _ -> Hept_mapfold.edesc funs acc edesc



(* Propagate the constants, and in particular the array ones *)
let const_propagation_array constmap nd =
  (* Propagating the constant from the constant definition *)
  let funs_const_prop_array = {Hept_mapfold.defaults with
        edesc = edesc_const_prop_array;
      } in
  let nd, _ = funs_const_prop_array.node_dec funs_const_prop_array constmap nd in

  (* VarArr = const^size / replace "VarElem = VarArr[ind]" by "VarElem=const" *)
  (* mVarArr : var_ident -> (const, size) *)
  let mVarArr = detect_const_array_power nd.n_block.b_equs in
  let funs_const_array_power_repl = {Hept_mapfold.defaults with
        edesc = edesc_const_array_power_repl;
      } in
  let nd, _ = funs_const_array_power_repl.node_dec funs_const_array_power_repl mVarArr nd in

  (* VarArr = [ ... ] / replace "VarElem = VarArr[ind]" by "VarElem=elemVarArr" *)
  (* mVarArr : var_ident -> lelem *)
  let mVarArr = detect_const_array_tuple nd.n_block.b_equs in
  let funs_const_array_tuple = {Hept_mapfold.defaults with
        edesc = edesc_const_array_tuple;
      } in
  let nd, _ = funs_const_array_tuple.node_dec funs_const_array_tuple mVarArr nd in

  (* Constant propagation - WARNING: remove normalization property *)

  (* TODO *)


  nd



(* ============================================================================= *)
(* Main functions *)
let node constmap nd =
  let nd = closure_useless_locvar_removal nd in
  let nd = const_propagation_array constmap nd in
  let nd = closure_useless_locvar_removal nd in
  nd

let program p =
  (* Gather the constant definition inside a map *)
  let constmap = List.fold_left (fun acc pdesc-> match pdesc with
    | Pconst cd -> MapString.add cd.c_name.name cd acc
    | _ -> acc
  ) MapString.empty p.p_desc in
  
  let nlpdesc = List.fold_left
  (fun acc pdesc -> match pdesc with
    | Pnode nd -> (Pnode (node constmap nd))::acc
    | _ -> pdesc::acc
  ) [] p.p_desc in
  {p with p_desc = nlpdesc}
