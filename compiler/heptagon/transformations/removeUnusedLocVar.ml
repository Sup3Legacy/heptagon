
open Idents
open Names
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

let extract_data_out eq =
  let rec get_list_vid plhs = match plhs with
    | Etuplepat pl -> List.fold_left (fun acc p1 -> acc@(get_list_vid p1)) [] pl
    | Evarpat vid -> vid::[]
  in
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

let node nd =
  let nd = closure_useless_locvar_removal nd in
  nd

let program p =
  let nlpdesc = List.fold_left
  (fun acc pdesc -> match pdesc with
    | Pnode nd -> (Pnode (node nd))::acc
    | _ -> pdesc::acc
  ) [] p.p_desc in
  {p with p_desc = nlpdesc}
