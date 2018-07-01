(* Equation clustering - group equation together,
    in order to coarsen the granularity of the application *)

(* Author: Guillaume I *)

(** Heuristics:
    * If an equation uses only one data, merge it with the producer equation
    * If the output of an equation is only used once, merge it with the consumer equation
  *)
open Idents
open Names
open Types
open Heptagon
open Hept_mapfold

exception Equation_not_in_Eeq_form
exception ListEmpty
exception Data_produced_twice
exception GroupEqNotFound


let debug_info = true (* TODO DEBUG *)
let merge_only_same_instance = true   (* Force group fusion to be performed between equations of the same instance *)
let merge_only_same_instance_wfz = false (* Previous policy only applies on wfz groups *)
let merge_no_wfz = true                (* wfz groups should not be merged together *)


(* Remove all elements of lToRemove in l and concatene it to res *)
let rec remove_all_list lToRemove res l = match l with
 | [] -> res
 | h::t ->
  if (List.mem h lToRemove) then (remove_all_list lToRemove res t)
  else (remove_all_list lToRemove (h::res) t)

(* Remove an element elem from a list l, if actbool is true *)
let remove_list actbool l elem =
  let rec remove_list_aux res l elem = match l with
    | [] -> (false,res)
    | h::t -> if (h=elem) then (true, List.rev_append res t)
      else remove_list_aux (h::res) t elem
  in
  if (actbool) then remove_list_aux [] l elem else (true,l)

(* Remove all list for variable declaration, by looking at its vid to be sure *)
let rec mem_list_vid vid lvd = match lvd with
  | [] -> false
  | h::t -> if (Idents.name h = Idents.name vid) then true
    else mem_list_vid vid t

let rec remove_all_list_vid lToRemove res l = match l with
 | [] -> res
 | h::t ->
  if (mem_list_vid h lToRemove) then (remove_all_list_vid lToRemove res t)
  else (remove_all_list_vid lToRemove (h::res) t)


(* Get the last element of a list *)
let rec get_last l = match l with
 | [] -> raise ListEmpty
 | x::[] -> x
 | _::t -> get_last t

(* Concatenation of l1 and l2, while avoiding duplicate element from l1 and l2 *)
let rec concat_no_dupl l1 l2 = match l2 with
  | [] -> l1
  | h::t -> if (List.mem h l1) then
      concat_no_dupl l1 t
    else concat_no_dupl (h::l1) t


(* -----------------------------------------------------------  *)

type group_eq = {
  name : string;    (* Name of the group of equation *)
  lequ : eq list;   (* List of equations contained inside this group *)
  instance : int;   (* Number of the instance (we cannot merge different instances) *)
  wfz : string option; (* Does the group_eq contain a wfz? *)
  is_pre : bool;      (* Is the group a single "pre" equation (not to be merged) *)

  (* The two next field are temporary values, computed only after the dataTable *)
  l_inp : var_ident list;               (* Inputs of a group of equation *)
  l_out : (var_ident * (eq list)) list; (* Outputs of a group of equation + equs outside of the group using it *)
  l_loc : var_ident list;               (* Local var of a group of equation *)
}

let mk_group_eq n leq i wfzOpt isPre = { name = n; lequ = leq; instance = i;
    wfz = wfzOpt; is_pre = isPre;
    l_inp = []; l_out = []; l_loc = [] }

(* Hashtbl maintained through the transformation: *)
(*  * dataTable : var_ident --> ( leq_Prod_data , leq_Cons_data ) *)
(*  * eq2grTable : eq --> gr_eq *)
let merge_group_eq eq2grTable gEq1 gEq2 =
  let rec is_varid_in_l_out vid l_out = match l_out with
   | [] -> false
   | (hid,_)::t -> if (vid=hid) then true else is_varid_in_l_out vid t 
  in
  if (merge_only_same_instance && (gEq1.instance != gEq2.instance)) then
    failwith "Merging with 2 different instances not allowed" else
  if (merge_no_wfz && ((gEq1.wfz!=None) && (gEq2.wfz!=None))) then
    failwith "Merging groups with 2 wfz not allowed" else
  if ((gEq1.is_pre) || (gEq2.is_pre)) then
    failwith "Merging pre groups not allowed"
  else
    (* Input : variable not produced, but used by the group
       Output: variable produced, but used outside of the group
       Local : variable produced, and not used outside of the group 
      *)
    
    (* in3 = (in1 + in2) - (out1 + out2 + out_gl)
       out3 = (out1 + out2) used outside of the group
       loc3 = loc1 + loc2 + [(out1 + out2) not used outside of the group]
       NOTE: global output are managed at the very end
    *)
    let lin12 = concat_no_dupl gEq1.l_inp gEq2.l_inp in
    let lout12 = List.rev_append gEq1.l_out gEq2.l_out in
    let lEqu3 = List.rev_append gEq1.lequ gEq2.lequ in
    let (name3, wfz3) = match gEq1.wfz with
      | None -> (gEq2.name, gEq2.wfz)
      | Some _ -> (gEq1.name, gEq1.wfz)
    in
    let instance3 = match gEq1.wfz with
      | None -> gEq2.instance       (* Improve that by having an interval? *)
      | Some _ -> gEq1.instance
    in

    let lin3 = List.filter (fun vid ->
      not (is_varid_in_l_out vid lout12)
    ) lin12 in

    let (lout3, l_new_loc) = List.fold_left (fun (acc_out, acc_loc) (vid, lCons) ->
      (* We check if there is still equation outside of the group using vid *)
      let lConsRem = remove_all_list lEqu3 [] lCons in
      if (lConsRem=[]) then (acc_out, vid::acc_loc)
      else ((vid, lConsRem)::acc_out, acc_loc)
    ) ([],[]) lout12 in

    let lloc3 = List.rev_append (List.rev_append gEq1.l_loc gEq2.l_loc) l_new_loc in
    let lloc3 = remove_all_list_vid lin3 [] lloc3 in

    let gr3 = { name = name3; lequ = lEqu3;
      instance = instance3; wfz = wfz3; is_pre = false;
      l_inp = lin3;
      l_out = lout3;
      l_loc = lloc3;
    } in

    (* Update of eq2grTable *)
    List.iter (fun eq -> Hashtbl.replace eq2grTable eq gr3) lEqu3;
    gr3

(* -------------- *)

(* Name management*)
let name_counter = ref 0

let new_group_name inst wfz =
  name_counter := !name_counter +1;
  match wfz with
  | None -> ("group_" ^ (string_of_int !name_counter))
  | Some wfzName ->
     ("groupwfz_" ^ (string_of_int !name_counter) ^ "_" ^ wfzName)

(* Get a variable from the lhs. If it is void, returns None *)
let rec get_lhs_var p = match p with
  | Etuplepat pl -> if (pl=[]) then None else get_lhs_var (List.hd pl)
  | Evarpat vid -> Some vid

(* Get a variable from the rhs. Only called then the lhs is void.
   If there is no variable on the rhs either, throw an error *)
let get_rhs_var e =
  (* TODO: not enough !!! (ex: if there is a pre) BUT, because of normalization, works if lhs is void *)
  let edesc_get_rhs funs acc ed = match ed with
    | Evar vid -> ed, Some vid
    | _ -> Hept_mapfold.edesc funs acc ed
  in
  let funs_get_rhs_var = {Hept_mapfold.defaults with edesc = edesc_get_rhs} in
  let _,acc = funs_get_rhs_var.exp funs_get_rhs_var None e in
  match acc with
   | None -> failwith "Equation does not have any variable on the lhs and rhs"
   | Some vid -> vid

(* Getter to pattern-match an equation *)
let get_lhs_rhs_eq e = match e.eq_desc with
  | Eeq (lhs, rhs) -> (lhs, rhs)
  | _ -> raise Equation_not_in_Eeq_form

let is_Evar e = match e.e_desc with
  | Evar vid -> Some vid
  | _ -> None


(* Examine the equation to figure out which instance of duplication we are talking about *)
let get_instance_num e =
  let (lhs,rhs) = get_lhs_rhs_eq e in
  let vidopt = get_lhs_var lhs in
  let vid = match vidopt with
    | None -> get_rhs_var rhs
    | Some vlhs -> vlhs
  in
  (* Instance number currently encoded at the end of vid *)
  let strDelimEnd = Dirty_hyperperiod_expansion_Safran.strDelimEnd_varid in (* = "_sh" *)
  let lstrSplit = Str.split (Str.regexp strDelimEnd) (Idents.name vid) in
  let strNum = get_last lstrSplit in
  let instNum = int_of_string strNum in
  instNum

let extract_wfz e =
  let (_,rhs) = get_lhs_rhs_eq e in
  match rhs.e_desc with
  | Eapp (a, _, _) -> begin
    match a.a_op with
    | Efun (fname,_) | Enode (fname, _) -> begin
      (* External call *)
      if ((fname.qual=Pervasives) || (fname.qual=LocalModule)) then None
      else Some fname.Names.name
    end
    | _ -> None
  end
  | _ -> None

let extract_is_pre e =
  let (_,rhs) = get_lhs_rhs_eq e in
  match rhs.e_desc with
  | Epre _ | Efby _ -> true
  | _ -> false

let extract_is_ithe e =
  let (_,rhs) = get_lhs_rhs_eq e in
  match rhs.e_desc with
  | Eapp (ap, lsexp, _) -> (
      match ap.a_op with
      | Eifthenelse -> Some (List.hd (List.tl lsexp)) (* Second element = then *)
      | _ -> None
    )
  | _ -> None


(* Initial construction of lgroupEq
   Note: inputs/outputs/locals not extracted*)
let build_group_single_eq e =
  let i = if (!Compiler_options.hyperperiod) then
    get_instance_num e
  else 0 in
  let wfz = extract_wfz e in
  let is_pre = extract_is_pre e in
  let n = new_group_name i wfz in
  let gr = mk_group_eq n [e] i wfz is_pre in
  gr

(* -------------- *)

(* Get all the data_in of an equation *)
let extract_data_in eq =
  let edesc_extract_data_in funs acc edesc = match edesc with
    | Evar vid -> edesc, vid::acc
    | _ -> Hept_mapfold.edesc funs acc edesc
  in
  let (_, rhs) = get_lhs_rhs_eq eq in
  let funs_data_in = { Hept_mapfold.defaults with edesc = edesc_extract_data_in} in
  let _, acc = funs_data_in.exp funs_data_in [] rhs in
  acc

(* Get all the data_out of an equation *)
let extract_data_out eq =
  let rec get_list_vid plhs = match plhs with
    | Etuplepat pl -> List.fold_left (fun acc p1 -> List.rev_append acc (get_list_vid p1)) [] pl
    | Evarpat vid -> vid::[]
  in
  let (lhs, _) = get_lhs_rhs_eq eq in
  get_list_vid lhs

(* Build datainoutEq and depTable, associating the equation with the data & vice versa *)
let buildDataTable nd lgroupEq =
  let depTable = Hashtbl.create (List.length nd.n_block.b_local) in
  let eq2grTable = Hashtbl.create (List.length nd.n_block.b_equs) in

  let lgroupEq = List.fold_left (fun acc gr ->
    let eq = List.hd gr.lequ in
    let eqDataIn = extract_data_in eq in
    let eqDataOut = extract_data_out eq in

    (* Update information per variables *)
    List.iter (fun nvarin ->
      try
        let (info_prod, info_cons) = Hashtbl.find depTable nvarin in
        Hashtbl.replace depTable nvarin (info_prod, eq::info_cons)
      with Not_found ->
       Hashtbl.add depTable nvarin ([],eq::[])
    ) eqDataIn;
    List.iter (fun nvarout ->
      try
        let (info_prod, info_cons) = Hashtbl.find depTable nvarout in
        if (info_prod!=[]) then raise Data_produced_twice else
        Hashtbl.replace depTable nvarout (eq::[],info_cons)
      with Not_found ->
       Hashtbl.add depTable nvarout (eq::[],[])
    ) eqDataOut;
    let incomplete_dataOut = List.rev_map (fun eq -> (eq,[])) eqDataOut in
    { gr with l_inp = eqDataIn; l_out = incomplete_dataOut}::acc
  ) [] lgroupEq in

  (* Now that "depTable" is completed, we fill the missing dataOut info *)
  let lgroupEq = List.rev_map (fun grEq ->
    let complete_dataOut = List.rev_map
      (fun (varOutId,_) ->
        let (_, infoCons) = Hashtbl.find depTable varOutId in
        (varOutId, infoCons)
      ) grEq.l_out in
    { grEq with l_out = complete_dataOut }
  ) lgroupEq in

  (* Now that lgroupEq is stable, we complete eq2grTable *)
  List.iter (fun gr ->
    List.iter (fun eq ->
      Hashtbl.add eq2grTable eq gr
    ) gr.lequ
  ) lgroupEq;

  (lgroupEq, depTable, eq2grTable)

(* ------------- *)

(* Heuristic #0.5 - applicable only to single groups *)
let heuristic_ifte dataTable eq2grTable lgroupEq =
  let rec heuristic_ifte_aux lgroupRes lgroupRem = match lgroupRem with
    | [] -> lgroupRes 
    | gr::rest -> begin
      (* Heuristic should be applied only to single group *)
      assert((List.length gr.lequ) = 1);
      let eq = List.hd gr.lequ in

      let opteThen = extract_is_ithe eq in
      match opteThen with
      | None -> heuristic_ifte_aux (gr::lgroupRes) rest
      | Some eThen ->


        (* TODO: modify heuristic here => no merge if double-var ? => nope... :/ *)
        (*    grep => else is always a constant *)
        (* ===> issue if with the variable, which might depend (on a cyclic fashion) with the then? *)
        (* NOTE: no obvious criterion on which one to fold => DESACTIVATE THAT OPTIM BY DEFAULT *)






        (* Merge it with the group issuing the var from the "then" *)
        match (is_Evar eThen) with
        | None -> heuristic_ifte_aux (gr::lgroupRes) rest
        | Some varIdThen ->
        let (infoProd,_) = try Hashtbl.find dataTable varIdThen
          with Not_found -> (
            Format.eprintf "Cons/prod info not found, for varIdThen = %s\n@?" (Idents.name varIdThen);
            raise GroupEqNotFound)
        in
        (* If the "then" variable is an input of the program => no merge *)
        if (infoProd=[]) then heuristic_ifte_aux (gr::lgroupRes) rest else
        let eqThen = List.hd infoProd in
        let grToMerge = try Hashtbl.find eq2grTable eqThen
          with Not_found -> (
            Format.eprintf "Group of equation not found, for varIdThen = %s\n@?" (Idents.name varIdThen);
            raise GroupEqNotFound)
        in
        (* Merge not allowed if the instance is different *)
        if (merge_only_same_instance && (grToMerge.instance != gr.instance)) then
          heuristic_ifte_aux (gr::lgroupRes) rest else
        (* Merge not allowed if the other group is a pre *)
        if (grToMerge.is_pre) then
          heuristic_ifte_aux (gr::lgroupRes) rest else
        (* Other non-merge cases are irrelevant because this equation is a ithe *)
        let ngr = merge_group_eq eq2grTable gr grToMerge in

        let (found, lgroupRes) = remove_list true lgroupRes grToMerge in
        let (found, rest) = remove_list (not found) rest grToMerge in
        assert(found);
        heuristic_ifte_aux (ngr::lgroupRes) rest
    end
  in
  heuristic_ifte_aux [] lgroupEq


(* Version of Heuristic #1 for equation of the form Var = Arr[...]
  where Arr is another variable (not constant) *)
let heuristic_merge_array_accesses dataTable eq2grTable lgroupEq =

  let rec heuristic_merge_array_accesses_aux lgroupRes lgroupRem = match lgroupRem with
    | [] -> lgroupRes
    | gr::rest -> begin
      (* First application ever => all groups of correct form should be of size 1, except *)
      if ((List.length gr.lequ) != 1) then
        heuristic_merge_array_accesses_aux (gr::lgroupRes) rest
      else
      let eqGr = List.hd gr.lequ in
      let (plhs, erhs) = get_lhs_rhs_eq eqGr in
      match erhs.e_desc with
      | Eapp (app, lsexp, _) -> begin
        match app.a_op with
        | Eselect -> begin
          let eArr = Misc.assert_1 lsexp in
          match eArr.e_desc with
          | Evar dataIn -> begin
            let (leqProd,_) = Hashtbl.find dataTable dataIn in
            if (leqProd=[]) then
              (* Input array access *)
              heuristic_merge_array_accesses_aux (gr::lgroupRes) rest
            else
            let eqProd = List.hd leqProd in

            (* Merging! *)
            let grToMerge = try Hashtbl.find eq2grTable eqProd
            with Not_found -> (
              Format.eprintf "Group of equation not found, for dataIn = %s\n@?" (Idents.name dataIn);
              raise GroupEqNotFound
            ) in

            (* Merge not allowed if the instance is different *)
            if (merge_only_same_instance && (grToMerge.instance != gr.instance)) then
              heuristic_merge_array_accesses_aux (gr::lgroupRes) rest else
            (* Merge not allowed if one of the group is a wfz and instance is different *)
            if (merge_only_same_instance_wfz && (grToMerge.instance != gr.instance))
                    && (grToMerge.wfz!=None || gr.wfz!=None) then
              heuristic_merge_array_accesses_aux (gr::lgroupRes) rest else
            (* Merge not allowed if both groups contain a wfz *)
            if (merge_no_wfz && ((grToMerge.wfz!=None) && (gr.wfz!=None))) then
              heuristic_merge_array_accesses_aux (gr::lgroupRes) rest else
            (* Merge not allowed if the other group is a pre *)
            if (grToMerge.is_pre) then
              heuristic_merge_array_accesses_aux (gr::lgroupRes) rest else


            let ngr = merge_group_eq eq2grTable gr grToMerge in

            let (found, lgroupRes) = remove_list true lgroupRes grToMerge in
            let (found, rest) = remove_list (not found) rest grToMerge in
            assert(found);
            heuristic_merge_array_accesses_aux (ngr::lgroupRes) rest
          end
          | _ -> (* Econst probably *)
            heuristic_merge_array_accesses_aux (gr::lgroupRes) rest
        end
        | _ -> heuristic_merge_array_accesses_aux (gr::lgroupRes) rest
      end
      | _ -> heuristic_merge_array_accesses_aux (gr::lgroupRes) rest
    end
  in
  heuristic_merge_array_accesses_aux [] lgroupEq


(* Heuristic #1 *)
let heuristic_merge_single_use _ eq2grTable lgroupEq =
  let rec heuristic_merge_single_use_aux lgroupRes lgroupRem = match lgroupRem with
    | [] -> lgroupRes
    | gr::rest -> begin
      (* Don't do anything with pre/fby *)
      if (gr.is_pre) then
        heuristic_merge_single_use_aux (gr::lgroupRes) rest
      else
      (* Default case: more than one output , or output used more than once *)
      if (not ((List.length gr.l_out) = 1)) then
        heuristic_merge_single_use_aux (gr::lgroupRes) rest
      else
      (* Check that there is only one use *)
      let (dataOut, infoCons) = List.hd gr.l_out in
      if (not ((List.length infoCons) = 1)) then
        heuristic_merge_single_use_aux (gr::lgroupRes) rest
      else (
        (* Remark: this is an over-approximation of the real criterion *)
        (* Merging ! *)
        let eqCons = List.hd infoCons in
        let grToMerge = try Hashtbl.find eq2grTable eqCons
        with Not_found -> (
           Format.eprintf "Group of equation not found, for dataOut = %s\n@?" (Idents.name dataOut);
          raise GroupEqNotFound)
        in
        (* Merge not allowed if the instance is different *)
        if (merge_only_same_instance && (grToMerge.instance != gr.instance)) then
          heuristic_merge_single_use_aux (gr::lgroupRes) rest else
        (* Merge not allowed if one of the group is a wfz and instance is different *)
        if (merge_only_same_instance_wfz && (grToMerge.instance != gr.instance))
                && (grToMerge.wfz!=None || gr.wfz!=None) then
          heuristic_merge_single_use_aux (gr::lgroupRes) rest else
        (* Merge not allowed if both groups contain a wfz *)
        if (merge_no_wfz && ((grToMerge.wfz!=None) && (gr.wfz!=None))) then
          heuristic_merge_single_use_aux (gr::lgroupRes) rest else
        (* Merge not allowed if the other group is a pre *)
        if (grToMerge.is_pre) then
          heuristic_merge_single_use_aux (gr::lgroupRes) rest else (

        let ngr = merge_group_eq eq2grTable gr grToMerge in

        let (found, lgroupRes) = remove_list true lgroupRes grToMerge in
        let (found, rest) = remove_list (not found) rest grToMerge in
        assert(found);

        heuristic_merge_single_use_aux (ngr::lgroupRes) rest
        )
      )
    end
  in
  heuristic_merge_single_use_aux [] lgroupEq

(* Heuristic #2 *)
let heuristic_merge_single_prod dataTable eq2grTable lgroupEq =
  let rec heuristic_merge_single_prod_aux lgroupRes lgroupRem = match lgroupRem with
    | [] -> lgroupRes
    | gr::rest -> begin
      (* Don't do anything with pre/fby *)
      if (gr.is_pre) then
        heuristic_merge_single_prod_aux (gr::lgroupRes) rest
      else
      (* Default case*)
      if (not ((List.length gr.l_inp) = 1)) then
        heuristic_merge_single_prod_aux (gr::lgroupRes) rest
      else
        (* Merging ! *)
        let dataIn = List.hd gr.l_inp in
        let (leqProd,_) = Hashtbl.find dataTable dataIn in
        if (leqProd=[]) then (* True input of the program*)
          heuristic_merge_single_prod_aux (gr::lgroupRes) rest
        else
        let eqProd = List.hd leqProd in

        let grToMerge = try Hashtbl.find eq2grTable eqProd
        with Not_found -> (
          Format.eprintf "Group of equation not found, for dataIn = %s\n@?" (Idents.name dataIn);
          raise GroupEqNotFound
        ) in

        (* Merge not allowed if the instance is different *)
        if (merge_only_same_instance && (grToMerge.instance != gr.instance)) then
          heuristic_merge_single_prod_aux (gr::lgroupRes) rest else
        (* Merge not allowed if one of the group is a wfz and instance is different *)
        if (merge_only_same_instance_wfz && (grToMerge.instance != gr.instance))
                && (grToMerge.wfz!=None || gr.wfz!=None) then
          heuristic_merge_single_prod_aux (gr::lgroupRes) rest else
        (* Merge not allowed if both groups contain a wfz *)
        if (merge_no_wfz && ((grToMerge.wfz!=None) && (gr.wfz!=None))) then
          heuristic_merge_single_prod_aux (gr::lgroupRes) rest else
        (* Merge not allowed if the other group is a pre *)
        if (grToMerge.is_pre) then
          heuristic_merge_single_prod_aux (gr::lgroupRes) rest else


        let ngr = merge_group_eq eq2grTable gr grToMerge in

        let (found, lgroupRes) = remove_list true lgroupRes grToMerge in
        let (found, rest) = remove_list (not found) rest grToMerge in
        assert(found);
        heuristic_merge_single_prod_aux (ngr::lgroupRes) rest
    end
  in
  heuristic_merge_single_prod_aux [] lgroupEq

(* Applying heuristics until stability *)
let rec heuristic_run dataTable eq2grTable lgroupEq =
  let origSize = List.length lgroupEq in

  (* First heuristic: merge if an eq use a single variable *)
  let lgroupEq = heuristic_merge_single_use dataTable eq2grTable lgroupEq in
  if (debug_info) then
    Format.fprintf (Format.formatter_of_out_channel stdout) "lgroupEq.size (heuristique 1) = %i\n@?" (List.length lgroupEq)
  else ();

  (* Second heuristic: merge if an eq produce a single variable *)
  let lgroupEq = heuristic_merge_single_prod dataTable eq2grTable lgroupEq in
  if (debug_info) then
    Format.fprintf (Format.formatter_of_out_channel stdout) "lgroupEq.size (heuristique 2) = %i\n@?" (List.length lgroupEq)
  else ();

  let finalSize = List.length lgroupEq in
  if (finalSize < origSize) then
    heuristic_run dataTable eq2grTable lgroupEq
  else
    lgroupEq


(* First step: grouping equations together *)
let group_equation nd =
  if (debug_info) then
    Format.fprintf (Format.formatter_of_out_channel stdout) "lEq.size = %i\n@?" (List.length nd.n_block.b_equs)
  else ();

  (* Init *)
  let lgroupEq = List.rev_map (fun eq ->
    build_group_single_eq eq 
  ) nd.n_block.b_equs in

  (* Build dataTable - associate each varId to the equations interacting which them *)
  (* dataTable : var_ident --> ( leq_Prod_data , leq_Cons_data ) *)
  (* eq2grTable : eq --> group_eq *)
  let (lgroupEq, dataTable, eq2grTable) = buildDataTable nd lgroupEq in

  (* Other optims *)
  (* let (lgroupEq, dataTable, eq2grTable, nd) = optimize lgroupEq dataTable eq2grTable nd in *)

  if (debug_info) then
    Format.fprintf (Format.formatter_of_out_channel stdout) "lgroupEq.size (avant heuristique 0.5) = %i\n@?" (List.length lgroupEq)
  else ();

  (* Heuristic 0.5: if an equation is a ifte, merge its group with the "then" *)
  (*    => Works in Safran case because these ifte are transformed "condact" *)
  (* let lgroupEq = heuristic_ifte dataTable eq2grTable lgroupEq in *)
  (* Desactivated - not valid (causality issues afterward) *)
  let lgroupEq = heuristic_merge_array_accesses dataTable eq2grTable lgroupEq in
  (* Note: no effect on the result for AS... :/ *)

  if (debug_info) then
    Format.fprintf (Format.formatter_of_out_channel stdout) "lgroupEq.size (avant heuristique 1) = %i\n@?" (List.length lgroupEq)
  else ();

  let lgroupEq = heuristic_run dataTable eq2grTable lgroupEq in

  (* TODO DEBUG *)
  let (num_non_wfz, num_pre, num_wfz) = List.fold_left (fun (accNwfz,accPre,accWfz) gr ->
    if (gr.is_pre) then (accNwfz,accPre+1,accWfz) else
    if (gr.wfz!=None) then (accNwfz,accPre,accWfz+1) else
    (accNwfz+1,accPre,accWfz)
  ) (0,0,0) lgroupEq in
  Format.fprintf (Format.formatter_of_out_channel stdout)
    "num_non_wfz = %i | num_pre = %i | num_wfz = %i\n@?" num_non_wfz num_pre num_wfz;


  (* We now deal with potential output variable of the program,
      which might have become a local variable of a group *)
  let lglobalOut = List.rev_map (fun vd -> vd.v_ident) nd.n_output in
  let lgroupEq = List.rev_map (fun grEq ->
      let (lvid_newout, lvid_loc) = List.partition
        (fun vid -> List.mem vid lglobalOut) grEq.l_loc in
      let lvid_newout = List.rev_map (fun vid -> (vid,[])) lvid_newout in
      { grEq with l_out = List.rev_append lvid_newout grEq.l_out; l_loc = lvid_loc}
    ) lgroupEq in

  lgroupEq

(* ======================================================================= *)

(* Variable declaration search *)
let rec search_for_vardecl lvdec vid = match lvdec with
  | [] -> None
  | h::t ->
    if (h.v_ident=vid) then Some h
    else search_for_vardecl t vid

let get_vardecl tblvdNd lvid =
  List.map (fun vid ->
    try Hashtbl.find tblvdNd vid
    with Not_found ->
      failwith ("EquationClustering :: get_vardecl => vid "
                ^ (Idents.name vid) ^ " was not found in the node")
  ) lvid


(* For each group of equation lgroupEq, build the corresponding subnode *)
let build_subnodes lgroupEq nd =
  let sizeTblvdNd = (List.length nd.n_input) + (List.length nd.n_output)
            + (List.length nd.n_block.b_local) in
  let tblvdNd = Hashtbl.create sizeTblvdNd in
  List.iter (fun vd -> Hashtbl.add tblvdNd vd.v_ident vd) nd.n_input;
  List.iter (fun vd -> Hashtbl.add tblvdNd vd.v_ident vd) nd.n_output;
  List.iter (fun vd -> Hashtbl.add tblvdNd vd.v_ident vd) nd.n_block.b_local;

  let subnodesgr = List.fold_left (fun acc grEq ->
    (* Note: even if it is a pre, we still build the corresponding subnode *)
    let lvidIn = grEq.l_inp in
    let lvidOut = List.map (fun (vid,_) -> vid) grEq.l_out in
    let lvidLoc = grEq.l_loc in

    (* Retrieves the variable declaration from nd *)
    let lVarin = get_vardecl tblvdNd lvidIn in
    let lVarout = get_vardecl tblvdNd lvidOut in
    let lVarloc = get_vardecl tblvdNd lvidLoc in
    
    (* Creating the objects *)
    let bl = Hept_utils.mk_block ~stateful:nd.n_stateful ~locals:lVarloc grEq.lequ in
    let snname = Modules.fresh_value "clustering" grEq.name in
    let sn = Hept_utils.mk_node ~typeparamdecs:nd.n_typeparamdecs ~input:lVarin ~output:lVarout
      ~stateful:nd.n_stateful ~param:nd.n_params snname bl in
    (sn,grEq)::acc
  ) [] lgroupEq in
  subnodesgr

(* Note: if we want the signatures of these subnodes, Hept_utils.signature_of_node *)

let get_eq_annot instance = "release(" ^ (string_of_int instance)
      ^ ") deadline(" ^ (string_of_int (instance+1)) ^ ")"

(* Building the main node *)
let build_mainnode subnodesgr nd =
  (* Note: all equations are inside the subnodes/lgroupEq, expect for pre *)
  let lVarlocOutmainNode = List.fold_left (fun acc (snd,_) ->
    List.rev_append (snd.n_output) acc (* No duplication *)
  ) [] subnodesgr in
  let lVarloc = remove_all_list nd.n_output [] lVarlocOutmainNode in

  let lequ = List.fold_left (fun acc (sn,geq) ->
    if (geq.is_pre) then
      (* Pre => we just put the equation at the top level *)
      List.rev_append geq.lequ acc
    else (
      (* rhs of equation *)
      let op_rhs = Efun (sn.n_name,[]) in
      let app_rhs = Hept_utils.mk_app op_rhs in
      let lin_rhs = List.map (fun vd ->
        let edesc_in_rhs = Evar vd.v_ident in
        Hept_utils.mk_exp edesc_in_rhs vd.v_type ~linearity:Linearity.Ltop
      ) sn.n_input in
      let rhs_edesc = Eapp (app_rhs, lin_rhs, None) in
      let ty_rhs = Types.Tprod (List.map (fun vd -> vd.v_type) sn.n_output) in
      let rhs = Hept_utils.mk_exp rhs_edesc ty_rhs ~linearity:Linearity.Ltop in
      
      (* lhs of equation *)
      let snOutvid = List.map (fun vd -> vd.v_ident) sn.n_output in
      let plhs = if ((List.length sn.n_output)=1) then
        (Evarpat (List.hd snOutvid)) else (Etuplepat (List.map (fun vid -> Evarpat vid) snOutvid))
      in

      let annotEq = if (geq.wfz=None) then None else Some (get_eq_annot geq.instance) in

      let neq_desc = Eeq (plhs, rhs) in
      (* stateful = true => overapprox, but we are exiting early *)
      let neq = { eq_desc = neq_desc; eq_stateful = true;   
          eq_inits = Linearity.Lno_init; eq_loc = Location.no_location;
          eq_annot = annotEq } in
      neq::acc
      )
  ) [] subnodesgr in

  let bl = Hept_utils.mk_block ~stateful:nd.n_stateful ~locals:lVarloc lequ in
  let mn = Hept_utils.mk_node ~typeparamdecs:nd.n_typeparamdecs ~input:nd.n_input ~output:nd.n_output
    ~stateful:nd.n_stateful nd.n_name bl in
  mn


(* ======================================================================= *)

(* Change the input/output of the subnodes such that all of them are scalars *)
(* Communications between subnodes is preserved by the renaming convention *)
let option_generate_scalar_interfaces = true (* TODO *)

(* Create an ordered list from the association list of (pos, elem for position pos) *)
let get_list_vardecl_from_assoc_list lassoc =
  let rec get_list_vardecl_from_assoc_list_aux pos res lassoc = match pos with
    | 0 -> res
    | _ ->
      assert(pos>0);
      let elem = try
        List.assoc pos lassoc
      with Not_found -> failwith ("get_list_vardecl_from_assoc_list_aux - pos "
            ^ (string_of_int pos) ^ " not found")
      in
      get_list_vardecl_from_assoc_list_aux (pos-1) (elem::res) lassoc
  in
  get_list_vardecl_from_assoc_list_aux (List.length lassoc) [] lassoc


(* Replace the arrays in the interface of a subnode by its elements *)
(* It includes the global inputs/outputs *)
(* isMainNode = true ===> We are currently doing that for the main node (slight modif) *)
let scalar_subnodes_interface isMainNode htblScalarVar subnodesgr =
  let rec create_var_decl_aux arrId sizeArr tyArr = match sizeArr with
    | 0 -> []
    | _ -> begin
      assert(sizeArr>0);
      let strNameVarDec = (Idents.name arrId) ^ "_" ^ (string_of_int sizeArr) in
      let nameVarDec = Idents.gen_var "equationClustering" (strNameVarDec) in
      
      let vardec = Hept_utils.mk_var_dec nameVarDec tyArr ~linearity:Linearity.Ltop in
      (sizeArr, vardec)::(create_var_decl_aux arrId (sizeArr-1) tyArr)
    end
  in

  (* Filling htblScalarVar : varIdIn/Out -> (vardecl list) option *)
  List.iter (fun (snode, _) ->
    let lvdIn = snode.n_input in
    let lvdOut = snode.n_output in

    (* Detect if a given variable declaration is a destructible array *)
    List.iter (fun vd ->
      let optSizeTyArr = ArrayDestruct.get_array_const_size vd.v_type in
      match optSizeTyArr with
        | None -> Hashtbl.replace htblScalarVar vd.v_ident None
        | Some (size, tyElem) -> begin
          (* Work already done for this variable? *)
          if (Hashtbl.mem htblScalarVar vd.v_ident) then () else
          let lnScalVar = create_var_decl_aux vd.v_ident size tyElem in
          Hashtbl.replace htblScalarVar vd.v_ident (Some lnScalVar)
        end
    ) (List.rev_append lvdIn lvdOut);
  ) subnodesgr;

  (* Change the subnodes:                                 *)
  (*  - Move the array input/output into the local vardec *)
  (*       and replace them with the new scalar vardecs   *)
  (*  - Add equations to rebuilt input arrays             *)
  (*  - Add equations to select elements of output arrays *)
  let subnodesgr = List.rev_map (fun (snode, grEq) ->
    (* Variable declaration management *)
    let linput = snode.n_input in
    let loutput = snode.n_output in

    let lninput = List.fold_left (fun acc vdIn ->
      let optlVarscal = 
        try Hashtbl.find htblScalarVar vdIn.v_ident
        with Not_found -> failwith "Input element not found in htblScalarVar"
      in
      match optlVarscal with 
        | None -> vdIn::acc
        | Some lVarscal ->
          let lVarscal = List.map (fun (_,vd) -> vd) lVarscal in
          List.append lVarscal acc
    ) [] linput in

    let lnoutput = List.fold_left (fun acc vdOut ->
      let optlVarscal = 
        try Hashtbl.find htblScalarVar vdOut.v_ident
        with Not_found -> failwith "Output element not found in htblScalarVar"
      in
      match optlVarscal with 
        | None -> vdOut::acc
        | Some lVarscal ->
          let lVarscal = List.map (fun (_,vd) -> vd) lVarscal in
          List.append lVarscal acc
    ) [] loutput in

    let lnlocal = if (isMainNode) then snode.n_block.b_local else
      List.fold_left (fun acc vdInOut ->
        if (Hashtbl.mem htblScalarVar vdInOut.v_ident) then
          vdInOut::acc
        else acc
      ) snode.n_block.b_local (List.rev_append linput loutput) in

    (* Equations management *)
    (* Input: OldVardeclIn = Earray [ lScalarVarDecl ] *)
    let nEqIn =
      if (isMainNode) then [] else List.fold_left (fun acc vdIn ->
      let optlVarscal = try Hashtbl.find htblScalarVar vdIn.v_ident
        with Not_found -> failwith "Input element not found in htblScalarVar"
      in
      match optlVarscal with 
        | None -> acc
        | Some lVarscal ->
          (* lVarscal is an association list for (i, varDecl_i), starting from i=1 *)
          let lScalarVarDecl = get_list_vardecl_from_assoc_list lVarscal in
          let lexpVarScal = List.map (fun vdecl ->
            Hept_utils.mk_exp (Evar vdecl.v_ident) vdecl.v_type ~linearity:Linearity.Ltop
          ) lScalarVarDecl in
          let appTuple = Hept_utils.mk_app Earray in
          let edescrhs = Eapp (appTuple, lexpVarScal, None) in
          let erhs = Hept_utils.mk_exp edescrhs vdIn.v_type ~linearity:Linearity.Ltop in

          let plhs = Evarpat vdIn.v_ident in
          let neq = Hept_utils.mk_simple_equation plhs erhs in 
          neq::acc
    ) [] linput in

    (* Output: Etuplepat[ lScalarVarDecl ] = OldVardeclOut *)
    let nEqOut =
      if (isMainNode) then [] else List.fold_left (fun acc vdOut ->
      let optlVarscal = try Hashtbl.find htblScalarVar vdOut.v_ident
        with Not_found -> failwith "Output element not found in htblScalarVar"
      in
      match optlVarscal with
        | None -> acc
        | Some lVarscal ->
          let lScalarVarDecl = get_list_vardecl_from_assoc_list lVarscal in
          let plhs = Etuplepat (List.map (fun vd -> Evarpat vd.v_ident) lScalarVarDecl) in

          let edescrhs = Evar vdOut.v_ident in
          let erhs = Hept_utils.mk_exp edescrhs vdOut.v_type ~linearity:Linearity.Ltop in

          let neq = Hept_utils.mk_simple_equation plhs erhs in 
          neq::acc
    ) [] loutput in

    let lnequs = List.rev_append (List.rev_append nEqIn nEqOut) snode.n_block.b_equs in

    let nbl = { snode.n_block with b_local = lnlocal; b_equs = lnequs } in
    let nsnode = {snode with n_input = lninput; n_output = lnoutput; n_block = nbl } in
    (nsnode, grEq)
  ) subnodesgr in

  (subnodesgr, htblScalarVar)

(* Note: the signature of the main node changes too *)
let scalar_mainnode htblScalarVar mainnode =
  let scalar_new_nd, htblScalarVar = scalar_subnodes_interface true htblScalarVar [(mainnode,[])] in
  let (mainnode, _) = List.hd scalar_new_nd in

  (* fby management (which are still with arrays at that point *)
  let nEqs = List.fold_left (fun acc eq ->
    (* Is the equation a fby? *)
    let (_, erhs) = get_lhs_rhs_eq eq in
    match erhs.e_desc with
      | Efby (_, _) ->
        failwith "scalar_mainnode: Efby expression here ??? oO "
      | Epre (Some st_exp, ePre) -> 
        begin
        (* Is the fby on array or scalar? *)
        let optSizeTyArr = ArrayDestruct.get_array_const_size ePre.e_ty in
        match optSizeTyArr with
        | None -> eq::acc (* fby on a scalar *)
        | Some (_, tyElem) ->
        let lvarlhs = extract_data_out eq in
        let varIdlhs = Misc.assert_1 lvarlhs in

        let varIdPre = match ePre.e_desc with
          | Evar vid -> vid
          | _ -> failwith "Right part of a fby is not a variable"
        in

        (* Assumption - Safran: ePre is a variable and eConst is const^N *)
        (*let valstexpConst = match eConst.e_desc with
          | Econst st_exp -> (match st_exp.se_desc with
              | Sarray_power (se, _) -> se
              | _ -> failwith "Left part of a fby is not in const^size form"
            )
          | _ -> failwith "Left part of a fby is not a constant"
        in*)
        let rec get_valstexpConst st_exp = match st_exp.se_desc with
          | Sarray_power (se, _) -> se
          | Stuple l ->
            if (List.length l = 1) then
              get_valstexpConst (List.hd l)
            else failwith "Left part of a fby is not in const^size form"
          | _ -> failwith "Left part of a fby is not in const^size form"
        in
        let valstexpConst = get_valstexpConst st_exp in

        let optlIndVarScalLhs = try
          Hashtbl.find htblScalarVar varIdlhs
        with Not_found -> failwith ("varIdlhs = " ^ (Idents.name varIdlhs) ^ " not found")
        in
        let lIndVarScalLhs = match optlIndVarScalLhs with
          | None -> failwith ("Variable " ^ (Idents.name varIdlhs) ^ "is associated with nothing in htblScalarVar");
          | Some l -> l
        in
        let lVarScalLhs = get_list_vardecl_from_assoc_list lIndVarScalLhs in
        let optlIndVarScalPre = try
          Hashtbl.find htblScalarVar varIdPre
        with Not_found -> failwith ("varIdPre = " ^ (Idents.name varIdPre) ^ " not found")
        in
        let lIndVarScalPre = match optlIndVarScalPre with
          | None -> failwith ("Variable " ^ (Idents.name varIdPre) ^ "is associated with nothing in htblScalarVar");
          | Some l -> l
        in
        let lVarScalPre = get_list_vardecl_from_assoc_list lIndVarScalPre in
        assert((List.length lVarScalPre) = (List.length lVarScalLhs));

        (* We build the equations *)
        let lEqs = List.rev_map2 (fun varLhs varPre ->
          let eConstScal = Hept_utils.mk_exp (Econst valstexpConst)
            tyElem ~linearity:Linearity.Ltop in
          let eScalVarrhs = Hept_utils.mk_exp (Evar varPre.v_ident)
            tyElem ~linearity:Linearity.Ltop in
          let eScalFbyrhs = Hept_utils.mk_exp (Efby (eConstScal, eScalVarrhs))
            tyElem ~linearity:Linearity.Ltop in

          let eqdesc = Eeq(Evarpat varLhs.v_ident, eScalFbyrhs) in
          { eq_desc = eqdesc;
            eq_stateful = true;         (* fby *)
            eq_inits = Linearity.Lno_init;
            eq_annot = None;
            eq_loc = Location.no_location; }
        ) lVarScalLhs lVarScalPre in
        List.rev_append lEqs acc
      end
      | _ -> eq::acc  (* Not a fby *)
  ) [] mainnode.n_block.b_equs in

  (* Put these equation back into the mainnode *)
  let nBl = { mainnode.n_block with b_equs = nEqs } in
  let mainnode = { mainnode with n_block = nBl } in
  mainnode


(* ======================================================================= *)

(* Option to add "Var = read_int/float() | () = write_int/float(Var)"
    instead of having inputs and outputs - needed for Lopht *)
let option_generate_read_write_int_float = true (* TODO *)

let read_int_qname = { qual = Pervasives; name = "read_int" }
let read_float_qname = { qual = Pervasives; name = "read_float" }
let write_int_qname = { qual = Pervasives; name = "write_int" }
let write_float_qname = { qual = Pervasives; name = "write_float" }

(* If/then/else : res1 is return if ty is an int/bool, else res2 is returned *)
let ifte_int ty res1 res2 = match ty with
  | Tid x ->
    if ((x.name = "int") || (x.name="bool")) then res1 else
    if ((x.name="float") || (x.name="real")) then res2 else
    failwith ("ifte_int : Tid type unknown " ^ x.name)
  | _ -> failwith "ifte_int : type unknown"

(* Find the instance of an input/output variable, from the naming convention *)
(*    and produce the correct release/deadline tag from it *)
let get_tag vd =
  let strDelimEnd = Dirty_hyperperiod_expansion_Safran.strDelimEnd_varid in (* = "_sh" *)
  let lstrSplit = Str.split (Str.regexp strDelimEnd) (Idents.name vd.v_ident) in
  let strAftersh = List.hd (List.tl lstrSplit) in
  let lstrAftersh = Str.split (Str.regexp "_") strAftersh in
  let strNumInstance = List.hd lstrAftersh in
  let inst = int_of_string strNumInstance in
  "release(" ^ (string_of_int inst) ^ ") deadline(" ^ (string_of_int (inst+1)) ^ ")"


(* TODO: bug here !!! *)

(* Transform the input/output of the main node into local var + add equations read/write_int/float *)
let add_read_write_int_float mainnode =
  let linput = mainnode.n_input in
  let loutput = mainnode.n_output in

  (* var = read_int() / var = read_float() *)
  let nEqs = List.fold_left (fun acc invd ->
      let fname = ifte_int invd.v_type read_int_qname read_float_qname in
      let apprhs = Hept_utils.mk_app (Efun (fname,[])) in
      let erhsdesc = Eapp(apprhs, [], None) in
      let erhs = Hept_utils.mk_exp erhsdesc invd.v_type ~linearity:Linearity.Ltop in

      (* Tag *)
      let annotReleaseDeadline =
        if (!Compiler_options.hyperperiod) then
          Some (get_tag invd)
        else None
      in

      let plhs = Evarpat invd.v_ident in
      let eqdesc = Eeq (plhs, erhs) in
      let nEqin = { eq_desc = eqdesc; eq_stateful = false;
                   eq_inits = Lno_init; eq_annot = annotReleaseDeadline ; eq_loc = Location.no_location } in
      nEqin::acc
    ) mainnode.n_block.b_equs linput in

  (* () = write_int(var) / () = write_float(var) *)
  let void_type = Tprod [] in
  let nEqs = List.fold_left (fun acc outvd ->
      let fname = ifte_int outvd.v_type write_int_qname write_float_qname in
      let expArg = Hept_utils.mk_exp (Evar outvd.v_ident) outvd.v_type ~linearity:Linearity.Ltop in
      let lexpArg = expArg::[] in

      let apprhs = Hept_utils.mk_app (Efun (fname,[])) in
      let erhsdesc = Eapp(apprhs, lexpArg, None) in
      let erhs = Hept_utils.mk_exp erhsdesc void_type ~linearity:Linearity.Ltop in
      
      (* Tag *)
      let annotReleaseDeadline =
        if (!Compiler_options.hyperperiod) then
          Some (get_tag outvd)
        else None
      in
      let plhs = Etuplepat [] in
      let eqdesc = Eeq (plhs, erhs) in
      let nEqout = { eq_desc = eqdesc; eq_stateful = false;
                   eq_inits = Lno_init; eq_annot = annotReleaseDeadline; eq_loc = Location.no_location } in
      nEqout::acc
    ) nEqs loutput in

  (* Build the new main node *)
  let nLoc = List.rev_append mainnode.n_output
    (List.rev_append mainnode.n_input mainnode.n_block.b_local) in

  let nBl = {mainnode.n_block with b_local = nLoc; b_equs = nEqs } in
  let new_nd = { mainnode with n_input = []; n_output = []; n_block = nBl } in
  new_nd


(* ======================================================================= *)

(* Main functions *)
let node nd =
  let lgroupEq = group_equation nd in

  (* TODO DEBUG *)
  Format.fprintf (Format.formatter_of_out_channel stdout) "ping - group equation obtained\n@?";

  let subnodesgr = build_subnodes lgroupEq nd in

  (* TODO DEBUG *)
  Format.fprintf (Format.formatter_of_out_channel stdout) "ping - subnodes built\n@?";
  
  (* Creating the hashtable associating a input/output with a potential list of new scalar var decl *)
  let numInOutVar = List.fold_left (fun acc (sn,_) -> 
    acc + (List.length sn.n_input) + (List.length sn.n_output)
  ) 0 subnodesgr in
  let htblScalarVar = Hashtbl.create numInOutVar in

  let (subnodesgr, htblScalarVar) = scalar_subnodes_interface false htblScalarVar subnodesgr in
  let new_nd = build_mainnode subnodesgr nd in

  let new_nd = if (option_generate_scalar_interfaces) then
      scalar_mainnode htblScalarVar new_nd
    else new_nd in
  let new_nd = if (option_generate_read_write_int_float) then
      add_read_write_int_float new_nd
    else new_nd in

  

  (* Don't add the "pre" subnodes, whose equation is already in the main node *)
  let subnodes = List.fold_left (fun acc (sn,gr) ->
   if (gr.is_pre) then acc else sn::acc
  ) [] subnodesgr in

  new_nd :: subnodes

let program p =
  let npdesc = List.fold_left (fun acc pdesc ->
  	 match pdesc with
  	   | Pnode nd ->
        let new_nd = node nd in
        let new_pnode = List.rev_map (fun nd1 -> Pnode nd1) new_nd in
        List.rev_append new_pnode acc
  	   | _ -> pdesc::acc
  	) [] p.p_desc in

  { p with p_desc = npdesc }
