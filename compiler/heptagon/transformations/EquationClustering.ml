(* Equation clustering - group equation together, in order to coarsen the granularity of the application *)

(** Heuristics:
    * If an equation uses only one data, merge it with the producer equation
    * If the output of an equation is only used once, merge it with the consumer equation
  *)
open Heptagon
open Hept_mapfold

exception Equation_not_in_Eeq_form

let debug_info = true (* TODO DEBUG *)


type group_eq = {
  name : string;    (* Name of the group of equation *)
  lequ : eq list;   (* List of equations contained inside this group *)
  instance : int;   (* Number of the instance (we cannot merge different instances) *)

  (* The two next field are temporary values, computed only after the dataTable *)
  l_inp : var_ident list; (* Inputs of a group of equation *)
  l_out : var_ident list; (* Outputs of a group of equation *)
  l_loc : var_ident list; (* Local var of a group of equation *)
}

let mk_group_eq n leq i = { name = n; lequ = leq; instance = i;
    l_inp = []; l_out = []; l_loc = [] }

let merge_group_eq gEq1 gEq2 =
  if (gEq1.instance != gEq2.instance) then
    failwith "Merging with 2 different instances not allowed"
  else
    let (l_loc_in_gr1, l_in_gr1) = List.partition (fun vid -> 
      List.mem vid gEq2.l_out
    ) gEq1.l_inp in
    let (l_loc_in_gr2, l_in_gr2) = List.partition (fun vid ->
      List.mem vid gEq1.l_out
    ) gEq2.l_inp in

    (* TODO: /!\ output of the program *)
    let (l_loc_out_gr1, l_out_gr1) = List.partition (fun vid ->
      (List.mem vid gEq2.l_inp)
    ) gEq1.l_out in
    let (l_loc_out_gr2, l_out_gr2) = List.partition (fun vid ->
      List.mem vid gEq1.l_inp
    ) gEq2.l_out in
    
    { name = gEq1.name; lequ = gEq1.lequ @ gEq2.lequ; instance = gEq1.instance;
      l_inp = l_in_gr1 @ l_in_gr2;
      l_out = l_out_gr1 @ l_out_gr2;
      l_loc = gEq1.l_loc @ gEq2.l_loc @ l_loc_in_gr1 @ l_loc_in_gr2 @ l_loc_out_gr1 @ l_loc_out_gr2;
    }

(* -------------- *)

(* Name management*)
let name_counter = ref 0

let new_group_name s inst =
  name_counter := !name_counter +1;
  (s ^ (string_of_int !name_counter) ^ "_sh" ^ inst)

(* Get a variable from the lhs. If it is void, returns None *)
let rec get_lhs_var p = match p with
  | Etuplepat pl -> if (pl=[]) then None else get_lhs_var (List.hd pl)
  | Evarpat vid -> Some vid

(* Get a variable from the rhs. Only called then the lhs is void.
   If there is no variable on the rhs either, throw an error *)
let rec get_rhs_var e =
  (* TODO: not enough !!! (ex: if there is a pre) BUT, because of normalization, works if lhs is void *)
  let edesc_get_rhs funs acc ed = match ed with
    | Evar vid -> ed, Some vid
    | _ -> Hept_mapfold.edesc funs acc edesc
  in
  let funs_get_rhs_var = {Hept_mapfold.defaults with edesc = edesc_get_rhs} in
  let _,acc = funs_get_rhs_var.exp e in
  match acc with
   | None -> failwith "Equation does not have any variable on the lhs and rhs"
   | Some vid -> vid

(* Get the last element of a list *)
let rec get_last l = match l with
 | [] -> raise ListEmpty
 | x::[] -> x
 | h::t -> get_last t

(* Getter to pattern-match an equation *)
let get_lhs_rhs_eq e = match e with
  | Eeq (lhs, rhs) -> (lhs, rhs)
  | _ -> raise Equation_not_in_Eeq_form


(* Examine the equation to figure out which instance of duplication we are talking about *)
let get_instance_num e =
  let (lhs,rhs) = get_lhs_rhs_eq e in
  let vidopt = get_lhs_var lhs in
  let vid = match vidopt with
    | None -> get_rhs_var rhs in
    | Some vlhs -> vlhs
  in
  (* Instance number currently encoded at the end of vid *)
  let strDelimEnd = Dirty_hyperperiod_expansion_Safran.strDelimEnd_varid in (* = "_sh" *)
  let lstrSplit = Str.split (Str.regex strDelimEnd) (Names.name vid) in
  let strNum = get_last lstrSplit in
  let instNum =int_of_string strNum in
  instNum


(* Initial construction of lgroupEq *)
let build_group_single_eq e =
  let i = get_instance_num e in
  let n = new_group_name "group_" i in
  mk_group_eq n [e] i

(* -------------- *)

(* Get all the data_in of an equation *)
let extract_data_in eq =
  let edesc_extract_data_in funs acc edesc = match edesc with
    | Evar vid -> edesc, vid::acc
    | _ -> Hept_mapfold.edesc funs acc edesc
  in
  let (_, rhs) = get_lhs_rhs_eq eq in
  let funs_data_in = { Hept_mapfold.defaults with edesc = edesc_extract_data_in} in
  let _, acc = funs_data_in.eq funs_data_in [] eq in
  acc

(* Get all the data_out of an equation *)
let extract_data_out eq =
  let rec get_list_vid plhs = match plhs with
    | Etuplepat pl -> List.fold_left (fun acc p1 -> acc@(get_list_vid p1)) [] pl
    | Evarpat vid -> vid::[]
  in
  let (lhs, _) = get_lhs_rhs_eq eq in
  get_list_vid lhs

(* Build datainoutEq and depTable, associating the equation with the data & vice versa *)
let buildDataTable nd lgroupEq =
  let depTable = Hashtbl.create (List.length nd.n_block.b_local) in
  let datainoutEq = Hashtbl.create (List.length nd.n_block.b_equs) in
  let lgroupEq = List.fold_left (fun acc gr ->
    let eq = List.hd gr.lequ in
    let eqDataIn = extract_data_in eq in
    let eqDataOut = extract_data_out eq in

    (* Log information per equations*)
    Hashtbl.add datainoutEq (eqDataIn, eqDataOut);

    (* Update inforamtion per variables *)
    List.iter (fun nvarin ->
      try
        let (info_prod, info_cons) = Hashtbl.find depTable nvarin in
        Hashtbl.add depTable nvarin (info_prod, eq::info_cons)
      with Not_found ->
       Hashtbl.add depTable nvarin ([],eq::[])
    ) eqDataIn;
    List.iter (fun nvarout ->
      try
        let (info_prod, info_cons) = Hashtbl.find depTable nvarout in
        if (info_prod!=[]) then raise Data_produced_twice else
        Hashtbl.add depTable nvarout (eq::[],info_cons)
      with Not_found ->
       Hashtbl.add depTable nvarout (eq::[],[])
    ) eqDataOut;
    { gr with l_inp = eqDataIn; l_out = eqDataOut }::acc
  ) lgroupEq;
  (lgroupEq, depTable, datainoutEq)


(* TODO: replace searchs by dataTable usage ??? *)


(* ------------- *)

(* Heuristic #1 *)
let heuristic_merge_single_use lgroupEq =
  let rec search_merge_group_single_use dataOut grToMerge result lgr = match lgr with
    | [] -> (false, result)
    | hgr::tgr ->
      if (List.mem dataOut hgr.l_inp) then
        result@((merge_group_eq hgr grToMerge)::tgr)
      else
        search_merge_group_single_use dataOut grToMerge (hgr::result) tgr 
  in
  let rec heuristic_merge_single_use_aux lgroupRes lgroupRem = match lgroupRem with
    | [] -> lgroupRes
    | gr::rest -> begin
      (* Default case *)
      if (not ((List.length gr.l_out) = 1)) then
        heuristic_merge_single_use_aux (gr::lgroupRes) rest
      else
        (* gr needs to be merged with another group (from lgroupRes or lgroupRem) *)
        let dataOut = List.hd gr.l_out in
        let (found, lgroupRes) = search_merge_group_single_use dataOut gr [] lgroupRes in
        if (found) then heuristic_merge_single_use_aux lgroupRes rest else
        (* The searched group is inside the list of group which was not treated yet *)
        let (found, rest) = search_merge_group_single_use dataOut gr [] rest in
        assert(found);
        heuristic_merge_single_use_aux lgroupRes rest
    end
  in
  heuristic_merge_single_use_aux [] lgroupEq


(* Heuristic #2 *)
let heuristic_merge_single_prod lgroupEq =
  let rec search_merge_group_single_prod dataIn grToMerge result lgr = match lgr with
    | [] -> (false, result)
    | hgr::tgr ->
      if (List.mem dataIn hgr.l_out) then
        result@((merge_group_eq hgr grToMerge)::tgr)
      else
       search_merge_group_single_prod dataIn grToMerge (hgr::result) tgr
  in
  let rec heuristic_merge_single_prod_aux lgroupRes lgroupRem = match lgroupRem with
    | [] -> lgroupRes
    | gr::rest -> begin
      (* Defautl case*)
      if (not ((List.length gr.l_inp) = 1)) then
        heuristic_merge_single_prod_aux (gr::lgroupRes) rest
      else
        let dataIn = List.hd gr.l_inp in
        let (found, lgroupRes) = search_merge_group_single_prod dataIn gr [] lgroupRes in
        if (found) then heuristic_merge_single_prod_aux lgroupRes rest else
        (* The searched group is inside the list of group which was not treated yet *)
        let (found, rest) = search_merge_group_single_prod dataIn gr [] rest in
        assert(found);
        heuristic_merge_single_prod_aux lgroupRes rest
    end
  in
  heuristic_merge_single_prod_aux [] lgroupEq



(* First step: grouping equations together *)
let group_equation nd =
  (* Init *)
  let lgroupEq = List.map (fun eq ->
    build_group_single_eq eq 
  ) nd.n_block.b_equs in

  (* Build dataTable - associate each varId to the equations interacting which them *)
  let (lgroupEq, depTable, dataInOutEq) = buildDataTable nd lgroupEq in
  let vidOut = List.map (fun vd -> vd.v_ident) nd.n_output in

  if (debug_info) then
    Format.fprintf "lgroupEq.size (avant heuristique 1) = %i" (List.length lgroupEq);

  (* First heuristic: merge if an eq use a single variable *)
  let lgroupEq = heuristic_merge_single_use vidOut lgroupEq in

  if (debug_info) then
    Format.fprintf "lgroupEq.size (heuristique 1) = %i" (List.length lgroupEq);

  (* Second heuristic: merge if an eq produce a single variable *)
  let lgroupEq = heuristic_merge_single_prod vidOut lgroupEq in

  if (debug_info) then
    Format.fprintf "lgroupEq.size (heuristique 2) = %i" (List.length lgroupEq);

  (* We now deal with potential output variable of the program,
      which might have become a local variable of a group *)
  let lglobalOut = List.map (fun vd -> v.v_ident) nd.n_output in
  let lgroupEq = List.map (fun grEq ->
      let (lvid_newout, lvid_loc) = List.partition
        (fun vid -> List.mem vid lglobalOut) grEq.l_loc in
      { grEq with l_out = lvid_newout@grEq.l_out, l_loc = lvid_loc}
    ) lgroupEq in

  lgroupEq

(* ======================================================================= *)

(* Variable declaration search *)
let rec search_for_vardecl lvdec vid = match lvdec with
  | [] -> None
  | h::t ->
    if (h.v_ident=vid) then Some h
    else search_for_vardecl t vid

let get_vardecl nd lvid =
  List.map (fun vid ->
    let vdecopt = search_for_vardecl nd.n_input vid in
    match vdecopt with
      | Some vdec -> vdec
      | None ->
    let vdecopt = search_for_vardecl nd.n_output vid in
    match vdecopt with
      | Some vdec -> vdec
      | None ->
    let vdecopt = search_for_vardecl nd.n_block.b_local vid in
    match vdecopt with
      | Some vdec -> vdec
      | None -> failwith ("EquationClustering :: get_vardecl => vid " ^ vid ^ " was not found in the node")
  ) lvid


(* For each group of equation lgroupEq, build the corresponding subnode *)
let build_subnodes lgroupEq nd =
  let subnodes = List.fold_left (fun acc grEq ->
    let lvidIn = grEq.l_inp in
    let lvidOut = grEq.l_out in
    let lvidLoc = grEq.l_loc in

    (* Retrieves the variable declaration from nd *)
    let lVarin = get_vardecl nd lvidIn in
    let lVarout = get_vardecl nd lvidOut in
    let lVarloc = get_vardecl nd lvidLoc in

    (* Creating the objects *)
    let bl = Hept_utils.mk_block ~stateful:nd:stateful ~locals:lVarloc grEq.lequ in
    let sn = Hept_utils.mk_node ~typeparamdesc:nd.typeparamdecs ~input:lVarin ~output:lVarout
      ~stateful:nd.stateful grEq.name bl in
    sn
  ) lgroupEq in
  subnodes

(* Note: if we want the signatures of these subnodes, Hept_utils.signature_of_node *)

let rec remove_all_list lToRemove res l = match l with
 | [] -> res
 | h::t ->
  if (List.mem h lToRemove) then (remove_all_list lToRemove res t)
  else (remove_all_list lToRemove (h::res) t)


(* Building the main node *)
let build_mainnode subnodes nd =
  (* Note: all equations are inside the subnodes/lgroupEq *)
  let lVarlocOutmainNode = List.fold_left (fun acc snd ->
    (snd.n_output)@acc (* No duplication *)
  ) [] subnodes in
  let lVarloc = remove_all_list nd.n_output lVarlocOutmainNode in

  let lequ = List.fold_left (fun acc sn ->
    
    (* rhs of equation *)
    let app_rhs = Efun (sn.name,[]) in
    let lin_rhs = List.map (fun vd ->
      let edesc_in_rhs = Evar vd.v_ident in
      Hept_utils.mk_exp edesc_in_rhs vd.v_type ~linearity:Linearity.LTop
    ) snd.n_input in
    let rhs_edesc = Eapp (app_rhs, lin_rhs, None) in
    let ty_rhs = Types.Tprod (List.map (fun vd -> vd.v_type) sn.n_output) in
    let rhs = Hept_utils.mk_exp rhs_edesc ty_rhs ~linearity:Linearity.LTop in

    (* lhs of equation *)
    let snOutvid = List.map (fun vd -> vd.v_ident) sn.n_output in
    let plhs = if ((List.length sn.n_output)=1) then
      Evarpat (List.hd snOutvid) else Etuplepat snOutvid
    in

    let neq = Hept_utils.mk_simple_eq plhs rhs in
    neq::acc
  ) subnodes in

  let bl = Hept_utils.mk_block ~stateful:nd.stateful ~locals:lVarloc lequ in

  let mn = Hept_utils.mk_node ~typeparamdesc:nd.typeparamdecs ~input:nd.input ~output:nd.output
    ~stateful:nd.stateful mainnode_name bl in


(* ======================================================================= *)

(* Main functions *)
let node nd =
  let lgroupEq = group_equation nd in
  let subnodes = build_subnodes lgroupEq nd in
  let new_nd = build_mainnode subnodes nd in
  new_nd :: subnodes


let program p =
  let npdesc = List.fold_left (fun acc pdesc ->
  	 match pdesc with
  	   | Pnode nd -> (node nd)@acc
  	   | _ -> pdesc::acc
  	) [] p.p_desc in

  { p with p_desc = npdesc }
