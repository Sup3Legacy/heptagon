(* Equation clustering - group equation together, in order to coarsen the granularity of the application *)

(** Heuristics:
    * If an equation uses only one data, merge it with the producer equation
    * If the output of an equation is only used once, merge it with the consumer equation
  *)
open Idents
open Heptagon
open Hept_mapfold

exception Equation_not_in_Eeq_form
exception ListEmpty
exception Data_produced_twice
exception GroupEqNotFound


let debug_info = true (* TODO DEBUG *)


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
    | h::t -> if (h=elem) then (true,res@t)
      else remove_list_aux (h::res) t elem
  in
  if (actbool) then remove_list_aux [] l elem else (true,l)


(* Get the last element of a list *)
let rec get_last l = match l with
 | [] -> raise ListEmpty
 | x::[] -> x
 | _::t -> get_last t


(* -----------------------------------------------------------  *)

type group_eq = {
  name : string;    (* Name of the group of equation *)
  lequ : eq list;   (* List of equations contained inside this group *)
  instance : int;   (* Number of the instance (we cannot merge different instances) *)

  (* The two next field are temporary values, computed only after the dataTable *)
  l_inp : var_ident list;                (* Inputs of a group of equation *)
  l_out : (var_ident * (eq list)) list;  (* Outputs of a group of equation + equations outside of the group using it *)
  l_loc : var_ident list;                (* Local var of a group of equation *)
}

let mk_group_eq n leq i = { name = n; lequ = leq; instance = i;
    l_inp = []; l_out = []; l_loc = [] }

(* let print_group_eq ff geq =
  let print_varideq ff =
  Format.fprintf ff "[[in: (%a) | out: (%a) | num_loc: %i | num_eq: %i ]]\n@?"
  (Pp_tools.print_list Global_printer.print_ident "" "" "") l_inp
  print_list_varideql l_out
  (List.length l_loc) (List.length lequ) *)


(* Hashtbl maintained through the transformation: *)
(*  * dataTable : var_ident --> ( leq_Prod_data , leq_Cons_data ) *)
(*  * eq2grTable : eq --> gr_eq *)
let merge_group_eq eq2grTable gEq1 gEq2 =
  let rec is_varid_in_l_out vid l_out = match l_out with
   | [] -> false
   | (hid,_)::t -> if (vid=hid) then true else is_varid_in_l_out vid t 
  in

  if (gEq1.instance != gEq2.instance) then
    failwith "Merging with 2 different instances not allowed"
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
    let lin12 = gEq1.l_inp @ gEq2.l_inp in
    let lout12 = gEq1.l_out @ gEq2.l_out in
    let lEqu3 = gEq1.lequ @ gEq2.lequ in

    let lin3 = List.filter (fun vid ->
      not (is_varid_in_l_out vid lout12)
    ) lin12 in

    let (lout3, l_new_loc) = List.fold_left (fun (acc_out, acc_loc) (vid, lCons) ->
      (* We check if there is still equation outside of the group using vid *)
      let lConsRem = remove_all_list lEqu3 [] lCons in
      if (lConsRem=[]) then (acc_out, vid::acc_loc)
      else ((vid, lConsRem)::acc_out, acc_loc)
    ) ([],[]) lout12 in

    let gr3 = { name = gEq1.name; lequ = lEqu3; instance = gEq1.instance;
      l_inp = lin3;
      l_out = lout3;
      l_loc = gEq1.l_loc @ gEq2.l_loc @ l_new_loc;
    } in

    (* Update of eq2grTable *)
    List.iter (fun eq -> Hashtbl.add eq2grTable eq gr3) lEqu3;
    gr3

(* -------------- *)

(* Name management*)
let name_counter = ref 0

let new_group_name s inst =
  name_counter := !name_counter +1;
  (s ^ (string_of_int !name_counter) ^ "_sh" ^ (string_of_int inst))

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

(* Initial construction of lgroupEq
   Note: inputs/outputs/locals not extracted*)
let build_group_single_eq e =
  let i = get_instance_num e in
  let n = new_group_name "group_" i in
  let gr = mk_group_eq n [e] i in
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
    | Etuplepat pl -> List.fold_left (fun acc p1 -> acc@(get_list_vid p1)) [] pl
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
    let incomplete_dataOut = List.map (fun eq -> (eq,[])) eqDataOut in
    { gr with l_inp = eqDataIn; l_out = incomplete_dataOut}::acc
  ) [] lgroupEq in

  (* Now that "depTable" is completed, we fill the missing dataOut info *)
  let lgroupEq = List.map (fun grEq ->
    let complete_dataOut = List.map
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

(* Heuristic #1 *)
let heuristic_merge_single_use _ eq2grTable lgroupEq =
  let rec heuristic_merge_single_use_aux lgroupRes lgroupRem = match lgroupRem with
    | [] -> lgroupRes
    | gr::rest -> begin
      (* Default case: more than one output , or output used more than once *)
      if (not ((List.length gr.l_out) = 1)) then
        heuristic_merge_single_use_aux (gr::lgroupRes) rest
      else
      (* Check that there is only one use *)
      let (dataOut, infoCons) = List.hd gr.l_out in
      if (not ((List.length infoCons) = 1)) then
        heuristic_merge_single_use_aux (gr::lgroupRes) rest
      else
        (* Merging ! *)
        let eqCons = List.hd infoCons in
        let grToMerge = try Hashtbl.find eq2grTable eqCons
        with Not_found -> (
           Format.eprintf "Group of equation not found, for dataOut = %s\n@?" (Idents.name dataOut);
          raise GroupEqNotFound)
        in
        (* Merge not allowed in the instance is different *)
        if (grToMerge.instance != gr.instance) then
          heuristic_merge_single_use_aux (gr::lgroupRes) rest else

        let ngr = merge_group_eq eq2grTable gr grToMerge in
        
        let (found, lgroupRes) = remove_list true lgroupRes grToMerge in
        let (found, rest) = remove_list (not found) rest grToMerge in
        assert(found);
        heuristic_merge_single_use_aux (ngr::lgroupRes) rest
    end
  in
  heuristic_merge_single_use_aux [] lgroupEq


(* Heuristic #2 *)
let heuristic_merge_single_prod dataTable eq2grTable lgroupEq =
  let rec heuristic_merge_single_prod_aux lgroupRes lgroupRem = match lgroupRem with
    | [] -> lgroupRes
    | gr::rest -> begin
      (* Defautl case*)
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

        (* Merge not allowed in the instance is different *)
        if (grToMerge.instance != gr.instance) then
          heuristic_merge_single_prod_aux (gr::lgroupRes) rest else

        let ngr = merge_group_eq eq2grTable gr grToMerge in

        let (found, lgroupRes) = remove_list true lgroupRes grToMerge in
        let (found, rest) = remove_list (not found) rest grToMerge in
        assert(found);
        heuristic_merge_single_prod_aux (ngr::lgroupRes) rest
    end
  in
  heuristic_merge_single_prod_aux [] lgroupEq


(* First step: grouping equations together *)
let group_equation nd =
  if (debug_info) then
    Format.fprintf (Format.formatter_of_out_channel stdout) "lEq.size = %i\n@?" (List.length nd.n_block.b_equs)
  else ();

  (* Init *)
  let lgroupEq = List.map (fun eq ->
    build_group_single_eq eq 
  ) nd.n_block.b_equs in

  (* Build dataTable - associate each varId to the equations interacting which them *)
  (* dataTable : var_ident --> ( leq_Prod_data , leq_Cons_data ) *)
  (* eq2grTable : eq --> group_eq *)
  let (lgroupEq, dataTable, eq2grTable) = buildDataTable nd lgroupEq in

  if (debug_info) then
    Format.fprintf (Format.formatter_of_out_channel stdout) "lgroupEq.size (avant heuristique 1) = %i\n@?" (List.length lgroupEq)
  else ();

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

  (* We now deal with potential output variable of the program,
      which might have become a local variable of a group *)
  let lglobalOut = List.map (fun vd -> vd.v_ident) nd.n_output in
  let lgroupEq = List.map (fun grEq ->
      let (lvid_newout, lvid_loc) = List.partition
        (fun vid -> List.mem vid lglobalOut) grEq.l_loc in
      let lvid_newout = List.map (fun vid -> (vid,[])) lvid_newout in
      { grEq with l_out = lvid_newout@grEq.l_out; l_loc = lvid_loc}
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

  let subnodes = List.fold_left (fun acc grEq ->
    let lvidIn = grEq.l_inp in
    let lvidOut = List.map (fun (vid,_) -> vid) grEq.l_out in
    let lvidLoc = grEq.l_loc in

    (* Retrieves the variable declaration from nd *)
    let lVarin = get_vardecl tblvdNd lvidIn in
    let lVarout = get_vardecl tblvdNd lvidOut in
    let lVarloc = get_vardecl tblvdNd lvidLoc in

    (* TODO: improve that? *)

    (* Creating the objects *)
    let bl = Hept_utils.mk_block ~stateful:nd.n_stateful ~locals:lVarloc grEq.lequ in
    let snname = Modules.fresh_value "clustering" grEq.name in
    let sn = Hept_utils.mk_node ~typeparamdecs:nd.n_typeparamdecs ~input:lVarin ~output:lVarout
      ~stateful:nd.n_stateful ~param:nd.n_params snname bl in

    sn::acc
  ) [] lgroupEq in
  subnodes


(* Note: if we want the signatures of these subnodes, Hept_utils.signature_of_node *)


(* Building the main node *)
let build_mainnode subnodes nd =
  (* Note: all equations are inside the subnodes/lgroupEq *)
  let lVarlocOutmainNode = List.fold_left (fun acc snd ->
    (snd.n_output)@acc (* No duplication *)
  ) [] subnodes in
  let lVarloc = remove_all_list nd.n_output [] lVarlocOutmainNode in

  let lequ = List.fold_left (fun acc sn ->
    
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

    let neq = Hept_utils.mk_simple_equation plhs rhs in
    neq::acc
  ) [] subnodes in

  let bl = Hept_utils.mk_block ~stateful:nd.n_stateful ~locals:lVarloc lequ in

  let mn = Hept_utils.mk_node ~typeparamdecs:nd.n_typeparamdecs ~input:nd.n_input ~output:nd.n_output
    ~stateful:nd.n_stateful nd.n_name bl in
  mn


(* ======================================================================= *)

(* Main functions *)
let node nd =
  let lgroupEq = group_equation nd in

  (* TODO DEBUG *)
  Format.fprintf (Format.formatter_of_out_channel stdout) "ping - group equation obtained\n@?";

  let subnodes = build_subnodes lgroupEq nd in

  (* TODO DEBUG *)
  Format.fprintf (Format.formatter_of_out_channel stdout) "ping - subnodes built\n@?";

  let new_nd = build_mainnode subnodes nd in
  new_nd :: subnodes

let program p =
  let npdesc = List.fold_left (fun acc pdesc ->
  	 match pdesc with
  	   | Pnode nd ->
        let new_nd = node nd in
        let new_pnode = List.map (fun nd1 -> Pnode nd1) new_nd in
        new_pnode@acc
  	   | _ -> pdesc::acc
  	) [] p.p_desc in

  { p with p_desc = npdesc }
