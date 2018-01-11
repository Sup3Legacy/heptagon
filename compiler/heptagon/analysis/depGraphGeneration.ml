(* Generation of the dependence graph from the system (Safran UC) *)
(* To be pluged in tempodep? + good way to analyse the relations *)
open Format
open Idents
open Heptagon
open Hept_mapfold

exception Data_produced_twice
exception Equation_not_in_Eeq_form

(* Dependence graph data structure *)
type func_depgraph =
  | Ext_node of string			(* External function called *)
  | Operator of string		(* Other kind of equation *)

type rate = string

type sched_info = {
  r : rate;
  shift : int;
}

type info_node = {
  kinfo : func_depgraph;
  wcet : int option;
  sinfo : sched_info option;
}
(* long-term todo: make "info_node" more modular, with modules and functors?
   -> Not useful for one application, but cleaner *)


type depgraph_node = {
  name : string;
  data_in : string list;
  data_out : string list;
  
  info : info_node;
}

type depgraph_edge = {
  name_var : string;
  e_prod : depgraph_node;
  e_cons : depgraph_node list;
}

type depgraph = {
  nodes : depgraph_node list;
  edges : depgraph_edge list;
}


(* =================================================================== *)
(* =================================================================== *)
(* =================================================================== *)
(* Pretty-printer - to Dotty *)

let get_color dgn = "black" (* By default *)

let print_node_dotty ff node =
  fprintf ff "\t%s [label=\"%s\"; color=%s];\n@?"
    node.name  node.name  (get_color node)

let print_edges_dotty ff edge =
  List.iter (fun cons ->
    fprintf ff "\t%s -> %s;\n@?" edge.e_prod.name cons.name
  ) edge.e_cons

let print_depgraph_dotty ff gr =
  fprintf ff "digraph depgraph {\n@?";
  List.iter (fun dgn -> fprintf ff "%a" print_node_dotty dgn) gr.nodes;
  List.iter (fun dne -> fprintf ff "%a" print_edges_dotty dne) gr.edges;
  fprintf ff "}\n@?"


(* =================================================================== *)
(* Pretty-printer - to common format (~ print_AST) *)

let print_opt pp ff opt = match opt with
  | None -> fprintf ff "None"
  | Some a -> fprintf ff "Some %a" pp a

let print_int ff i = fprintf ff "%i" i
let print_string ff s = fprintf ff "%s" s

let print_list pp ff l =
  let rec print_list_aux pp ff bfirst l = match l with
    | [] -> ()
    | h::t -> 
      if (bfirst) then () else fprintf ff ", ";
      fprintf ff "%a" pp h;
      print_list_aux pp ff false t
  in
  print_list_aux pp ff true l

(* Information of a node *)
let print_info_func_depgraph ff kinfo = match kinfo with
  | Ext_node s -> fprintf ff "Ext_func(%s)" s
  | Operator s -> fprintf ff "Operator(%s)" s

let print_info_sched ff sinfo =
  fprintf ff "%s %i" sinfo.r sinfo.shift

let print_info_node ff info =
  fprintf ff "%a, %a, %a"
    print_info_func_depgraph info.kinfo
    (print_opt print_int) info.wcet
    (print_opt print_info_sched) info.sinfo

let print_list_data ff lstr = print_list print_string ff lstr

(* Main functions *)
let print_node_text ff dgn =
  fprintf ff "\t%s [%a] [%a] (%a)"
    dgn.name
    print_list_data dgn.data_in
    print_list_data dgn.data_out
    print_info_node dgn.info

let print_id_node ff node = print_string ff node.name

let print_edges_text ff edge =
  fprintf ff "\t%s (%s) -> (%a)"
    edge.name_var
    edge.e_prod.name
    (print_list print_id_node) edge.e_cons

let print_depgraph_text ff gr =
  fprintf ff "Nodes:\n";
  List.iter (fun dgn -> fprintf ff "%a\n" print_node_text dgn) gr.nodes;
  fprintf ff "\n\nEdges:\n";
  List.iter (fun dne -> fprintf ff "%a\n" print_edges_text dne) gr.edges;
  fprintf ff "\n@?"

(* -------------------------------------------------------------------------------------------- *)
(* Dependence graph builder *)

(* First pass: building the nodes corresponding to the equation *)
let count = ref 0
let get_name_node eq =
  let name = "node_" ^ (string_of_int (!count)) in
  count := !count+1; name


let get_name_from_varident (vid:Idents.var_ident) = Idents.name vid

let rec get_outvar_name pat = match pat with
  | Etuplepat lp -> List.fold_left (fun acc p -> acc@(get_outvar_name p)) [] lp
  | Evarpat vid -> (get_name_from_varident vid)::[]  


let is_external_function rhs = match rhs.e_desc with
  | Eapp (ap, larg, opt) -> begin
    match ap.a_op with
      | Efun (fname,_) | Enode (fname, _) ->
        if (fname.Names.qual=Names.LocalModule) then None else
        if (fname.Names.qual=Names.Pervasives) then None else
        (Some fname) (* Note: approximation here *)
      | _ -> None
    end
  | _ -> None


let get_invar_name rhs =
  let edesc_invar_name funs acc ed = match ed with
    | Evar vid | Elast vid -> ed, (get_name_from_varident vid)::acc
    | _ -> ed, acc
  in
  let funs_gather_invar = { Hept_mapfold.defaults with edesc=edesc_invar_name} in
  let _, acc = Hept_mapfold.exp funs_gather_invar [] rhs in
  acc


let build_dep_graph_node eq =
  let name_node = get_name_node eq in
  
  let (dout_node, din_node, kinfo) = match eq.eq_desc with
    | Eeq (plhs, rhs) -> begin
     let lstrout = get_outvar_name plhs in
     let lstrin = get_invar_name rhs in
     let isExtFuncOpt = is_external_function rhs in
     let kinfo = match isExtFuncOpt with
       | None -> Operator
         ""
         (* TODO: find a good way to encode any expression in an exportable way... :/ *)
         (* TODO: use ast pretty-printer here? <============== More detailled? AST with holes for inputs? *)
       | Some fname -> Ext_node fname.Names.name
     in
     (lstrout, lstrin, kinfo)
     end
    | _ -> raise Equation_not_in_Eeq_form
  in
  
  (* Building *)
  let ninfo = {kinfo = kinfo; wcet = None; sinfo = None} in
  let dgnode = {name = name_node; data_in = din_node; data_out = dout_node; info = ninfo} in
  dgnode


(* Build the dependence graph of nd *)
let node nd =
  (* Nodes *)
  let lnodes = List.fold_left
    (fun acc eq ->
      (build_dep_graph_node eq):: acc
    ) [] nd.n_block.b_equs
  in
  let empty_gr = { nodes = lnodes; edges = [] } in
  
  (* Edges ~ variables of the program *)
  (* DepTable regroup the information % the data of the program *)
  let depTable = Hashtbl.create (List.length nd.n_block.b_local) in
  List.iter (fun ngr ->
    List.iter (fun nvarin ->
      try
        let (info_prod, info_cons) = Hashtbl.find depTable nvarin in
        Hashtbl.add depTable nvarin (info_prod, ngr::info_cons)
      with Not_found ->
       Hashtbl.add depTable nvarin ([],ngr::[])
    ) ngr.data_in;
    List.iter (fun nvarout ->
      try
        let (info_prod, info_cons) = Hashtbl.find depTable nvarout in
        if (info_prod!=[]) then raise Data_produced_twice else
        Hashtbl.add depTable nvarout (ngr::[],info_cons)
      with Not_found ->
       Hashtbl.add depTable nvarout (ngr::[],[])
    ) ngr.data_out
  ) lnodes;

  let gr = Hashtbl.fold
    (fun namevar (info_prod, info_cons) gr ->
      (* Default case: input/output data *)
      if ((List.length info_prod)=0) || ((List.length info_cons)=0) then gr else
      begin
        assert((List.length info_prod) = 1);
        let e = {name_var = namevar; e_prod = (List.hd info_prod); e_cons = info_cons} in
        { gr with edges = e::gr.edges}
      end
    ) depTable empty_gr in
  gr


let program p =
  let ldepgraph = List.fold_left
    (fun acc pdesc -> match pdesc with
      | Pnode nd -> (node nd)::acc
      | _ -> acc
    ) [] p.p_desc in
  (* The name of the file on which the depgraph is outputed
    was given in argument of the compiler *)
  let oc = open_out (List.hd !Compiler_options.depgraphGeneration) in
  let ff = Format.formatter_of_out_channel oc in
  List.iter (fun dgr -> print_depgraph_text ff dgr) ldepgraph;
  p

