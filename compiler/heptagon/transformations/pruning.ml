
(* Pruning transformation: remove all nodes which are not called by the main nodes *)
(* A main node is either:
     - If (Compiler_option.mainnode=[]) a node without static parameter
     - Else, one of the nodes specified inside this list *)
open Names
open Heptagon
open Signature

exception Node_Not_found

let rec find_qname_nameonly qname lmainnode = match lmainnode with
  | [] -> false
  | qn::r -> if (qname.name = qn.name) then true
    else find_qname_nameonly qname r


(* Removal of the useless nodes = only keep the useful nodes *)
let prune_program p useful_nodes =
  let rec aux_prune_program lpdesc useful_nodes = match lpdesc with
    | [] -> []
    | (Pnode n)::r -> 
       if (List.mem n.n_name useful_nodes) then (Pnode n)::(aux_prune_program r useful_nodes)
         else (aux_prune_program r useful_nodes)
    | h::r -> h::(aux_prune_program r useful_nodes)
  in
  let nlpdesc = aux_prune_program p.p_desc useful_nodes in
  { p with p_desc = nlpdesc }



(* ====================================================================== *)
(* Analysis to determine the useful nodes / Inspiration by "callgraph.ml" *)

(* Search a node of name "node_name" in a program *)
let rec find_node lpdesc node_name = match lpdesc with
  | [] -> raise Node_Not_found
  | Pnode n::r -> if (n.n_name=node_name) then n else (find_node r node_name)
  | _::r -> (find_node r node_name)

(* Gather the nodes called by a given node "node_name" in a program*)
let gather_called_nodes node_name p =
  (* Filter to avoid adding the external nodes *)
  let add_called_node name acc =
   if (Modules.find_value name).node_external
     then acc
     else name::acc
  in
  
  let app_called_node _ acc app = match app.a_op with
    | Enode (ln, _) -> app, (add_called_node ln acc) 
    | Efun (ln, _) -> app, (add_called_node ln acc)
    | _ -> app, acc
  in
  
  let node = find_node p.p_desc node_name in
  let funs = {Hept_mapfold.defaults with app = app_called_node } in
  let _, acc = Hept_mapfold.block funs [] node.n_block in
  acc

(* Get the set of nodes recursively called by a given node "node_name" *)
let rec call_node p visited_nodes node_name =
  (* Base case: the node was already visited*)
  if (List.mem node_name visited_nodes) then visited_nodes else
  
  let call_list = gather_called_nodes node_name p in
  
  (* Recursion *)
  let nvisited_nodes = List.fold_left (call_node p) (node_name::visited_nodes) call_list in
  nvisited_nodes


(* ====================================================================== *)
let program p =
  (* Get the main nodes / By default, the nodes without static parameters *)
  let main_nodes = if (!Compiler_options.mainnode=[]) then
    List.filter (function Pnode n -> ((n.n_params=[]) && (n.n_typeparamdecs=[]))
                                        | _ -> false) p.p_desc
  else
    List.filter (fun pdesc -> match pdesc with
      | Pnode n -> find_qname_nameonly n.n_name !Compiler_options.mainnode
      | _ -> false
    ) p.p_desc
  in
 
  let main_nodes = List.map (function Pnode n -> n.n_name
         | _ -> Misc.internal_error "pruning transformation - must be a Pnode here") main_nodes in
  
  (* Creates the list of instances starting from these nodes *)
  let useful_nodes = List.fold_left (call_node p) [] main_nodes in
  let p = prune_program p useful_nodes in
  p





