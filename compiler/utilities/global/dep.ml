(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)
(* dependences between equations *)

open Sgraph
open Idents

module type READ =
sig
  type equation
  val read: equation -> ident list
  val linear_read : equation -> ident list
  val def: ident list -> equation -> ident list
  val antidep: equation -> bool
end

module Make (Read:READ) =
struct
  let build eqs =
    (* associate a graph node for each name declaration *)
    let rec nametograph g var_list is_antidep n_to_graph =
      let add_node env x =
        if Env.mem x env then
          let l = Env.find x env in
          Env.add x ((g, is_antidep)::l) env
        else
          Env.add x [(g, is_antidep)] env
      in
      List.fold_left add_node n_to_graph var_list in

    let rec nametograph_env g var_list node_env =
      List.fold_left (fun env x -> Env.add x g env) node_env var_list in

    let rec init_graph eqs g_list n_to_graph lin_map node_env =
      match eqs with
        | [] -> g_list, n_to_graph, lin_map, node_env
        | eq :: eqs ->
            let g = make eq in
            let node_env = nametograph_env g (Read.def [] eq) node_env in
            let n_to_graph = nametograph g (Read.def [] eq)
              (Read.antidep eq) n_to_graph in
            let lin_map = nametograph g (Read.linear_read eq) true lin_map in
            init_graph eqs (g :: g_list) n_to_graph lin_map node_env
    in

    let rec make_graph g_list names_to_graph lin_map =
      let attach_one node (g, is_antidep) =
        if is_antidep then
          add_depends g node
        else
          add_depends node g
      in

      let attach env node n =
        try
          let l = Env.find n env in
          List.iter (attach_one node) l
        with
          | Not_found -> () in

      match g_list with
        | [] -> ()
        | node :: g_list ->
            let names = Read.read (containt node) in
            List.iter (attach names_to_graph node) names;
            let reads = Misc.list_diff names (Read.linear_read (containt node)) in
            List.iter (attach lin_map node) reads;
            make_graph g_list names_to_graph lin_map
    in

    let g_list, names_to_graph, lin_map, node_env =
      init_graph eqs [] Env.empty Env.empty Env.empty in
    make_graph g_list names_to_graph lin_map;
    g_list, node_env
end

