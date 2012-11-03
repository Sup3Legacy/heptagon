(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

open Names


(* naming and local environment *)


type ident = {
  hash : int;        (* to speed up things *)
  source : string;  (* the original name in the source *)
  unique_name : string;
  generated_by : string option;
  is_reset : bool;
}

let is_reset id = id.is_reset

type var_ident = ident

(* Warning this comparison is correct only between idents of a same node *)
let ident_compare id1 id2 =
  let c = compare id1.hash id2.hash in
  if c = 0 then compare id1.unique_name id2.unique_name else c

(*
(* used only for debugging *)
let debug_name id =
  if id.is_generated then
    id.source ^ "_" ^ (string_of_int id.num)
  else
    id.source

(* used only for debugging *)
let debug_print_ident ff id = Format.fprintf ff "%s" (debug_name id)*)


(* Type used to store for each node an hash-table storing the ident counters.*)
(* One counter exist per source name. It is used to define the unique name. *)
type nodes = (string,int) Hashtbl.t QualEnv.t
let (node_env : nodes ref) = ref QualEnv.empty

(* Stores the current node heap *)
let current_node_heap = ref []
(* Stores the current counters, initialized with a dummy *)
let dummy_counters = Hashtbl.create 0
let current_counters = ref dummy_counters



let load_nodes nds =
  node_env := QualEnv.append nds !node_env

let save_nodes modul =
  QualEnv.filter (fun m _ -> m.qual = modul) !node_env


(** This function should be called every time we enter a node *)
let push_node n =
  current_node_heap := n::!current_node_heap;
  current_counters :=
    try QualEnv.find n !node_env
    with Not_found ->
      let c = Hashtbl.create 100 in
      node_env := QualEnv.add n c !node_env;
      c

let pop_node () =
  let nh, cc, o = match !current_node_heap with
    | [] -> Misc.internal_error "pop node before pushing one."
    | o::[] -> [], dummy_counters, o
    | o::n::t -> n::t, QualEnv.find n !node_env, o
  in
  current_node_heap := nh;
  current_counters := cc;
  o



let clone_node f f' =
  (if (QualEnv.mem f' !node_env)
   then Misc.internal_error "Cloning node overwriting an existing one");
  node_env := QualEnv.add f' (Hashtbl.copy (QualEnv.find f !node_env)) !node_env


let rec fresh_string s =
  try
    let num = Hashtbl.find !current_counters s in
    let new_name = s ^ "_" ^ string_of_int num in
    Hashtbl.add !current_counters s (num + 1);
    if Hashtbl.mem !current_counters new_name
    then fresh_string s
    else (Hashtbl.add !current_counters new_name 1; new_name)
  with
    | Not_found -> (* it is already a fresh name *)
        Hashtbl.add !current_counters s 1;
        s
(*
    with Not_found -> 1 in
  Hashtbl.add !current_counters s (num + 1);
  let new_name = if num = 1 then s else s ^ "_" ^ string_of_int num in
  if Hashtbl.mem !current_counters new_name
  then fresh_string s
  else new_name
*)

let gen_var pass_name ?(reset=false) name =
  let unique_name = fresh_string name in
  { hash = Hashtbl.hash unique_name; source = name; generated_by = Some pass_name;
    is_reset = reset; unique_name = unique_name }

let ident_of_name ?(reset=false) name =
  let unique_name = fresh_string name in
  { hash = Hashtbl.hash unique_name; source = name; generated_by = None;
    is_reset = reset; unique_name = unique_name }

let source_name id = id.source
let name id = id.unique_name

let current_node () = List.hd (!current_node_heap)

let local_qn name = { Names.qual = Names.LocalModule (Names.QualModule (current_node ()));
                      Names.name = name }


let print_ident ff id =
  let s =
    if !Compiler_options.full_name then
    match id.generated_by with
      | None -> name id
      | Some p -> p ^ (name id)
    else name id
  in
  Format.fprintf ff "%s" s


module M = struct
  type t = ident
  let compare = ident_compare
  let print_t = print_ident
end

module Env =
struct
  include (Map.Make(M))

  let append env0 env =
    fold (fun key v env -> add key v env) env0 env

  (* Environments union *)
  let union env1 env2 =
    fold (fun name elt env -> add name elt env) env2 env1

  (* Environments difference : env1 - env2 *)
  let diff env1 env2 =
    fold (fun name _ env -> remove name env) env2 env1

  (* Environments partition *)
  let partition p env =
    fold
      (fun key elt (env1,env2) ->
         if p(key)
         then ((add key elt env1),env2)
         else (env1,(add key elt env2)))
      env
      (empty, empty)

  (* Print Env *)
  let print_t print_value ff m =
    Format.fprintf ff "@[<hov>{@ ";
    iter (fun k v -> Format.fprintf ff "%a => %a,@ " M.print_t k print_value v) m;
    Format.fprintf ff "}@]";
end

module IdentSet = struct
  include (Set.Make(M))

  let print_t ff s =
    Format.fprintf ff "@[<hov>{@ ";
    iter (fun e -> Format.fprintf ff "%a,@ " M.print_t e) s;
    Format.fprintf ff "}@]"

  let to_list s =
    fold (fun x acc -> x::acc) s []

end

module S = Set.Make (struct type t = string
                            let compare = Pervasives.compare end)


