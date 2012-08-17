open Names
open Misc
open Location
open Signature
open Modules
open Static
open Global_mapfold
open Mls_mapfold
open Minils
open Global_printer

(** Generate all the needed instances,
    Instances of nodes from other modules are respectively done in their modules,
    thus the program list as output of [Callgraph.program] *)


module Error =
struct
  type error =
    | Enode_unbound of qualname
    | Epartial_evaluation of static_exp list

  let message loc kind =
    begin match kind with
      | Enode_unbound ln ->
          Format.eprintf "%aUnknown node '%s'@."
            print_location loc
            (fullname ln)
      | Epartial_evaluation se_l ->
          Format.eprintf "%aUnable to fully instanciate the static exps '%a'@."
            print_location loc
            print_static_exp_tuple se_l
    end;
    raise Errors.Error
end

module Param_instances :
sig
  type key = (*private*) static_exp (** Fully instantiated param *)
  type env = key QualEnv.t
  val instantiate_node : env -> QualEnv.key -> static_exp list -> QualEnv.key * key list
  val get_node_instances : QualEnv.key -> key list list
  val add_node_instance : QualEnv.key -> key list -> unit
  val build : param list -> key list -> env
  module Instantiate :
  sig
    val get_new_instances_of_node : node_dec -> program_desc list
    val get_new_instances_from_program : program -> program_desc list
    val update_node : node_dec -> node_dec
  end
end =
struct
  type key = static_exp
  type env = key QualEnv.t

  (** An instance is a list of instantiated params *)
  type instance = key list

  let compare_instance x y = list_compare static_exp_compare x y

  module S = (** Instances set *)
    Set.Make(
      struct
        type t = instance
        let compare = compare_instance
      end)

  module M = (** Map instance to its instantiated node *)
    Map.Make(
      struct
        type t = qualname * instance
        let compare (l1,i1) (l2,i2) =
          let cl = compare l1 l2 in
          if cl = 0 then compare_instance i1 i2 else cl
      end)

  (** Maps a couple (node name, params) to the name of the instantiated node *)
  let nodes_names = ref M.empty

  (** Maps a node to its list of instances *)
  let nodes_instances = ref QualEnv.empty

  (** Instantiate the static parameters to create an [instance]. *)
  let apply_subst_params m se_l =
    List.map (fun s -> simplify (apply_subst_se m s)) se_l

  (** Instantiate node, should correctly deal with partial application. *)
  let rec instantiate_node m n params = match n.qual with
    | LocalModule _->
        (match (QualEnv.find n m).se_desc with
          | Sfun (n,se_l) -> n, apply_subst_params m (se_l@params) (* concatenate the static args *)
          | _ -> Misc.internal_error "callgraph")
    | _ -> n, apply_subst_params m params

  (** @return the name of the node corresponding to the instance of
      [ln] with the static parameters [params]. *)
  and node_for_params_call m ln params =
    let ln, params = instantiate_node m ln params in
    try M.find (ln,params) !nodes_names, []
    with Not_found -> ln, params (* if not in nodes_names, it should not be instanciated,
    being probably parameterless or choosen to be kept with paramters. *)

  (** Generates a fresh name for the the instance of
      [ln] with the static parameters [params] and stores it. *)
  let generate_new_name ln params = match params with
    | [] -> nodes_names := M.add (ln, params) ln !nodes_names
    | _ ->
        let { qual = q; name = n } = ln in
        let param_string =
          List.fold_left
            (fun s se ->
              s ^ (Name_utils.print_pp_to_name print_static_exp se))
            "_params_" params in
        let new_ln =
          Modules.fresh_value_in "callgraph" (n^param_string^"_") q in
        nodes_names := M.add (ln, params) new_ln !nodes_names

  (** Adds an instance of a node. *)
  let add_node_instance ln params =
    (* get the already defined instances *)
    let instances = try QualEnv.find ln !nodes_instances
                    with Not_found -> S.empty in
    if S.mem params instances then () (* nothing to do *)
    else ( (* it's a new instance *)
      let instances = S.add params instances in
      nodes_instances := QualEnv.add ln instances !nodes_instances;
      generate_new_name ln params )

  (** @return the list of instances of a node. *)
  let get_node_instances ln =
   let instances_set =
      try QualEnv.find ln !nodes_instances
      with Not_found -> S.empty in
   S.elements instances_set


  (** Build an environment by instantiating the passed params *)
  let build params_names params_values =
    List.fold_left2
      (fun m { p_name = n } v -> QualEnv.add (Idents.local_qn n) v m)
      QualEnv.empty params_names (List.map eval params_values)


  (** This module creates an instance of a node with a given
      list of static parameters. *)
  module Instantiate =
  struct
    (** Replaces static parameters with their value in the instance. *)
    let static_exp funs m se =
      let se, _ = Global_mapfold.static_exp funs m se in
      let se = match se.se_desc with
        | Svar q ->
            (match q.qual with
              | LocalModule _ -> (* This var is a static parameter, try to instanciate it. *)
                (try
                  QualEnv.find q m
                 with Not_found ->
                   se) (* Allow partial application, especially with [update_node] *)
     (* Format.eprintf "rr %a@." (print_qualenv print_static_exp) m*)
              | _ -> se)
        | Sfun (q,se_l) ->
            (match q.qual with
              | LocalModule _ ->
                  (try
                    assert (se_l = []); (* TODO better error handling,
                                          it prevents q to be a partial application...
                                          could be accepted, but require to modify the typing *)
                    QualEnv.find q m
                    with Not_found -> Misc.internal_error "callgraph")
              | _ -> se)
        | _ -> se in
      se, m

    (** Replaces nodes call with the call to the correct instance. *)
    let edesc funs m ed =
      let ed, _ = edesc funs m ed in
      let ed =
        match ed with
          | Eapp ({ a_op = Efun ln; a_params = params } as app, e_list, r) ->
              let ln, params = node_for_params_call m ln params in
              Eapp ({ app with a_op = Efun ln; a_params = params }, e_list, r)
          | Eapp ({ a_op = Enode ln; a_params = params } as app, e_list, r) ->
              let ln, params = node_for_params_call m ln params in
              Eapp ({ app with a_op = Enode ln; a_params = params }, e_list, r)
          | Eiterator(it, ({ a_op = Efun ln; a_params = params } as app),
                        n, pe_list, e_list, r) ->
              let ln, params = node_for_params_call m ln params in
              Eiterator(it, {app with a_op = Efun ln; a_params = params },
                       n, pe_list, e_list, r)
          | Eiterator(it, ({ a_op = Enode ln; a_params = params } as app),
                       n, pe_list, e_list, r) ->
              let ln, params = node_for_params_call m ln params in
              Eiterator(it,{app with a_op = Enode ln; a_params = params },
                       n, pe_list, e_list, r)
          | _ -> ed
      in ed, m

    let global_funs = { Global_mapfold.defaults with static_exp = static_exp }

    let instanciate_node_body n m =
      Idents.push_node n.n_name;
      let funs = { defaults with edesc = edesc;
                                             global_funs = global_funs } in
      let n, _ = node_dec_it funs m n in
      let _ = Idents.pop_node () in
      n

    let clone_instance n params =
      Idents.push_node n.n_name;
      let m = build n.n_params params in
      let n = instanciate_node_body n m in

      (* Add to the global environment the signature of the new instance *)
      let node_sig = find_value n.n_name in
      let node_sig, _ = Global_mapfold.node_it global_funs m node_sig in
      let node_sig = { node_sig with node_params = [];
                                      node_param_constraints = [] } in
      (* Find the name that was associated to this instance *)
      let ln, params = node_for_params_call m n.n_name params in
      if params != [] then Misc.internal_error "params left";
      if not (check_value ln) then Modules.add_value ln node_sig;
      (* Clone the idents *)
      Idents.clone_node n.n_name ln;
      let _ = Idents.pop_node () in
      { n with n_name = ln; n_params = []; n_param_constraints = []; }

    let get_new_instances_of_node n =
      List.map (fun params -> Pnode (clone_instance n params)) (get_node_instances n.n_name)

    let get_new_instances_from_program p =
      let program_desc acc pd = match pd with
        | Pnode n -> (* for every node in the program p, search for instance *)
            (get_new_instances_of_node n)@acc
        | _ -> pd :: acc
      in
      List.fold_left program_desc [] p.p_desc

    let update_node n =
      instanciate_node_body n QualEnv.empty
  end

end

(* Global mutable environment used for memoiziations *)
type info =
  { mutable opened : program NamesEnv.t;
    mutable called_nodes : ((qualname * static_exp list) list) QualEnv.t;
    mutable need_instanciation : bool QualEnv.t; }

let info =
  { (** opened programs*)
    opened = NamesEnv.empty;
    (** Maps a node to the list of (node name, params) it calls *)
    called_nodes = QualEnv.empty;
    (** Tells whether a node needs to be instanciated *)
    need_instanciation = QualEnv.empty;
    }


(** Loads the modname.epo file. *)
let load_object_file file =
  Modules.open_module (Names.Module file);
  try
    let filename = Compiler_utils.findfile (file ^ ".epo") in
    let ic = open_in_bin filename in
      try
        let (p : program) = input_value ic in
          if p.p_format_version <> minils_format_version then (
            Format.eprintf "The file %s was compiled with \
                     an older version of the compiler.@\n\
                     Please recompile %s.ept first.@." filename file;
            raise Errors.Error
          );
          close_in ic;
          info.opened <- NamesEnv.add file p info.opened
      with
        | End_of_file | Failure _ ->
            close_in ic;
            Format.eprintf "Corrupted object file %s.@\n\
                      Please recompile %s.ept first.@." filename file;
            raise Errors.Error
  with
    | Compiler_utils.Cannot_find_file(filename) ->
        Format.eprintf "Cannot find the object file '%s'.@."
          filename;
        raise Errors.Error

(** @return the node with name [ln], loading the corresponding
    object file if necessary. *)
let node_by_longname node =
  match node.qual with
    | LocalModule _ -> raise Not_found
    | _ -> ();
  let prog_name = filename_from_modul node.qual in
  if not (NamesEnv.mem prog_name info.opened)
  then load_object_file prog_name;
  let p = NamesEnv.find prog_name info.opened in
  try
    let n =
      List.find (function Pnode n -> n.n_name = node | _ -> false) p.p_desc
    in
    (match n with
      | Pnode n -> n
      | _ -> Misc.internal_error "callgraph")
  with
    Not_found -> Error.message (no_location ()) (Error.Enode_unbound node)

let is_local ln = match ln.qual with
  | LocalModule _ -> true
  | _ -> false

(** Non memoized version of need_instanciation *)
let rec _need_instanciation ln =
  if is_local ln then true
  else
  (* external nodes can't be instanciated *)
  if (Modules.find_value ln).node_external
  then false
  else begin
    if !Compiler_options.enforce_callgraph
    then (* If I'm not parameterless, I need instanciation *)
      (Modules.find_value ln).node_params != []
    else (* Am I high-order, or is there a child requiring me to be instanciated ? *)
      let is_high_order (ln,_) = match ln with
        | { qual = LocalModule _ } -> true
        | _ -> false
      in
      (* This is recursive, a node needs to be instanciated
         when it calls a node needing instanciation with some of its local parameters. *)
      let child_require_instanciation (ln,params) =
        (need_instanciation ln)
        && (List.exists Signature.is_local_se params)
      in
      let childs = called_nodes ln in
      (*
Format.eprintf "%a has childs : @." print_qualname ln;
List.iter (fun (n,_) -> Format.eprintf "%a@." print_qualname n) childs;
  Format.eprintf "%a has child high_order ? %b@."
  print_qualname ln (List.exists is_high_order childs);
  Format.eprintf "%a has child needing inst ? %b@."
  print_qualname ln (List.exists child_require_instanciation childs);
  *)
      (List.exists is_high_order childs)
      or (List.exists child_require_instanciation childs)
  end

(** Is responsible to decide whether a node may be generated,
  or it needs to be instanciated with specific parameters. *)
and need_instanciation ln =
  try QualEnv.find ln info.need_instanciation
  with Not_found ->
    let b = _need_instanciation ln in
    info.need_instanciation <- QualEnv.add ln b info.need_instanciation;
    b


(** Non memoized version of called_nodes *)
and _called_nodes ln =
  let edesc _ acc ed = match ed with
    | Eapp ({ a_op = (Enode ln | Efun ln); a_params = params }, _, _)
    | Eiterator(_, {a_op = (Enode ln | Efun ln); a_params = params},_,_,_,_) ->
        let acc = if need_instanciation ln then (ln,params)::acc else acc in
        ed, acc
    | _ -> raise Errors.Fallback
  in
  let funs = { defaults with edesc = edesc } in
  let n = node_by_longname ln in
  let _, acc = node_dec funs [] n in
  acc

(** @return the list of nodes, called by the node named [ln],
    needing instanciation, with the
    corresponding params (static parameters appear as free variables). *)
and called_nodes ln =
  (* external nodes don't call others *)
  if (Modules.find_value ln).node_external then []
  else match ln.qual with
    | LocalModule _ -> [] (* high-order so we can't know *)
    | _ ->
        try QualEnv.find ln info.called_nodes
        with Not_found ->
          let called = _called_nodes ln in
          info.called_nodes <- QualEnv.add ln called info.called_nodes;
          called

(** Call add_node_instance, to generates the instances
    needed to call [ln] with static parameters [params]. *)
let rec call_node (ln, params) =
  (* First, add the instance for this node *)
  let n = node_by_longname ln in
  Idents.push_node n.n_name;
  let m = if params = [] (* there is no substitution for the root nodes *)
    then QualEnv.empty
    else Param_instances.build n.n_params params
  in
  (* Recursively generate needed instances. *)
  let childs = called_nodes ln in
  let childs =
    List.map (fun (ln, p) -> (Param_instances.instantiate_node m ln p)) childs
  in
  let childs = List.filter (fun (ln, _) -> need_instanciation ln) childs in
  List.iter (fun (n,p) -> Param_instances.add_node_instance n p) childs;
  List.iter call_node childs;
  let _ = Idents.pop_node () in ()

let program p =
  (* Open the current module *)
  info.opened <-
    NamesEnv.add (filename_from_modul p.p_modname) p NamesEnv.empty;
  (* Find the nodes which doesn't require instanciation *)
  let to_gen_nodes =
    List.fold_left
      (fun acc p -> match p with
        | Pnode n ->
          if not (need_instanciation n.n_name)
          then (n.n_name, [])::acc
          else acc
        | _ -> acc)
      [] p.p_desc
  in
  (* Creates the list of instances starting from these nodes *)
  List.iter call_node to_gen_nodes;
  (* The current program generate the to_gen_nodes plus some instances *)
  let pd = List.fold_right
    (fun pd acc -> match pd with
      | Pnode n when need_instanciation n.n_name ->
          (Param_instances.Instantiate.get_new_instances_of_node n)@acc
      | Pnode n ->
          (Pnode (Param_instances.Instantiate.update_node n))::acc
      | _ -> pd::acc)
    p.p_desc []
  in
  let p = { p with p_desc = pd } in
  (* Generate all the remaining needed instances,*)
  (* Every instance needed has invoked the opening of its module *)
  let p_list = NamesEnv.fold   (* First filter the modules from the one of p *)
    (fun _ o l -> if p.p_modname != o.p_modname then o::l else l)
    info.opened []
  in
  let new_nodes_in_other_modules =
    List.map (fun o -> {o with p_desc =
      Param_instances.Instantiate.get_new_instances_from_program o}) p_list
  in
  p::new_nodes_in_other_modules
