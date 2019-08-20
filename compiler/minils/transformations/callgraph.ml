(***********************************************************************)
(*                                                                     *)
(*                             Heptagon                                *)
(*                                                                     *)
(* Gwenael Delaval, LIG/INRIA, UJF                                     *)
(* Leonard Gerard, Parkas, ENS                                         *)
(* Adrien Guatto, Parkas, ENS                                          *)
(* Cedric Pasteur, Parkas, ENS                                         *)
(* Marc Pouzet, Parkas, ENS                                            *)
(*                                                                     *)
(* Copyright 2012 ENS, INRIA, UJF                                      *)
(*                                                                     *)
(* This file is part of the Heptagon compiler.                         *)
(*                                                                     *)
(* Heptagon is free software: you can redistribute it and/or modify it *)
(* under the terms of the GNU General Public License as published by   *)
(* the Free Software Foundation, either version 3 of the License, or   *)
(* (at your option) any later version.                                 *)
(*                                                                     *)
(* Heptagon is distributed in the hope that it will be useful,         *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of      *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the       *)
(* GNU General Public License for more details.                        *)
(*                                                                     *)
(* You should have received a copy of the GNU General Public License   *)
(* along with Heptagon.  If not, see <http://www.gnu.org/licenses/>    *)
(*                                                                     *)
(***********************************************************************)
open Names
open Types
open Misc
open Location
open Signature
open Modules
open Static
open Global_mapfold
open Mls_mapfold
open Minils
open Global_printer

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


let is_external ln =
  (* Kernel content is defined externaly by a .cl file *)
  if (Modules.check_kernel ln) then true else
  (Modules.find_value ln).node_external


module Param_instances :
sig
  type key1 = private static_exp (** Fully instantiated param *)
  type key2 = private ty         (** Fully instantiated type param *)
  type instance = (key1 list) * (key2 list)
  type env1 = key1 QualEnv.t
  type env2 = key2 QualEnv.t
  type env = env1 * env2
  val instantiate: env -> static_exp list -> ty list -> instance
  val get_node_instances : QualEnv.key -> instance list
  val add_node_instance : QualEnv.key -> instance -> unit
  val build_param : env -> param list -> key1 list -> env
  val build_typeparam : env -> type_name list -> key2 list -> env
  
  (* DEBUG *)
  val print_node_instances : Format.formatter -> unit
  val print_node_names : Format.formatter -> unit
  val print_instance : Format.formatter -> instance -> unit
  
  module Instantiate :
  sig
    val program : program -> program
  end
  
  (*module Instantiate_type_param :
  sig
    val program : program -> program
  end*)
end =
struct
  type key1 = static_exp
  type key2 = ty
  type env1 = key1 QualEnv.t
  type env2 = key2 QualEnv.t
  type env = env1 * env2

  (** An instance is a list of instantiated params and a list of instantiated type params *)
  type instance = (key1 list) * (key2 list)

  (** two instances are equal if the desc of keys are equal *)
  let compare_instances =
    let compare_se se1 se2 = compare se1.se_desc se2.se_desc in
    Misc.pair_compare
      (Misc.list_compare compare_se)
      (Misc.list_compare Global_compare.type_compare)

  (** Instances set *)
  module S =
    Set.Make(
      struct
        type t = instance
        let compare = compare_instances
      end)

  (** Map instance to its instantiated node *)
  module M =
    Map.Make(
      struct
        type t = qualname * instance
        let compare = Misc.pair_compare compare compare_instances
      end)

  (** Maps a couple (node name, params) to the name of the instantiated node *)
  let nodes_names = ref M.empty

  (** Maps a node to its list of instances *)
  let nodes_instances = ref QualEnv.empty
  
  (* BEGIN DEBUG *)
  let print_instance ff (inst : instance) =
    let (inst1, inst2) = inst in
    Format.fprintf ff "%a * %a"
      (Pp_tools.print_list Global_printer.print_static_exp "(" "," ")") inst1
      (Pp_tools.print_list Global_printer.print_type "(" "," ")") inst2
  
  let print_node_instances ff =
    let print_nodes_instances_aux ff node_inst =
      QualEnv.iter (fun key sinst -> Format.fprintf ff "	%a ---> %a\n@?"
        Global_printer.print_qualname key
        (Pp_tools.print_list print_instance "(" "," ")") (S.elements sinst)
      ) node_inst
    in
    Format.fprintf ff "nodes_instances =\n@?";
    print_nodes_instances_aux ff !nodes_instances

  let print_node_names ff =
    let print_node_names_aux ff nodes_names =
      M.iter (fun key qname -> Format.fprintf ff "	%a ---> %a\n@?"
        (Pp_tools.print_couple Global_printer.print_qualname print_instance "(" ") * (" ")") key
        Global_printer.print_qualname qname
      ) nodes_names
    in
    Format.fprintf ff "nodes_names =\n@?";
    print_node_names_aux ff !nodes_names
  (* END DEBUG *)
  
  
  
  (** create a params instance *)
  let instantiate (env1,env2) se_l ty_l =
    try
      let inst_se_l = List.map (eval env1) se_l in
      let inst_ty_l = List.map (eval_type env2) ty_l in
      (inst_se_l, inst_ty_l)
    with Errors.Error ->
      Error.message no_location (Error.Epartial_evaluation se_l)


  (** @return the name of the node corresponding to the instance of
      [ln] with the instance values [insts]. *)
  let node_for_params_call ln insts = match insts with
    | ([],[]) -> ln
    | _ ->
      (* DEBUG
      Format.fprintf (Format.formatter_of_out_channel stdout) "node_for_params_call => %a %a\n@?"
        Global_printer.print_qualname ln
        print_instance insts; *)
      if (is_external ln) then ln
      else (let ln = M.find (ln,insts) !nodes_names in ln)

  (** Generates a fresh name for the the instance of
      [ln] with the static parameters [params] and stores it. *)
  let generate_new_name ln insts = match insts with
    | ([],[]) -> nodes_names := M.add (ln, insts) ln !nodes_names
    | (params,types) ->
        let { qual = q; name = n } = ln in
        let param_string =
          List.fold_left
            (fun s se ->
              s ^ (Names.print_pp_to_name Global_printer.print_static_exp se))
            "_params_" params in
        let typeparam_string =
          List.fold_left
            (fun s ty ->
              s ^ (Names.print_pp_to_name Global_printer.print_type ty))
            "_types_" types in
        let new_ln =
          Modules.fresh_value_in "callgraph" (n^param_string^typeparam_string^"_") q in
        Idents.copy_node ln new_ln;
        nodes_names := M.add (ln, insts) new_ln !nodes_names

  (** Adds an instance of a node. *)
  let add_node_instance ln inst =
    (* get the already defined instances *)
    let instances = try QualEnv.find ln !nodes_instances
                    with Not_found -> S.empty in
    if S.mem inst instances then () (* if already there, nothing to do *)
    else ( (* it's a new instance *)
      let instances = S.add inst instances in
      nodes_instances := QualEnv.add ln instances !nodes_instances;
      generate_new_name ln inst )

  (** @return the list of instances of a node. *)
  let get_node_instances ln =
   let instances_set =
      try QualEnv.find ln !nodes_instances
      with Not_found -> S.empty in
   S.elements instances_set

  (** Build an environment by instantiating the passed params *)
  let build_param env params_names params_values =
    let (env1, env2) = env in
    let inst_param_val = List.map (eval env1) params_values in
    let env1 = List.fold_left2 (fun m { p_name = n } v -> QualEnv.add (local_qn n) v m)
      env1 params_names inst_param_val in
    (env1,env2)
  
  (** Build an environment by instantiating the passed type params *)
  let build_typeparam env typeparams_names ty_values =
    let (env1, env2) = env in
    let inst_typaram_val = List.map (eval_type env2) ty_values in
    let env2 = List.fold_left2 (fun m qn v -> QualEnv.add qn v m)
      env2 typeparams_names inst_typaram_val in
    (env1,env2)
  
  (** This module creates an instance of a node with a given
      list of static parameters. *)
  module Instantiate =
  struct
    (** Replaces static parameters with their value in the instance. *)
    let static_exp funs (env,tysubst) se =
      let se, _ = Global_mapfold.static_exp funs (env,tysubst) se in
      let se = match se.se_desc with
        | Svar q ->
            (match q.qual with
              | LocalModule -> (* This var is a static parameter, it has to be instanciated *)
                (try
                  let (env1, _) = env in
                  QualEnv.find q env1
                 with Not_found -> Misc.internal_error "callgraph - value of static parameter not found in environment")
              | _ -> se)
        | _ -> se in
      se, (env,tysubst)
    
    let ty funs (env,tysubst) t = match t with
      | Tid _ | Tinvalid -> t, (env,tysubst)
      | Tprod t_l -> let t_l, (env,tysubst) = mapfold (ty_it funs) (env,tysubst) t_l in (Tprod t_l), (env,tysubst)
      | Tarray (t, se) ->
          let t, (env,tysubst) = ty_it funs (env,tysubst) t in
          let se, (env,tysubst) = static_exp_it funs (env,tysubst) se in
          Tarray (t, se), (env,tysubst)
      | Tclasstype (tid, cl) ->
          let find_value_typaram env tid =
            (try
              let (_,env2) = env in
              QualEnv.find tid env2
             with Not_found ->
             Misc.internal_error ("callgraph - value of type parameter (" ^ tid.name ^ ") not found in environment")
           )
          in
          let typ = find_value_typaram env tid in
          let typ, (env,tysubst) = ty_it funs (env,tysubst) typ in
          typ, (env,tysubst)
    

    (** Replaces nodes call with the call to the correct instance. *)
    let edesc funs (env,tysubst) ed =
      let ed, _ = Mls_mapfold.edesc funs (env,tysubst) ed in
      let ed = match ed with
        | Eapp ({ a_op = Efun ln; a_params = params } as app, e_list, r) ->
          begin
            if (is_external ln) then ed else
            let ty_vals = List.map (fun (_,v) -> v) tysubst in (* tysubst was sorted *)
            let op = Efun (node_for_params_call ln (instantiate env params ty_vals)) in
            Eapp ({ app with a_op = op; a_params = []; }, e_list, r)
          end
        | Eapp ({ a_op = Enode ln; a_params = params } as app, e_list, r) ->
          begin
            if (is_external ln) then ed else
            let ty_vals = List.map (fun (_,v) -> v) tysubst in (* tysubst was sorted *)
            let op = Enode (node_for_params_call ln (instantiate env params ty_vals)) in
            Eapp ({ app with a_op = op; a_params = [] }, e_list, r)
          end
        | Eiterator(it, ({ a_op = Efun ln; a_params = params } as app),
                      n, pe_list, e_list, r) ->
          begin
            if (is_external ln) then ed else
            let ty_vals = List.map (fun (_,v) -> v) tysubst in (* tysubst was sorted *)
            let op = Efun (node_for_params_call ln (instantiate env params ty_vals)) in
            Eiterator(it, {app with a_op = op; a_params = [] },
                     n, pe_list, e_list, r)
          end
        | Eiterator(it, ({ a_op = Enode ln; a_params = params } as app),
                     n, pe_list, e_list, r) ->
          begin
            if (is_external ln) then ed else
            let ty_vals = List.map (fun (_,v) -> v) tysubst in (* tysubst was sorted *)
            let op = Enode (node_for_params_call ln (instantiate env params ty_vals)) in
            Eiterator(it,{app with a_op = op; a_params = [] },
                     n, pe_list, e_list, r)
          end
        | _ -> ed
      in
      ed, (env,tysubst)
    
    let app funs (env,tysubst) ap =
      let ap, _ = Mls_mapfold.app funs (env,ap.a_ty_subst) ap in
      ap, (env,tysubst)
    
    let node_dec_instance n (params,typarams) =
      Idents.enter_node n.n_name;
      let global_funs =
        { Global_mapfold.defaults with static_exp = static_exp;
                                       ty = ty } in
      let funs =
        { Mls_mapfold.defaults with edesc = edesc;
        							app = app;
                                    global_funs = global_funs } in
      
      let env = build_param (QualEnv.empty,QualEnv.empty) n.n_params params in
      let ntypeparam_name = List.map (fun typaram -> typaram.t_nametype) n.n_typeparams in
      let env = build_typeparam env ntypeparam_name typarams in
      
      let n, _ = Mls_mapfold.node_dec_it funs (env,[]) n in
      
      (* Add to the global environment the signature of the new instance *)
      (* Note that at that point the node cannot be external, or a kernel *)
      let node_sig = find_value n.n_name in
      let node_sig, _ = Global_mapfold.node_it global_funs (env,[]) node_sig in
      let node_sig = { node_sig with node_params = [];
                                     node_typeparams = [];
                                     node_param_constraints = [] } in
      (* Find the name that was associated to this instance *)
      let ln = node_for_params_call n.n_name (params, typarams) in
        if not (check_value ln) then
          Modules.add_value ln node_sig;
      { n with n_name = ln; n_params = []; n_param_constraints = []; n_typeparams = [];}

    let node_dec n =
      let l_insts = get_node_instances n.n_name in
      List.map (node_dec_instance n) l_insts

    let program p =
      let program_desc pd acc = match pd with
        | Pnode n ->
            let nds = node_dec n in
            List.fold_left (fun pds n -> Pnode n :: pds) acc nds
        | _ -> pd :: acc
      in
      { p with p_desc = List.fold_right program_desc p.p_desc [] }
  end
end

open Param_instances

type info =
  { mutable opened : program ModulEnv.t;
    mutable called_nodes : ((qualname * static_exp list * ty list) list) QualEnv.t; }

let info =
  { (* opened programs*)
    opened = ModulEnv.empty;
    (* Maps a node to the list of (node name, params) it calls *)
    called_nodes = QualEnv.empty }

(** Loads the modname.epo file. *)
let load_object_file modul =
  Modules.open_module modul;
  let modname = match modul with
      | Names.Pervasives -> "Pervasives"
      | Names.Module n -> n
      | Names.LocalModule -> Misc.internal_error "modules"
      | Names.QualModule _ -> Misc.unsupported "modules"
  in
  let name = String.uncapitalize_ascii modname in
    try
      let filename = Compiler_utils.findfile (name ^ ".epo") in
      let ic = open_in_bin filename in
        try
          let (p : program) = input_value ic in
            if p.p_format_version <> minils_format_version then (
              Format.eprintf "The file %s was compiled with \
                       an older version of the compiler.@\n\
                       Please recompile %s.ept first.@." filename name;
              raise Errors.Error
            );
            close_in ic;
            info.opened <- ModulEnv.add p.p_modname p info.opened
        with
          | End_of_file | Failure _ ->
              close_in ic;
              Format.eprintf "Corrupted object file %s.@\n\
                        Please recompile %s.ept first.@." filename name;
              raise Errors.Error
    with
      | Compiler_utils.Cannot_find_file(filename) ->
          Format.eprintf "Cannot find the object file '%s'.@."
            filename;
          raise Errors.Error

(** @return the node with name [ln], loading the corresponding
    object file if necessary. *)
let node_by_longname node =
  if not (ModulEnv.mem node.qual info.opened)
  then load_object_file node.qual;
  try
    let p = ModulEnv.find node.qual info.opened in
    let n = List.find (function Pnode n -> n.n_name = node | _ -> false) p.p_desc in
    (match n with
      | Pnode n -> n
      | _ -> Misc.internal_error "callgraph - node not found")
  with
    Not_found -> Error.message no_location (Error.Enode_unbound node)

(** @return the list of nodes called by the node named [ln], with the
    corresponding params (static parameters appear as free variables). *)
let collect_node_calls ln =
  (* only add nodes when not external and with params *)
  let add_called_node ln params typarams acc =
    match (params,typarams) with
      | [],[] -> acc
      | _ ->
        if (is_external ln) then acc else
          (ln, params,typarams)::acc
  in
  let edesc _ (acc,tysubst) ed = match ed with
    | Eapp ({ a_op = (Enode ln | Efun ln); a_params = params }, _, _) ->
        let ty_vals = List.map (fun (_,v) -> v) tysubst in (* tysubst was sorted *)
        ed, (add_called_node ln params ty_vals acc, tysubst)
    | Eiterator(_, { a_op = (Enode ln | Efun ln); a_params = params },
                _, _, _, _) ->
        let ty_vals = List.map (fun (_,v) -> v) tysubst in (* tysubst was sorted *)
        ed, (add_called_node ln params ty_vals acc, tysubst)
    | _ -> raise Errors.Fallback
  in
  let app funs (acc,_) ap =
    let ap, (acc,_) = Mls_mapfold.app funs (acc, ap.a_ty_subst) ap in
    ap, (acc,[])
  in
  
  let funs = { Mls_mapfold.defaults with edesc = edesc; app = app } in
  let n = node_by_longname ln in
  let _, (acc,_) = Mls_mapfold.node_dec funs ([],[]) n in
  acc

(** @return the list of nodes called by the node named [ln]. This list is
    computed lazily the first time it is needed. *)
let called_nodes ln =
  if not (QualEnv.mem ln info.called_nodes) then (
    let called = collect_node_calls ln in
    info.called_nodes <- QualEnv.add ln called info.called_nodes;
    called
  ) else
    QualEnv.find ln info.called_nodes

(** Generates the list of instances of nodes needed to call
    [ln] with static parameters [params]. *)
let rec call_node (ln, inst) =
  (* First, add the instance for this node *)
  let n = node_by_longname ln in
  
  let (params,typarams) = inst in
  let env = build_param (QualEnv.empty,QualEnv.empty) n.n_params params in
  let ntypeparam_name = List.map (fun typaram -> typaram.t_nametype) n.n_typeparams in
  let env = build_typeparam env ntypeparam_name typarams in
(*  List.iter check_no_static_var params; *)
  add_node_instance ln inst;

  (* Recursively generate instances for called nodes. *)
  let call_list = called_nodes ln in
  let call_list =
    List.map (fun (ln,p1,p2) -> ln, (instantiate env p1 p2) ) call_list in
  
  List.iter call_node call_list


let program p =
  (* Find the nodes without static parameters *)
  let main_nodes = List.filter (function Pnode n -> (is_empty n.n_params && is_empty n.n_typeparams)
                                        | _ -> false) p.p_desc in
  let main_nodes = List.map (function Pnode n -> n.n_name, ([],[])
                              | _ -> Misc.internal_error "callgraph") main_nodes in
  info.opened <- ModulEnv.add p.p_modname p ModulEnv.empty;
  
  (* Creates the list of instances starting from these nodes *)
  List.iter call_node main_nodes;
  
  (* DEBUG
  print_node_instances (Format.formatter_of_out_channel stdout);
  print_node_names (Format.formatter_of_out_channel stdout); *)
  
  let p_list = ModulEnv.fold (fun _ p l -> p::l) info.opened [] in
  
  (* Generate all the needed instances *)
  List.map Param_instances.Instantiate.program p_list

(* TODO: generation if there is typeparameters but no nparam => modularity? *)


