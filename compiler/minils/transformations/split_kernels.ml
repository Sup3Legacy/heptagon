(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(* Split the Kernel_callers into a Kernel_caller calling multiple kernels. *)

open Gpu
open Idents
open Names
open Types
open Signature
open Static
open Minils
open Mls_utils
open Graph
open Dep

module Var = Set.Make (struct type t = Idents.var_ident
                       let compare = Idents.ident_compare end)

let int_of_static_exp se = int_of_static_exp QualEnv.empty se

let extvalue_of_var_dec vd = mk_extvalue
    ~ty:vd.v_type ~clock:vd.v_clock
    ~loc:vd.v_loc (Wvar vd.v_ident)

let kerneltype_of_size size pmap =
  if size = [1] then
    Kernel
  else
    Parallel_kernel (size, pmap)

(* Split the equations to create the kernels, depending on the parallelisable equations *)
let eq _ acc eq =
  match eq.eq_rhs.e_desc, acc with
  | Eiterator ((Imap | Imapi), _, sel, _, _, _), (a, b, c)->
      (match b with
        | [] -> eq, (([eq], List.map int_of_static_exp sel, false) :: a, [], c)
        | _ -> eq, (([eq], List.map int_of_static_exp sel, false) ::
            ((List.rev b), [1], false) :: a, [], c))
  | Eiterator ((Ipmap | Ipmapi), _, sel, _, _, _), (a, b, c) ->
      (match b with
        | [] -> eq, (([eq], List.map int_of_static_exp sel, true) :: a, [], c)
        | _ -> eq, (([eq], List.map int_of_static_exp sel, true) ::
            ((List.rev b), [1], false) :: a, [], c))
  | _, (a, b, c) ->
      eq, (a, eq :: b, c)

(* Create the nodes from the equations *)
let program_desc funs acc pd = match pd with
  | Pnode n when n.n_gpu = Kernel_caller ->
      let n, acc = Mls_mapfold.node_dec_it funs acc n in
      let args = n.n_local @ n.n_input @ n.n_output in

      let rec create_nodes nodes = match nodes with
        | [] -> [], [], [], 0
        | (eq_l, size, pmap) :: nodes ->
            let (nodes, eqs, sizes, i) = create_nodes nodes in

            let size = List.rev size in

            (* Find the dependencies for the new kernel *)
            let rec add_def l = match l with
              | [] -> []
              | a :: l -> Vars.def (add_def l) a
            in
            let var_out = add_def eq_l in
            let rec add_def l set = match l with
              | a :: l -> add_def l (Var.add a set)
              | [] -> set
            in
            let var_out = add_def var_out Var.empty in
            let var_in = List.map (Vars.read false ) eq_l in
            let rec add_read l set = match l with
              | a :: l ->
                  let set =  if not (Var.mem a var_out) then Var.add a set else set in
                  add_read l set
              | [] -> set
            in

            (* The inputs and outputs of the new kernel *)
            let var_out = Var.fold
              (fun x acc -> {(vd_find x args) with v_mem = Global} ::acc) var_out [] in
            let var_in = List.fold_right add_read var_in Var.empty in
            let var_in = Var.fold
              (fun x acc -> {(vd_find x args) with v_mem = Global} ::acc) var_in [] in

            let tyke = kerneltype_of_size size pmap in

            (* Creates the kernel *)
            let qual_node = Modules.fresh_value "split_kernels"
              (n.n_name.name ^ "_kernel_" ^ (string_of_int i)) in
            let node =
                mk_node ~input:var_in ~output:var_out ~eq:eq_l
                ~stateful:n.n_stateful ~gpu:tyke ~param:n.n_params qual_node
            in

            (* Creates the corresponding call *)
            let tuple =
                Etuplepat (List.fold_right (fun x acc -> (Evarpat x.v_ident) :: acc) var_out []) in
            let node_exp =
              if (n.n_stateful) then
                mk_exp Clocks.Cbase (Tprod (List.map (fun x -> x.v_type) var_out))
                  (Eapp (mk_app (Enode qual_node), List.map extvalue_of_var_dec var_in, None))
               else
                mk_exp Clocks.Cbase (Tprod (List.map (fun x -> x.v_type) var_out))
				          (Eapp (mk_app (Efun qual_node), List.map extvalue_of_var_dec var_in, None))
            in
            let eq = mk_equation tuple node_exp in
            let sig_in = args_of_var_decs var_in in
            let sig_out = args_of_var_decs var_out in
				    Modules.add_value node.n_name
				      (Signature.mk_node ~gpu:tyke n.n_loc sig_in sig_out n.n_stateful n.n_params);

            (* Returns *)
            (Pnode node) :: nodes, eq :: eqs, (i, size, pmap) :: sizes, (i + 1)
      in

      (match acc with
        | (nodes, last, c) when last = [] ->
            let (nodes, eqs, _, _) = create_nodes nodes in
            Pnode {n with n_equs = List.rev eqs}, 
            ([], [], nodes @ c)
        | (nodes, last, c) ->
            let nodes = (List.rev last, [1], false) :: nodes in
            let (nodes, eqs, _, _) = create_nodes nodes in
            Pnode {n with n_equs = List.rev eqs;},
            ([], [], nodes @ c))
  | _ -> pd, acc

let funs =
  { Mls_mapfold.defaults with
      Mls_mapfold.program_desc = program_desc;
      Mls_mapfold.eq = eq; }

let program p =
  let p, acc = Mls_mapfold.program_it funs ([], [], []) p in
  match acc with
    | (_, _, c) -> {p with p_desc = c @ p.p_desc}