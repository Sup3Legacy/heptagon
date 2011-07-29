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

let sig_of_app app = match app.a_op with
  | Efun f
  | Enode f ->  Modules.find_value f
  | _ -> assert false

let kerneltype_of_size size size_par =
  if size = [1] then
    Kernel size_par
  else
    Parallel_kernel (size, size_par)

let rec find_parallelism eq = match eq with
  | Eapp ({a_op = (Efun f | Enode f)}, _, _) ->
      let s = Modules.find_value f in
      (match s.node_gpu with
        | GPU n -> n
        | _ -> 0)
  | Ewhen ({e_desc = eq}, _, _) -> find_parallelism eq
  | Eiterator (_, app, _, _, _, _) ->
      let s = sig_of_app app in
      (match s.node_gpu with
        | GPU n -> n
        | _ -> 0)
  | _ -> 0

(* Split the equations to create the kernels, depending on the parallelisable equations *)
let eq _ acc eq =
  match eq.eq_rhs.e_desc, acc with
  | Eiterator ((Imap | Imapi), app, sel, _, _, _), (a, b, c)->
      let s = sig_of_app app in
      let i = match s.node_gpu with
        | GPU n -> n
        | _ -> assert false
      in
      (match b with
        | [], _ -> eq, (([eq], List.map int_of_static_exp sel, i) :: a, ([], 0), c)
        | bl, j -> eq, (([eq], List.map int_of_static_exp sel, i) ::
            ((List.rev bl), [1], j) :: a, ([], 0), c))
  | Eiterator ((Ipmap | Ipmapi), _, sel, _, _, _), (a, b, c) ->
      (match b with
        | [], _ -> eq, (([eq], List.map int_of_static_exp sel, 0) :: a, ([], 0), c)
        | bl, j -> eq, (([eq], List.map int_of_static_exp sel, 0) ::
            ((List.rev bl), [1], j) :: a, ([], 0), c))
  | edesc, (a, (bl, j), c) ->
      let i = find_parallelism edesc in
      eq, (a, (eq :: bl, max j i), c)

(* Create the nodes from the equations *)
let program_desc funs acc pd = match pd with
  | Pnode n when n.n_gpu = Kernel_caller ->
      let n, acc = Mls_mapfold.node_dec_it funs acc n in
      let args = n.n_local @ n.n_input @ n.n_output in

      let rec create_nodes nodes = match nodes with
        | [] -> [], [], [], 0
        | (eq_l, size, size_par) :: nodes ->
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

            let tyke = kerneltype_of_size size size_par in

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
            (Pnode node) :: nodes, eq :: eqs, (i, size, size_par) :: sizes, (i + 1)
      in

      (match acc with
        | (nodes, (last, _), c) when last = [] ->
            let (nodes, eqs, _, _) = create_nodes nodes in
            Pnode {n with n_equs = List.rev eqs},
            ([], ([], 0), nodes @ c)
        | (nodes, (last, j), c) ->
            let nodes = (List.rev last, [1], j) :: nodes in
            let (nodes, eqs, _, _) = create_nodes nodes in
            Pnode {n with n_equs = List.rev eqs;},
            ([], ([], 0), nodes @ c))
  | _ -> pd, acc

let funs =
  { Mls_mapfold.defaults with
      Mls_mapfold.program_desc = program_desc;
      Mls_mapfold.eq = eq; }

let program p =
  let p, acc = Mls_mapfold.program_it funs ([], ([], 0), []) p in
  match acc with
    | (_, _, c) -> {p with p_desc = c @ p.p_desc}