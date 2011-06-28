(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(* Checks for nested kernels and pmap and deduce whether a function is on GPU or CPU. *)

open Names
open Location
open Types
open Gpu
open Signature
open Modules
open Heptagon
open Hept_mapfold

let rec create_env env l = match l with
  | [] -> env
  | a :: l -> 
      match a with
			  | Ptype _
			  | Pconst _ -> 
            env
			  | Pnode n -> 
            QualEnv.add n.n_name n (create_env env l)

let is_pervasives qn =
  (qn.qual = Pervasives)

type error =
  | Egpu_in_cpu_function
  | Ecpu_in_gpu_function
  | Ecpu_in_Kernel
  | Ekernel_in_Kernel
  | Emix

let message loc kind =
  begin match kind with
    | Egpu_in_cpu_function ->
        Format.eprintf "%aThe expression is GPU only but was preceded by CPU only functions.@."
          print_location loc
    | Ecpu_in_gpu_function ->
        Format.eprintf "%aThe expression is CPU only but was preceded by GPU only functions.@."
          print_location loc
    | Ecpu_in_Kernel ->
        Format.eprintf "%aA CPU only function is used in a Kernel.@."
          print_location loc
    | Ekernel_in_Kernel ->
        Format.eprintf "%aThere are nested Kernels.@."
          print_location loc
    | Emix ->
        Format.eprintf "%aThere are mixed functions.@."
          print_location loc
  end;
  raise Errors.Error

let add_acc acc const = match (acc, const) with
  | (_, true), _ -> acc
  | (No_constraint, _), Kernel_caller -> (CPU, false)
  | (No_constraint, _), _ -> (const, false)
  | (GPU, _), No_constraint -> (GPU, false)
  | (GPU, _), GPU -> (GPU, false)
  | (GPU, _), _ -> (GPU, true)
  | (CPU, _), GPU -> (CPU, true)
  | (CPU, _), _ -> (CPU, false)
  | _ -> Misc.internal_error "parallelisation"

let mount_acc acc const = match (acc, const) with
  | (_, true), _ -> acc
  | (No_constraint, _), Kernel_caller -> (CPU, false)
  | (No_constraint, _), _ -> (const, false)
  | (GPU, _), No_constraint -> (GPU, false)
  | (GPU, _), GPU -> (GPU, true)
  | (GPU, _), _ -> (GPU, true)
  | (CPU, _), GPU -> (CPU, true)
  | (CPU, _), _ -> (CPU, false)
  | _ -> Misc.internal_error "parallelisation"


(* Returns whether the exp is stateful.
   Replaces node calls with the correct Efun or Enode depending on the node signature. *)
let edesc funs (acc, env) ed =
    match ed with
		  | Eiterator (i, _, _, _, _, _) when i = Ipmap || i = Ipmapi ->
          let (_, err) = add_acc acc GPU in
          let ed, (acc, _) = Hept_mapfold.edesc funs ((No_constraint, err), env) ed in
		      ed, ((mount_acc acc GPU), env)
      | _ -> 
          let ed, (acc, _) = Hept_mapfold.edesc funs (acc, env) ed in
          ed, (acc, env)


(* Raise an error if needed *)
let eq funs acc eq =
  let eq, acc = Hept_mapfold.eq funs acc eq in
    match acc with
      | (CPU, true), _ -> message eq.eq_loc Egpu_in_cpu_function
      | (GPU, true), _ -> message eq.eq_loc Ecpu_in_gpu_function
      | (_, true), _ -> message eq.eq_loc Emix
      | _ -> eq, acc

(* Look for the functions used *)
let app funs (acc, env) a =
  let a, (acc, _) = Hept_mapfold.app funs (acc, env) a in
  match a.a_op with
    | Efun f | Enode f ->
        let ty_desc = find_value f in
        let const = ty_desc.node_gpu in
        if const = Undefined then
          let _ = node_dec funs ((No_constraint, false), env) (QualEnv.find f env) in
	        let ty_desc = find_value f in
	        let const = ty_desc.node_gpu in
          a, ((add_acc acc const), env)
        else
          a, ((add_acc acc const), env)
    | _ -> a, (acc, env)


(* Check that no CPU only function is used in a Kernel and update functions *)
let node_dec funs (_, env) n =
 Idents.enter_node n.n_name;
  let s = Modules.find_value n.n_name in
  if s.node_gpu != Undefined & s.node_gpu != Kernel then
    { n with n_gpu = s.node_gpu }, ((No_constraint, false), env)
  else
	  let n, (acc, _) = Hept_mapfold.node_dec funs ((No_constraint, false), env) n in
	  let const = n.n_gpu in
	  match const with 
	    | Undefined ->
	        let gpu = (match acc with (c, _) -> c) in
	        Modules.replace_value n.n_name {s with node_gpu = gpu};
	        { n with n_gpu = gpu }, ((No_constraint, false), env)
	    | Kernel_caller ->
	        (match acc with
	          | (CPU, _) -> message n.n_loc Ecpu_in_Kernel
	          | (Kernel, _) -> message n.n_loc Ekernel_in_Kernel
	          | (_, _) -> n, ((No_constraint, false), env))
      | _ -> Misc.internal_error "parallelisation"


let funs =
  { Hept_mapfold.defaults with
      edesc = edesc;
      eq = eq;
      app = app;
      node_dec = node_dec; }

let program p =
  let env = create_env QualEnv.empty p.p_desc in
  let p, _ = Hept_mapfold.program_it funs ((No_constraint, false), env) p in
  p
