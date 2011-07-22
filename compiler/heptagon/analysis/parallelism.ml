(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(* Checks for nested kernels and pmap and deduce whether a function is on GPU or CPU. *)
(* Changes maps in pmaps in kernels if the operator calls a normal function. *)

open Names
open Location
open Types
open Gpu
open Signature
open Modules
open Heptagon
open Hept_mapfold

(* Puts all the function definitions in a QualEnv to be able to analyze functions in any order. *)
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
    | Emix ->
        Format.eprintf "%aThere are mixed functions.@."
          print_location loc
  end;
  raise Errors.Error

(* Verifies the compatibility of two operations on the same level. *)
(* The right part of res is true if an incompatibility is encoutered. *)
let add_res res const = match (res, const) with
  | (_, true), _ -> res
  | (No_constraint, _), Kernel_caller -> (CPU, false)
  | (No_constraint, _), _ -> (const, false)
  | (GPU, _), No_constraint -> (GPU, false)
  | (GPU, _), GPU -> (GPU, false)
  | (GPU, _), _ -> (GPU, true)
  | (CPU, _), GPU -> (CPU, true)
  | (CPU, _), _ -> (CPU, false)
  | _ -> Misc.internal_error "parallelisation"

(* Verifies the compatibility of an operation with what is inside this operation. *)
let mount_res res const = match (res, const) with
  | (_, true), _ -> res
  | (No_constraint, _), Kernel_caller -> (CPU, false)
  | (No_constraint, _), _ -> (const, false)
  | (GPU, _), No_constraint -> (GPU, false)
  | (GPU, _), GPU -> (GPU, true)
  | (GPU, _), _ -> (GPU, true)
  | (CPU, _), GPU -> (CPU, true)
  | (CPU, _), _ -> (CPU, false)
  | _ -> Misc.internal_error "parallelisation"


(* Checks that pmaps are correct and changes maps in pmaps if necessary. *)
let edesc funs ((res, env, gpu) as acc) ed =
    match ed with
		  | Eiterator (Ipmap, _, _, _, _, _)
		  | Eiterator (Ipmapi, _, _, _, _, _) ->
          let (_, err) = add_res res GPU in
          let ed, (res, _, _) = Hept_mapfold.edesc funs ((No_constraint, err), env, gpu) ed in
		      ed, ((mount_res res GPU), env, gpu)
      (* Changes a map into a pmap when the function called is without constraint in a kernel. *)
		  | Eiterator (Imap, _, _, _, _, _)
		  | Eiterator (Imapi, _, _, _, _, _) when gpu = Kernel_caller ->
          let (_, err) = add_res res GPU in
          let ed, (res, _, _) = Hept_mapfold.edesc funs ((No_constraint, err), env, gpu) ed in
          (match ed, res with
            | Eiterator (Imap, a, sl, el1, el2, e), (No_constraint, _) ->
                Eiterator (Ipmap, a, sl, el1, el2, e), ((mount_res res GPU), env, gpu)
            | Eiterator (Imapi, a, sl, el1, el2, e), (No_constraint, _) ->
                Eiterator (Ipmapi, a, sl, el1, el2, e), ((mount_res res GPU), env, gpu)
            | _, _ ->
		            ed, (res, env, gpu))
      | _ ->
          Hept_mapfold.edesc funs acc ed

(* Raises an error if needed. *)
let eq funs acc eq =
  let eq, acc = Hept_mapfold.eq funs acc eq in
    match acc with
      | (CPU, true), _, _ -> message eq.eq_loc Egpu_in_cpu_function
      | (GPU, true), _, _ -> message eq.eq_loc Ecpu_in_gpu_function
      | (_, true), _, _ -> message eq.eq_loc Emix
      | _ -> eq, acc

(* Looks for the functions used. *)
let app funs acc a =
  let a, ((res, env, gpu) as acc) = Hept_mapfold.app funs acc a in
  match a.a_op with
    | Efun f | Enode f ->
        let ty_desc = find_value f in
        let const = ty_desc.node_gpu in
        (* If the function has not been analyzed, does it. *)
        if const = Undefined then
          let _ = node_dec funs acc (QualEnv.find f env) in
	        let ty_desc = find_value f in
	        let const = ty_desc.node_gpu in
          a, ((add_res res const), env, gpu)
        else
          a, ((add_res res const), env, gpu)
    | _ -> a, acc


(* Checks that no CPU only function is used in a Kernel_caller and update functions. *)
let node_dec funs ((_, env, _) as acc) n =
 Idents.enter_node n.n_name;
  let s = Modules.find_value n.n_name in
  if s.node_gpu != Undefined && s.node_gpu != Kernel_caller then
    { n with n_gpu = s.node_gpu }, acc
  else
	  let n, ((res, _, _) as acc) = Hept_mapfold.node_dec funs ((No_constraint, false), env, n.n_gpu) n in
	  match n.n_gpu with
	    | Undefined ->
	        let gpu = (match res with (c, _) -> c) in
	        Modules.replace_value n.n_name {s with node_gpu = gpu};
	        { n with n_gpu = gpu }, acc
	    | Kernel_caller ->
	        (match res with
	          | (CPU, _) -> message n.n_loc Ecpu_in_Kernel
	          | (_, _) -> n, acc)
      | _ -> Misc.internal_error "parallelisation"


let funs =
  { Hept_mapfold.defaults with
      edesc = edesc;
      eq = eq;
      app = app;
      node_dec = node_dec; }

let program p =
  let env = create_env QualEnv.empty p.p_desc in
  let p, _ = Hept_mapfold.program_it funs ((No_constraint, false), env, No_constraint) p in
  p
