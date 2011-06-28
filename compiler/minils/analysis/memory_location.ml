(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(* Checks for correctness of memory locations. *)

open Names
open Location
open Gpu
open Signature
open Idents
open Minils
open Mls_mapfold


let is_pervasives qn =
  (qn.qual = Pervasives)

type allowed_cast =
  | Restricted
  | Normal
  | Parallel
  | All

type error =
  | Eoperation_on_global_mem
  | Elocal_on_cpu
	| Ecreate_global_on_gpu
	| Ecreate_global_or_local_without_constraint
  | Eglobal_of_private
  | Eglobal_of_local
  | Elocal_of_private
  | Elocal_of_global
  | Enot_private

let message loc kind =
  begin match kind with
    | Eoperation_on_global_mem ->
        Format.eprintf "%aAn operation is done on a GPU memory in a CPU function.@."
          print_location loc
    | Elocal_on_cpu ->
        Format.eprintf "%aLocal memory cannot be allocated from the CPU.@."
          print_location loc
    | Ecreate_global_on_gpu ->
        Format.eprintf "%aGlobal memory cannot be allocated from the GPU.@."
          print_location loc
    | Ecreate_global_or_local_without_constraint ->
        Format.eprintf "%aNon private memories cannot be allocated from normal functions.@."
          print_location loc
    | Eglobal_of_private ->
        Format.eprintf "%aThis expression is private but is expected to be global.@."
          print_location loc
    | Elocal_of_private ->
        Format.eprintf "%aThis expression is private but is expected to be local.@."
          print_location loc
    | Elocal_of_global ->
        Format.eprintf "%aThis memory is global but is expected to be local.@."
          print_location loc
    | Enot_private ->
        Format.eprintf "%aThe called function should not expect a local or global memory.@."
          print_location loc
    | Eglobal_of_local ->
        Format.eprintf "%aThis expression is local but is expected to be global.@."
          print_location loc
  end;
  raise Errors.Error

let rec add_env gpu out_or_local env l = match l with
  | [] -> env
  | a :: l ->
      match gpu with
        | Kernel_caller
        | CPU ->
			      if a.v_mem = Local then
			        message a.v_loc Elocal_on_cpu
			      else
			        add_env gpu out_or_local (Env.add a.v_ident a env) l
        | GPU ->
			      if a.v_mem = Global & out_or_local then
			        message a.v_loc Ecreate_global_on_gpu
			      else
			        add_env gpu out_or_local (Env.add a.v_ident a env) l
        | No_constraint ->
            (match a.v_mem with
              | (Global | Local) when out_or_local -> 
			          message a.v_loc Ecreate_global_or_local_without_constraint
			        | _ -> add_env gpu out_or_local (Env.add a.v_ident a env) l)
        | _ -> Misc.internal_error "memory location"

let is_global env vi =
  let vd = Env.find vi env in
  (vd.v_mem = Global)

let rec mem_of_extval gpu env ext = 
  if gpu = Kernel_caller then
    Global
  else
    match ext.w_desc with
		  | Wconst _ -> Private
		  | Wvar v -> let vd = Env.find v env in vd.v_mem
		  | Wwhen (e, _, _)
		  | Wfield (e, _) -> mem_of_extval gpu env e

let check_cast gpu env cast loc ext_val in_mem =
  let arg_mem = mem_of_extval gpu env ext_val in
  match cast with
	  | Restricted ->
	      (match arg_mem, in_mem with
	        | _, Private -> ()
	        | Local, Local -> ()
          | Global, Global -> ()
	        | _ -> message loc Enot_private)
	  | Normal ->
	      (match arg_mem, in_mem with
	        | Private, Local -> message loc Elocal_of_private
	        | Private, Global -> message loc Eglobal_of_private
	        | Local, Global -> message loc Eglobal_of_local
	        | Global, Local -> message loc Elocal_of_global
	        | _ -> ())
	  | Parallel ->
	      (match arg_mem, in_mem with
	        | Local, Global -> message loc Eglobal_of_local
	        | Private, Global -> message loc Eglobal_of_private
	        | _ -> ())
	  | _ -> ()


let extvalue funs ((gpu, cannot, env) as acc) w =
	let w, _ = Mls_mapfold.extvalue funs acc w in
  if gpu = CPU then
	  match w.w_desc with
		  | Wvar vi ->
			    if cannot then
			      if is_global env vi then
			        message w.w_loc Eoperation_on_global_mem
			      else
			        w, acc
			    else
			      w, acc
		  | Wwhen (_, _, v) ->
		      if is_global env v then message w.w_loc Eoperation_on_global_mem;
		      w, acc
		  | _ ->
	        w, acc
  else
    w, acc

let exp funs ((gpu, _, env) as acc) eq =
  let rec cast_list cast wl il = match wl, il with
    | [], il -> il
    | w :: wl, { a_mem = im } :: il ->
        check_cast gpu env cast w.w_loc w im;
        cast_list cast wl il
    | _ -> Misc.internal_error "memory location"
  in
  if gpu = CPU then
    match eq.e_desc with
		  | Eapp(app, extl, _) ->
	        (match app.a_op with
	          | Eequal
	          | Efield_update
	          | Earray
	          | Earray_fill
	          | Eselect_dyn
	          | Econcat ->
			          let eq, _ = Mls_mapfold.exp funs (gpu, true, env) eq in
			          eq, acc
	          | Efun f | Enode f when is_pervasives f ->
			          let eq, _ = Mls_mapfold.exp funs (gpu, true, env) eq in
			          eq, acc
            | Eifthenelse ->
                (match extl with
                  | c :: extl ->
					            let _, _ = Misc.mapfold (extvalue_it funs) acc extl in
                      let _, _ = extvalue_it funs (gpu, true, env) c in
                      eq, acc
                  | _ -> Misc.internal_error "memory location")
            | Efun _
            | Enode _
	          | Eselect
	          | Eselect_trunc
	          | Eselect_slice
	          | Eupdate ->
			          let eq, _ = Mls_mapfold.exp funs acc eq in
			          eq, acc)
      | Ewhen (_, _, x)
		  | Emerge(x, _) ->
	        if is_global env x then
	          message eq.e_loc Eoperation_on_global_mem
	        else
	          let eq, _ = Mls_mapfold.exp funs acc eq in
	          eq, acc
		  | Eextvalue _
      | Efby _
		  | Estruct _
		  | Eiterator ((Ifold | Ifoldi), _, _, _, _, _) ->
				      let eq, _ = Mls_mapfold.exp funs acc eq in
				      eq, acc
		  | Eiterator _ ->
		      let eq, _ = Mls_mapfold.exp funs (gpu, true, env) eq in
		      eq, acc
  else if gpu = No_constraint then
	  match eq.e_desc with
      | Eapp ({ a_op = Efun f | Enode f}, wl, _) ->
	        let n = Modules.find_value f in
	        let il = n.node_inputs in
          let _ = cast_list Normal wl il in
          let eq, _ = Mls_mapfold.exp funs acc eq in
          eq, acc
          
      | Eiterator (it, { a_op = Efun f | Enode f }, _, sargs, args, _) ->
	        let n = Modules.find_value f in
	        let il = n.node_inputs in
          let _ = match it with 
					  | Imap
					  | Ipmap
					  | Imapi
					  | Ipmapi -> cast_list Restricted args (cast_list Normal sargs il)
					  | Ifold
					  | Imapfold ->
                let args, accf = Misc.split_last args in
                cast_list Normal [accf] 
                  (cast_list Restricted args 
                    (cast_list Normal sargs il))
					  | Ifoldi ->
                let il, i_acc = Misc.split_last il in
                let args, accf = Misc.split_last args in
                let _ = (cast_list Restricted args 
                          (cast_list Normal sargs il)) in
                cast_list Normal [accf] [i_acc]
          in
          let eq, _ = Mls_mapfold.exp funs acc eq in
          eq, acc
      | _ -> 
          let eq, _ = Mls_mapfold.exp funs acc eq in
          eq, acc
  else
	  match eq.e_desc with
      | Eapp ({ a_op = Efun f | Enode f}, wl, _) ->
	        let n = Modules.find_value f in
	        let il = n.node_inputs in
          let _ = cast_list Parallel wl il in
          let eq, _ = Mls_mapfold.exp funs acc eq in
          eq, acc
          
      | Eiterator (it, { a_op = Efun f | Enode f }, _, sargs, args, _) ->
	        let n = Modules.find_value f in
	        let il = n.node_inputs in
          let _ = match it with 
					  | Ipmap
					  | Ipmapi -> cast_list Restricted args (cast_list Parallel sargs il)
					  | Imap
					  | Imapi -> cast_list Parallel args (cast_list Parallel sargs il)
					  | Ifold
					  | Imapfold ->
                let args, accf = Misc.split_last args in
                cast_list Parallel [accf] 
                  (cast_list Parallel args 
                    (cast_list Parallel sargs il))
					  | Ifoldi ->
                let il, i_acc = Misc.split_last il in
                let args, accf = Misc.split_last args in
                let _ = (cast_list Parallel args 
                          (cast_list Parallel sargs il)) in
                cast_list Parallel [accf] [i_acc]
          in
          let eq, _ = Mls_mapfold.exp funs acc eq in
          eq, acc
      | _ -> 
          let eq, _ = Mls_mapfold.exp funs acc eq in
          eq, acc

(* Check that no CPU only function is used in a Kernel and update functions *)
let node_dec funs _ n =
  Idents.enter_node n.n_name;
  let env = add_env n.n_gpu false Env.empty n.n_input in
  let env = add_env n.n_gpu true env n.n_local in
  let env = add_env n.n_gpu true env n.n_output in
  match n.n_gpu with
    | CPU ->
	      let n, acc = Mls_mapfold.node_dec funs (n.n_gpu, false, env) n in
	      n, acc
    | _ ->
	      let n, acc = Mls_mapfold.node_dec funs (n.n_gpu, false, env) n in
	      n, acc

let funs =
  { Mls_mapfold.defaults with
      extvalue = extvalue;
      exp = exp;
      node_dec = node_dec; }

let program p =
  let p, _ = Mls_mapfold.program_it funs (No_constraint, false, Env.empty) p in
  p
