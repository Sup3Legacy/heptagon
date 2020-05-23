
(* Author: Guillaume I *)

open Names
open Idents

(* Naming convention for mls2obc *)

(* Signal/wait naming conventions for parallel schedule code generation *)
let signal_fun_call_qname = { qual = Pervasives; name = "decrease_count_condvar" }
let wait_fun_call_qname = { qual = Pervasives; name = "wait_count_condvar" }

let ty_pthread_condvar = Types.Tid { qual = Pervasives; name = "pthread_cond_t"}
let ty_pthread_mutvar = Types.Tid { qual = Pervasives; name = "pthread_mutex_t"}

let cond_var_signal_name signame = "cond_" ^ signame
let mut_var_signal_name signame = "mut_" ^ signame
let count_var_signal_name signame = "count_" ^ signame
(* let count_max_var_signal_name signame = "count_max_" ^ signame *)

let get_ident_of_signal signame =
  let condvarid = Idents.gen_var "mls2obc" (cond_var_signal_name signame) in
  let mutvarid = Idents.gen_var "mls2obc" (mut_var_signal_name signame) in
  let countvarid = Idents.gen_var "mls2obc" (count_var_signal_name signame) in
  (* let countmaxvarid = Idents.gen_var "mls2obc" (count_max_var_signal_name signame) in *)
  (condvarid, mutvarid, countvarid)



(* Naming convention for the methods of the scattered main node, for parallel CG *)
let name_init_mutex_func = "init_mutex"
let name_init_sync_counter_func = "init_sync_counter"

let name_var_memory_main = "mem"

let qname_pthread_cond_init = { qual = Pervasives; name = "pthread_cond_init" }
let qname_pthread_mut_init = { qual = Pervasives; name = "pthread_mutex_init" }
let name_pthread_create = "pthread_create"
let name_pthread_join = "pthread_join"

let get_name_thread n = "work_thread_" ^ (string_of_int n)


(* References to keep track of num_thread / num_device *)
(* Updated on mls2obc when passing to obc (because info about number of threads
		is scattered during the translation, and is needed by "cmain") *)
let rnum_thread = ref 0
