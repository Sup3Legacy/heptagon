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


(* Parallel schedule obtention and preprocess passes *)
(*  Only activated when !Compiler_options.parallel_schedule is true *)

(* Author: Guillaume I *)
open Containers

open Names
open Idents
open Minils
open Mls_utils
open Parsched

(* Also uses "Unicity_fun_instance.mFunname2Eq" *)

let debug = false
let ffout = Format.formatter_of_out_channel stdout

let print_sfunCons ff (sfunCons:StringSet.t) =
  Format.fprintf ff "sfunCons = { ";
  let lfunCons = StringSet.elements sfunCons in
  List.iter (fun elemstr -> Format.fprintf ff "%s, " elemstr) lfunCons;
  Format.fprintf ff "}\n@?"

let print_mfun2Table ff mfun2Table =
  Format.fprintf ff "mfun2Table =\n";
  StringMap.iter (fun k (blname, sd, ed) ->
    Format.fprintf ff "\t- %s -> (%s, %i, %i)\n" k blname sd ed
  ) mfun2Table;
  Format.fprintf ff "@?"


(* ==================================================== *)

(* Parsing function for the solution *)
let parse_file parse filename =
  let chan = open_in filename in
  let lexbuf = Lexing.from_channel chan in
  let res = 
    try parse lexbuf with
    | _ -> 
       close_in chan;
       let open Lexing in
       let pos = lexbuf.lex_curr_p in
       Printf.eprintf "Error in file \"%s\", line %d, character %d:\n"
          filename
          pos.pos_lnum
          (pos.pos_cnum-pos.pos_bol);
       failwith "Parsing error"
  in close_in chan; res

let parse_parsched filename = 
  parse_file (Parsched_parser.parsched Parsched_lexer.token) filename

(* Is it an OpenCL offload (kernel) or a normal function (value) *)
let qualify_value_or_kernel funname =
  try 
    let qk = Modules.qualify_kernel funname in
    (qk, true)
  with Not_found ->
    let qv = Modules.qualify_value funname in
    (qv, false)

(* Correspondance between a qualname of a function in the mls and the parsched funname *)
let qname_to_parsched_name qfunname =
  let nfnname = C.cname_of_qn qfunname in
  nfnname ^ "_step"


(* ==================================================== *)

(* Integrity check - Is the proposed schedule valid (in term of dependences) ? *)

(* Extract the funname of an equation. Return None if not an funcall equation *)
let extract_funcall_eq eq = match eq.eq_rhs.e_desc with
  | Eapp (ap, _, _) -> (match ap.a_op with
    | Enode fname | Efun fname -> Some fname
    | _ -> None
    )
  | _ -> None


(* Get the list of varid from the external value *)
let extract_varid_from_extval eval =
  match (Mls_utils.ident_of_extvalue eval) with
  | None -> []
  | Some vid -> vid::[]

(* Get the list of varid from the expression not behind a fby *)
let rec extract_immediate_varid_from_exp e = match e.e_desc with
  | Eextvalue eval -> extract_varid_from_extval eval
  | Efby _ -> []
  | Ewhen (e1, _, vid) -> vid::(extract_immediate_varid_from_exp e1)
  | Emerge (vid, lbranch) ->
    let llvid = List.map (fun (_, eval) -> extract_varid_from_extval eval) lbranch in
    vid::(List.concat llvid)
  | Estruct lstr ->
    let llvid = List.map (fun (_, eval) -> extract_varid_from_extval eval) lstr in
    List.concat llvid
  | Eiterator _ -> failwith "Eiterator not supported yet for parsched"
  | Eapp (_, leval, _) -> (* Note: ignore the potential reset variable *)
    (* Assume application is not a node or a function in our case *)
    let llvid = List.map (fun eval -> extract_varid_from_extval eval) leval in
    List.concat llvid

(* Get the list of function producing immediately (ie, not through fby) variables to lvarid *)
(* In short, dependency graph exploration to get the functions right below variables lvarid *)
let rec get_consumed_fun_from_var mVar2Eq svid_visited sres sresEq lvarid =
  (* Termination *)
  if (lvarid=[]) then (sres, sresEq) else

  let lEq = List.fold_left (fun leq_acc varid ->
    try
      let eq = Idents.Env.find varid mVar2Eq in
      eq::leq_acc
    with Not_found -> leq_acc (* Input - stop the search there *)
  ) [] lvarid in

  (* Remove redundancies in eq *)
  let sEq = List.fold_left (fun sacc eq -> EqSet.add eq sacc) EqSet.empty lEq in
  let lEq = EqSet.fold (fun eq lacc -> eq::lacc) sEq [] in

  (* Check equations *)
  let (nlvarid, nsres, nsresEq) = List.fold_left (fun (lvarid_acc, sres_acc, sresEq_acc) eq ->
    let ofuncall = extract_funcall_eq eq in
    match ofuncall with
    | None -> (* Not a function call *)
      let nlvarid = extract_immediate_varid_from_exp eq.eq_rhs in
      ((List.rev_append nlvarid lvarid_acc), sres_acc, sresEq_acc)
    | Some fname -> (* Function detected ! *)
        (lvarid_acc,
          StringSet.add fname.name sres_acc,
          EqSet.add eq sresEq_acc)
  ) ([], sres, sresEq) lEq in

  (* Redundancy management - remove the encountered vid & redundancies *)
  let (nlvarid, n_svid_visited) = List.fold_left (fun (lacc, svisited) vid ->
    if (IdentSet.mem vid svisited) then (lacc, svisited) else
    let nsacc = IdentSet.add vid svisited in
    (vid::lacc, nsacc)
  ) ([], svid_visited) nlvarid in

  get_consumed_fun_from_var mVar2Eq n_svid_visited nsres nsresEq nlvarid

(* mfun2Table: [fun_name --> (block_name, start_date, end_date) ] *)
(* Only take into account Res_funcall and Res_ocl_recover (to know where the value produced are) *)
let build_mfun2Table parsched =
  let mfun2Table = List.fold_left (fun macc (bl:block_sched) -> 
    let name_block = bl.bls_name in
    List.fold_left (fun macc (res:reservation) -> match res with
      | Res_funcall (res_name, res_st_date, res_end_date) ->
        StringMap.add res_name (name_block, res_st_date, res_end_date) macc
      | Res_ocl_recover (res_name, _, res_date) ->
        StringMap.add res_name (name_block, res_date, res_date) macc
      | _ -> macc
    ) macc bl.bls_lreser
  ) StringMap.empty parsched.lblock in
  mfun2Table

(* mvar2Eq : var_id -> eq *)
let build_mVar2Eq n =
  let mVar2Eq = List.fold_left (fun macc eq ->
    let lvar_lhs = Mls_utils.ident_list_of_pat eq.eq_lhs in
    List.fold_left (fun macc vid ->
      Idents.Env.add vid eq macc
    ) macc lvar_lhs
  ) Idents.Env.empty n.n_equs in
  mVar2Eq

(* We check if the parallel schedule corresponds to the node *)
let integrity_check mVar2Eq parsched n =
  (* Integrity checks:
    [Nodes/to be sure parsched is for the node "n"]
    -> All equations with a Eapp on the rhs have a corresponding node in the parallel schedule
    (note: Eiterators are not supported)
    -> All (and only) kernels are scheduled on a device block
    
    [Edges/dates du schedule]
    -> Pour chaque dependence immediate (cad pas fby), comparer les dates
      et s'assurer que "End_prod <= Begin_Cons"
      => Dependence retrouvee dans le graphe par exploration des equations (arbres) *)

  (* mfun2Table: [fun_name --> (block_name, start_date, end_date) ] *)
  let mfun2Table = build_mfun2Table parsched in

  (* Integrity checks *)
  List.iter (fun eq -> match eq.eq_rhs.e_desc with
    | Eapp (ap, lextval, _) -> begin match ap.a_op with
      | Efun fn | Enode fn -> begin
        (* Is that equation scheduled? *)
        let nqfnname = EqMap.find eq !Unicity_fun_instance.mEq2Funname in
        let nfnname = qname_to_parsched_name nqfnname in
        let (blname, beg_cons, _) = try
            StringMap.find nfnname mfun2Table
          with Not_found -> (
            Printf.eprintf "Parsched integrity check failed - Function \"%s\" (\"%s\") is not scheduled.\n"
              fn.name nfnname;
            failwith "Integrity check failed" )
        in

        (* Check the nature of fn and compare it to the nature of the block of the parsched *)
        if (Modules.check_kernel fn) then (
          (* OpenCL kernel *)
          if (not (is_device_block blname)) then (
            Format.fprintf ffout "Parsched integrity check failed - Function \"%s\" is scheduled on %s which is not a device block.\n" fn.name blname;
            failwith "Integrity check failed" )
        ) else (
          (* Not a kernel *)
          if (not (is_core_block blname)) then (
            Format.fprintf ffout "Parsched integrity check failed - Function \"%s\" is scheduled on %s which is not a core block.\n" fn.name blname;
            failwith "Integrity check failed" )
          (* DEBUG
          Format.fprintf ffout "Integrity - fn = %a\n@?" Global_printer.print_qualname fn;
          Format.fprintf ffout "Integrity - blname = %s\n@?" blname;
          *)
        );

        (* Dependency checks *)
        let lvaridUsed = List.concat (List.map extract_varid_from_extval lextval) in
        let (_, (seqCons : EqSet.t)) =
          get_consumed_fun_from_var mVar2Eq IdentSet.empty StringSet.empty EqSet.empty lvaridUsed in

        (* Get the end date of all producer functions *)
        EqSet.iter (fun (eqCons:Minils.eq) ->
          (* Recover the funname given to the scheduler *)
          let nqfname = try
              EqMap.find eqCons !Unicity_fun_instance.mEq2Funname
            with Not_found -> failwith "Parsched integrity check failed - Equation not found in mEq2Funname"
          in
          let nfname = qname_to_parsched_name nqfname in

          let (_,_, ed) = StringMap.find nfname mfun2Table in
          if (ed > beg_cons) then (
            Printf.eprintf "Parsched integrity check failed - Dependence from %s to %s is not respected.\n"
              nfname fn.name;
            failwith "Integrity check failed" )
        ) seqCons;

        (* DEBUG
        if (debug) then
          Format.fprintf ffout "Integrity - equation passed!\n@?" *)

      end
      | _ -> ()
    end
    | Eiterator _ -> failwith "Iterators are not supported for parallel schedule (yet?)"
    | _ -> ()
  ) n.n_equs;
  ()


(* ==================================================== *)

(* Naming convention for the synchronisation signal *)
let count_signal = ref 0
let get_signal_name res_name =
  let signame = res_name ^ (string_of_int !count_signal) in
  count_signal := !count_signal + 1;
  signame


(* Get the last end before a given date "d" (to insert something instantaneous after it *)
let get_last_end_before_date l_event_fun d =
  assert((List.length l_event_fun)>=2); (* At least something scheduled there (begin + end) *)
  let rec get_last_end_before_date_aux oprev_end d l_event_fun = match l_event_fun with
    | [] -> oprev_end
    | h::t ->
      let (dh, _, _, bstart_h) = h in
      (* If a start, ignore it *)
      if (bstart_h) then get_last_end_before_date_aux oprev_end d t else
      (* If we went later than d, then stop *)
      if (dh>d) then oprev_end else
      (* Recursion, while storing this new end before d *)
      get_last_end_before_date_aux (Some h) d t
  in
  get_last_end_before_date_aux None d (List.tl l_event_fun)

(* Get the first begin after a given date "d" (to insert something instantaneous before it) *)
let rec get_first_begin_after_date l_event_fun d = match l_event_fun with
  | [] -> None
  | h::t ->
    let (dh, _, _, bstart_h) = h in
    if (not (bstart_h)) then get_first_begin_after_date t d else (* Not a begin: ignore *)
    if (dh<d) then get_first_begin_after_date t d else   (* Before the date: continue *)
    Some h

(* Remove the Device blocks *)
let remove_device_blocks l_event_fun parsched =
  (* === Algorithm ===
    * For every block in a device block in parsched:
      => Add a ocl_launch (assumed instantaneous) on the Core block which is the last available
        before the start of the device block.
      => Add a ocl_recover (assumed instantaneous) on the Core block which is the first available
        after the end of the device block.
    * Then remove all device blocks. *)
  let parsched = List.fold_left (fun parsched_acc bls ->
    (* Not a device => we do not touch the non-device part of parsched *)
    if (not (is_device_block bls.bls_name)) then parsched_acc else

    (* For all offloading done on that block... *)
    List.fold_left (fun parsched_acc res_acc ->

      (* Get info on the offloading block *)
      let (res_name, res_st_date, res_end_date) = assert_funcall res_acc in

      (* a) Get the places where/when to but the ocl_launch and the ocl_recover *)
      (*    (Uses the global list of event) *)
      let olend = get_last_end_before_date l_event_fun res_st_date in     (* For ocl_launch  *)
      let ofbeg = get_first_begin_after_date l_event_fun res_end_date in  (* For ocl_recover *)

      let (proc_ocl_launch, date_ocl_launch) = match olend with
        | None -> (get_random_core_name parsched_acc, 0)
        | Some (date, block_name, _, bstart) ->
          assert(not bstart); (block_name, date)
      in
      let (proc_ocl_recover, date_ocl_recover) = match ofbeg with
        | None -> (get_random_core_name parsched_acc, res_end_date)
        | Some (date, block_name, _, bstart) ->
          assert(bstart); (block_name, date)
      in

      (* If they are on different process, then a signal is also needed
            to avoid that the "recover" happens before the "launch" *)
      let b_sig_needed = (proc_ocl_launch != proc_ocl_recover) in
      let signal_name = if b_sig_needed then
          get_signal_name res_name
        else
          "___DUMMY_SIGNAL_NAME"  (* Should never be used *)
      in


      (* b) We add the ocl_launch *)
      let parsched_acc = if (b_sig_needed) then
          let nres_signal_offload = mk_signal_res signal_name date_ocl_launch in
          add_new_reservation_before proc_ocl_launch nres_signal_offload parsched_acc
        else
          parsched_acc
      in
      let nres_ocl_launch = mk_ocl_launch_res res_name bls.bls_name date_ocl_launch in
      let parsched_acc = add_new_reservation_before proc_ocl_launch nres_ocl_launch parsched_acc in


      (* c) We add the ocl_recover *)
      let nres_ocl_recover = mk_ocl_recover_res res_name bls.bls_name date_ocl_recover in
      let parsched_acc = add_new_reservation_before proc_ocl_recover nres_ocl_recover parsched_acc in
      let parsched_acc = if (b_sig_needed) then
          let nres_wait_offload = mk_wait_res signal_name 1 date_ocl_recover in
          add_new_reservation_before proc_ocl_recover nres_wait_offload parsched_acc
        else
          parsched_acc
      in

      parsched_acc
    ) parsched_acc bls.bls_lreser
  ) parsched parsched.lblock in


  (* Remove all the device blocks from the parsched *)
  let lblock_proc = List.filter (fun bl -> not (is_device_block bl.bls_name)) parsched.lblock in
  let nparsched = mk_parsched parsched.nproc 0 lblock_proc in
  nparsched

(* ==================================================== *)

(* Reverse of "qname_to_parsched_name": from a pasched_name, get back the function name *)
let trim_name_gc_to_orig name_psch =
  let r = Str.regexp "[A-Za-z0-9_]+__\\([A-Za-z0-9_]+\\)_[0-9]+_step" in
  let name_orig = Str.replace_first r "\\1" name_psch in
  name_orig

let trim_name_gc_to_unique name_psch =
  let r = Str.regexp "[A-Za-z0-9_]+__\\([A-Za-z0-9_]+\\)_step" in
  let name_unique = Str.replace_first r "\\1" name_psch in
  name_unique


(* Find the equation associated to res *)
let get_equation_from_res res = match res with
  | Res_funcall (name, _, _) | Res_ocl_launch (name, _, _) -> (
    (* Remove the "_step" at the end of the name *)
    let name = trim_name_gc_to_unique name in
    try
      StringMap.find name !Unicity_fun_instance.mFunname2Eq
    with
      Not_found -> failwith "parsched_preproc::get_equation_from_res : Equation not found in mFunname2Eq"
    )
  | _ -> failwith "get_equation_from_res applied on a non-funcall/non-ocl-launch reservation"


(* Add the synchronisation reservation *)
let add_synch_reservation mVar2Eq parsched =
  (* Map to accelerate search of where a given fun or Ocl_launch is *)
  let mfun2Table = build_mfun2Table parsched in

  (* DEBUG
  Format.fprintf ffout "(addsynch - start) %a" print_mfun2Table mfun2Table; *)

  (* Algorithm:
    -> Detect equations where data consumed was produced on different thread
    -> For each of these equation, place the signal/wait at the right locations:
      => Signal at the end of the last producer of an other thread
      => If n signal was placed, we place a wait(n) before the execution of the equation
  *)
  let nparsched = List.fold_left (fun parsched_acc bls ->
    let current_block_name = bls.bls_name in

    let nparsched = List.fold_left (fun parsched_acc res ->
      (* We consider a computation that might need incoming synchronisation *)

      match res with
      | Res_funcall (res_name, res_date, _) | Res_ocl_launch (res_name, _, res_date) ->
        (* a) Get the list of reservations producting data used by "res" *)
        let eq_res = get_equation_from_res res in 
        let lvarid_used = extract_immediate_varid_from_exp eq_res.eq_rhs in
        let (_, sEq_used) =
          get_consumed_fun_from_var mVar2Eq IdentSet.empty StringSet.empty EqSet.empty lvarid_used
        in
        (* List of (res_fun_name, (name_block, res_st_date, res_end_date)) *)
        let lres_info_prod = EqSet.fold (fun eq_used lresname_acc ->
          let nqresname = try
              EqMap.find eq_used !Unicity_fun_instance.mEq2Funname
            with
              | Not_found -> failwith "add_synch_reservation: Unknown equation in mEq2Funname"
          in
          (* DEBUG
          Format.fprintf ffout "ping - nqresname = %a\n%a@?"
            Global_printer.print_qualname nqresname  print_mfun2Table mfun2Table; *)

          let psch_name = qname_to_parsched_name nqresname in
          let nres = try
              StringMap.find psch_name mfun2Table
            with Not_found ->
              failwith ("add_synch_reservation: Reservation name " ^ psch_name ^ " was not found in mfun2Table")
          in
          (psch_name, nres)::lresname_acc
        ) sEq_used [] in

        (* DEBUG
        let print_lres_info_prod ff lres_info_prod =
          Format.fprintf ff "lres_info_prod (%s) =\n" res_name;
          List.iter (fun (res_fun_name, (nblock, sd, ed)) ->
            Format.fprintf ff "\t- %s (%s, %i, %i)\n" res_fun_name nblock sd ed;
          ) lres_info_prod;
          Format.fprintf ff "@?"
        in
        print_lres_info_prod ffout lres_info_prod; *)


        (* b) Check the number of threads outside of current one
            where there is at least an element of lres_prod
            + maintain a list of the last executed element for
              each one of these threads *)
        let mLastRes = List.fold_left (fun macc (funname, (block_name, _, date)) ->
          if (StringMap.mem block_name macc) then (
            let (_, date_prev) = StringMap.find block_name macc in
            if (date_prev < date) then
              StringMap.add block_name (funname, date) macc
            else
              macc
          ) else
            StringMap.add block_name (funname, date) macc
        ) StringMap.empty lres_info_prod in

        (* Filter-out the current block *)
        let mLastRes = StringMap.remove current_block_name mLastRes in

        (* If mLastRes is empty, no need for synchronisation *)
        if (StringMap.is_empty mLastRes) then parsched_acc else

        (* c) Place wait & signal reservations *)
        let signame = get_signal_name res_name in
        let num_sync = StringMap.cardinal mLastRes in

        (* Wait reservation *)
        let wait_nres = Parsched.mk_wait_res signame num_sync res_date in
        let parsched_acc = add_new_reservation_before current_block_name wait_nres parsched_acc in

        (* Signal reservations *)
        let parsched_acc = StringMap.fold (fun bl_name (funname_res, date_res) psh_acc -> 
          let signal_nres = Parsched.mk_signal_res signame date_res in
          add_new_reservation_after_funname bl_name funname_res signal_nres psh_acc
        ) mLastRes parsched_acc in
        parsched_acc
      (* Nothing to do here *)
      | _ -> parsched_acc
    ) parsched_acc bls.bls_lreser in
    nparsched
  ) parsched parsched.lblock in
  nparsched


(* ==================================================== *)

(* Enrich a schedule to all the equations of n *)
let get_mls_parsched parsched =
  let (mls_parsched:Minils.parsched_eqs) = List.map (fun (pschbl:Parsched.block_sched) ->
    let lcomp = List.map (fun (res:Parsched.reservation) -> match res with
      | Res_funcall (funname, _, _) -> (
        let funname = trim_name_gc_to_unique funname in
        try
          let eq = StringMap.find funname !Unicity_fun_instance.mFunname2Eq in
          Comp_eq eq
        with
        | Not_found -> failwith ("Funname " ^ funname ^ " not found in mFunname2Eq")
      )
      | Res_ocl_launch (funname, deviceid, _) -> (
        let funname = trim_name_gc_to_unique funname in
        try
          let eq = StringMap.find funname !Unicity_fun_instance.mFunname2Eq in
          Comp_ocl_launch (eq, deviceid)
        with
        | Not_found -> failwith ("Funname " ^ funname ^ " not found in mFunname2Eq")
      )
      | Res_ocl_recover (funname, deviceid, _) -> (
        let funname = trim_name_gc_to_unique funname in
        try
          let eq = StringMap.find funname !Unicity_fun_instance.mFunname2Eq in
          Comp_ocl_recover (eq, deviceid)
        with
        | Not_found -> failwith ("Funname " ^ funname ^ " not found in mFunname2Eq")
      )
      | Res_signal (name, _) -> Comp_signal name
      | Res_wait (name, num, _) -> Comp_wait (name, num)
    ) pschbl.bls_lreser in
    lcomp
  ) parsched.lblock in
  mls_parsched



(* ==================================================== *)

(* Get the sorted event list (single list for all device/core) *)
let get_sorted_event_list parsched =
  let l_event_fun_unsorted = List.fold_left (fun lacc bls ->
    let bls_name = bls.bls_name in
    List.fold_left (fun lacc res ->
      let (fun_name, st_date, end_date) = assert_funcall res in
      let orig_fun_name = trim_name_gc_to_orig fun_name in

      (* DEBUG
      Format.fprintf ffout "ping - fun_name = %s |orig_fun_name = %s\n@?" fun_name orig_fun_name; *)

      (* We ignore device events *)
      let (_, b_is_kernel) = qualify_value_or_kernel orig_fun_name in

      (* TODO: qualify fun_name... which might or might not be a kernel... :/ *)
      if (b_is_kernel) then lacc else

      (st_date, bls_name, fun_name, true)::(end_date, bls_name, fun_name, false)::lacc
    ) lacc bls.bls_lreser
  ) [] parsched.lblock in
  let l_event_fun = List.sort (fun (d1, _, _, b1) (d2, _, _, b2) ->
    if (d1=d2) then (match (b1,b2) with
      | (true, false) -> 1  (* Second (end of task) should come before first (start of task) *)
      | (false,true) -> (-1)
      | _ -> 0
    ) else
    if (d1>d2) then 1 else (-1)
  ) l_event_fun_unsorted in
  l_event_fun



(* Preprocess the parallel scheduling to facilitate the parallel CG *)
(* Note: no need for the node, because we have Unicity_fun_instance.mFunname2Eq and mVar2Eq *)
let preprocess_parsched mVar2Eq (parsched:Parsched.parsched) =
  (* 1) No direct communication between 2 kernels *)
  (* We add a temporary variable for copy in the middle (as specific fun call? Or specific node?) *)
  (* We need to do it before scheduling => must be done in a separate pass *)
  (* Cf file "preprocess_lopht.ml" *)

  (* Preparation - get a sorted list of (date, block_name, fun_name, bstart) for scheduled funs on non-device
      where bstart = true when something is starting and bstart=false when something is finishing *)
  let l_event_fun = get_sorted_event_list parsched in
  (* Note: no need to update "l_event_fun" in the future, if parsched is updated *)
  (* This is just to know where and when are the functions. It should not be used for signal/other stuffs *)


  (* DEBUG *)
  if (debug) then
    Format.fprintf ffout " ~> l_event_fun built\n@?";

  (* 2) Remove Devices blocks (launch/recover reserv) *)
  let parsched = remove_device_blocks l_event_fun parsched in

  (* DEBUG *)
  if (debug) then
    Format.fprintf ffout " ~> Device block removed\n@?";

  (* DEBUG
  Format.fprintf ffout "parsched (after device block removal) = %a\n@?"
    Parsched.print_parsched parsched; *)

  (* 3) Add Synchronisations *)
  let parsched = add_synch_reservation mVar2Eq parsched in

  (* DEBUG *)
  if (debug) then
    Format.fprintf ffout " ~> Synchronisation added\n@?";

  (* DEBUG
  Format.fprintf ffout "parsched (after synchro) = %a\n@?" Parsched.print_parsched parsched; *)

  (* 4) Extend current schedule to a parsched_eqs schedule *)
  let (mls_parsched:Minils.parsched_eqs) = get_mls_parsched parsched in

  (* DEBUG
  Format.fprintf ffout "mls_parsched = %a\n@?" Mls_printast.print_parsched_eqs mls_parsched; *)

  mls_parsched


(* ==================================================== *)
let main_node n =
  (* We parse the parallel schedule file *)
  let parsched = parse_parsched (!Compiler_options.parsched_filename) in
  let parsched = Parsched.sort_reservation parsched in

  (* DEBUG *)
  if (debug) then
    Format.fprintf ffout "parsched = %a\n@?"
      Parsched.print_parsched parsched;


  (* Check the integrity of the parallel schedule *)
  let mVar2Eq = build_mVar2Eq n in
  integrity_check mVar2Eq parsched n;

  (* DEBUG *)
  if (debug) then
    Format.fprintf ffout "Integrity passed!\n@?";


  (* Preprocess the parallel schedule *)
  let mls_parsched = preprocess_parsched mVar2Eq parsched in

  (* DEBUG *)
  if (debug) then
    Format.fprintf ffout "Preprocess passed!\n@?";

  (* TODO for later: convert back non-functional equation (cf copy equation) to their previous version here *)
  (* Cf "preprocess_lopht" in "minils/gc/" *)

  (* We return the updated main node *)
  let mls_parsched_info = mk_parsched_info mls_parsched parsched.nproc parsched.ndevice in
  { n with n_parsched = Some mls_parsched_info }

let program p =
  let main_node_name = Misc.assert_1 !Compiler_options.mainnode in

  (* We trigger the transformation only on the main node *)
  let nlpdesc = List.map (fun pd -> match pd with
    | Pnode nd ->
      if (nd.n_name.name = main_node_name.name) then
        Pnode (main_node nd)
      else
        Pnode nd
    | _ -> pd
  ) p.p_desc in
  { p with p_desc = nlpdesc }

