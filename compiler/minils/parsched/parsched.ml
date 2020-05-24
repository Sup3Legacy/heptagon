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

(* Structure for parallel scheduling (parsed from the output of Lopht) *)
(* Author: Guillaume I *)

open Format

(* Example of parallel schedule we might parse:
PROCESSORS:2 DEVICES:2

BLOCKS:3  CPU_0
0    1000  f_step
1000 3000  h_step
5000 7000  l_step
END_BLOCKS

BLOCKS:3  CPU_1
1000 2000  g_step
4000 6000  k_step
7000 8000  m_step
END_BLOCKS

BLOCKS:1  DEVICE_0
2000 4000  vector_add_1_step
END_BLOCKS

BLOCKS:1  DEVICE_1
3000 5000  vector_add_2_step
END_BLOCKS
*)

type reservation = 
  | Res_funcall of string * int * int         (* (name, start_date, end_date) / only block on parsing *)
  | Res_ocl_launch of string * string * int      (* (name, id_device, date) *)
  | Res_ocl_recover of string * string * int     (* (name, id_device, date) *)
  | Res_signal of string * int                (* (name, date) *)
  | Res_wait of string * int * int            (* (name, num_signal, date) *)

type block_sched = {
  bls_name : string;
  bls_lreser : reservation list;   (* Note: no assertion on the order of reservation *)
}

type parsched = {
  nproc : int;
  ndevice : int;
  lblock: block_sched list;
}

(* ------------------------- *)

(* Constructors *)
let mk_funcall_res name s e = Res_funcall (name, s, e)
let mk_ocl_launch_res name id_device d = Res_ocl_launch (name, id_device, d)
let mk_ocl_recover_res name id_device d = Res_ocl_recover (name, id_device, d)
let mk_signal_res name_sync d = Res_signal (name_sync, d)
let mk_wait_res name_sync num d = Res_wait (name_sync, num, d)


let mk_block_sched name lresa =
  { bls_name = name; bls_lreser = lresa }

let mk_parsched nproc ndevice lblock =
  { nproc = nproc; ndevice = ndevice; lblock = lblock }


(* Pretty-printer *)
let print_reservation ff res = match res with
  | Res_funcall (n, s, e) -> fprintf ff "%i\t%i\t%s\n" s e n
  | Res_ocl_launch (n, iddev, d) -> fprintf ff "%i\t%i\tOCL_LAUNCH(%s) %s\n" d d iddev n
  | Res_ocl_recover (n, iddev, d) -> fprintf ff "%i\t%i\tOCL_RECOVER(%s) %s\n" d d iddev n
  | Res_signal (n, d) -> fprintf ff "%i\t%i\tSignal %s\n" d d n
  | Res_wait (n, ns, d) -> fprintf ff "%i\t%i\tWait(%i) %s\n" d d ns n

let print_block_sched ff bsch =
  fprintf ff "BLOCKS:%i  %s\n"
    (List.length bsch.bls_lreser)  bsch.bls_name;
  List.iter (fun res ->
    print_reservation ff res
  ) bsch.bls_lreser;
  fprintf ff "END_BLOCKS\n@?"

let print_parsched ff psched =
  fprintf ff "PROCESSORS:%i DEVICES:%i\n\n@?"
      psched.nproc psched.ndevice;
  List.iter (fun bsch ->
    print_block_sched ff bsch
  ) psched.lblock

(* ------------------------- *)

(* Nature of a block *)
let device_prefix = "DEVICE_"
let core_prefix = "CPU_"

let is_device_block block_name =
  if ( (String.length block_name) <= (String.length device_prefix)) then false else
  let prefix = String.sub block_name 0 (String.length device_prefix) in
  (prefix = device_prefix)

let is_core_block block_name =
  if ( (String.length block_name) <= (String.length core_prefix)) then false else
  let prefix = String.sub block_name 0 (String.length core_prefix) in
  (prefix = core_prefix)

(* Assert that a reservation is a funcall and extract infos *)
let assert_funcall res = match res with
  | Res_funcall (name, s, e) -> (name, s, e)
  | _ -> failwith "assert_funcall failed: reservation is not a funcall."

(* Get a random core block name (first one we get) *)
(* Used on situation where ANY core is fine to be used *)
let get_random_core_name parsched =
  let rec get_random_core_name_aux lbl = match lbl with
    | [] -> failwith "get_random_core_name : there is no core block in the parallel schedule."
    | h::t -> if (is_core_block h.bls_name) then h.bls_name else
      get_random_core_name_aux t
  in
  get_random_core_name_aux parsched.lblock

(* Get the start date of a reservation *)
let get_start_date res = match res with
  | Res_funcall (_, d, _) -> d
  | Res_ocl_launch (_, _, d) -> d
  | Res_ocl_recover (_, _, d) -> d
  | Res_signal (_, d) -> d
  | Res_wait (_, _, d) -> d


(* ------------------------- *)


(* Sort the reservation dates of each blocks in a parshed *)
let sort_reservation parshed =
  (* Comparaison function / 0=>Equal / +=>r1>r2 / -=>r1<r2 *)
  let fun_sort_resa r1 r2 =
    let d1 = get_start_date r1 in
    let d2 = get_start_date r2 in
    (d1-d2)
  in

  let lblock_sorted = List.map (fun bl ->
    let lresa = bl.bls_lreser in

    let lresa_sorted = List.sort fun_sort_resa lresa in
    { bl with bls_lreser = lresa_sorted }
  ) parshed.lblock in
  { parshed with lblock = lblock_sorted }


(* Add a new reservation in one of the list of sorted reservations of parshed *)
let add_new_reservation_aux fun_selection block_name nres parsched =
  let date = get_start_date nres in
  let nlbl = List.map (fun bl ->
    if (bl.bls_name=block_name) then (
      let (badded, nlres_rev) = List.fold_left (fun (badded, lres_acc) res ->
        (* If the reservation was already added *)
        if (badded) then (badded, res::lres_acc) else

        let d = get_start_date res in
        if (fun_selection lres_acc d date) then  (* Insertion condition (note: acc list is currently inverted) *)
          (true, res::nres::lres_acc)
        else
          (false, res::lres_acc)
      ) (false, []) bl.bls_lreser in

      (* If date is after all the other reservation ===> add it at the very end *)
      let nlres_rev = if (not badded) then nres::nlres_rev else nlres_rev in

      { bl with bls_lreser = List.rev nlres_rev }
    ) else
      bl
  ) parsched.lblock in
  { parsched with lblock = nlbl }

(* XXX_before ===> If several res has the same start date in the block, place it before all the other *)
let add_new_reservation_before block_name nres parsched =
  (* Add the new reservation just before the first reservation at "date" or above encountered  *)
  let fun_sel = (fun _ d date -> d>=date) in
  add_new_reservation_aux fun_sel block_name nres parsched

(* XXX_after ===> If several res has the same start date in the block, place it after all the other *)
let add_new_reservation_after block_name nres parsched =
  (* Add the new reservation just before the first reservation strictly above "date" encountered  *)
  let fun_sel = (fun _ d date -> d>date) in
  add_new_reservation_aux fun_sel block_name nres parsched

(* Add a reservation right after a given "funname" at the same date than its reservation *)
let add_new_reservation_after_funname block_name funname nres parsched =
  let fun_sel = (fun lprev_res d date -> match lprev_res with
    | [] -> false
    | prev_res::_ -> (match prev_res with
      | Res_funcall (prev_res_name, _, _) | Res_ocl_recover (prev_res_name, _, _)->
        if (prev_res_name=funname) then
          (assert(d>=date); true)
        else
          (assert(d<=date); false)
      | _ -> false
    )
  ) in
  add_new_reservation_aux fun_sel block_name nres parsched

