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

(* Preparation for the OpenCL code generation :
    - Log the kernel calls and associated input/output
    - Create 2 data structures (needed for CG, corresponding to the icl datastruct):
    mKernelCL : copt_id (identify the instance) ===>  (kernelsign, clo)
    mBufferCL : copt_id ====> ( (isInput, position) ===> id)
  *)

(* Author: Guillaume I *)
open Obc
open Obc_mapfold


module IntMap = Map.Make(struct type t=int let compare = Pervasives.compare end)
module BoolIntMap = Map.Make(struct type t=(bool * int) let compare = Pervasives.compare end)

(* Global datastructure to pass informations to all of the specific OpenCL CG parts *)
let mKernelCL = ref IntMap.empty
let mBufferCL = ref IntMap.empty
let mLocalBuffCL = ref IntMap.empty

(* mKernelCL : copt_id (identify the instance) ===>  (kernelname, kernelsign, clo) *)
(* mBufferCL : copt_id ====> (kernelname, kernelsign, (isInput, position) ===> (id, arg)) *)
(* mLocalBuffCL : copt_id ====> (kernelname, (posLocal ====> arg)) *)

(* Name of the global data structure used in the generated code - cf file "hept_opencl.h" *)
let icl_data_struct_string = "icl"


let idbuffer = ref 0    (* Will be equal at the end to the total number of buffer *)

let get_fresh_idbuffer () =
  let temp = !idbuffer in
  idbuffer := !idbuffer + 1;
  temp

(* ------------------------------------------ *)
(* Pretty-printer for the global data struct (for debugging) *)

let print_mKernelCL ff =
  IntMap.iter (fun k (kernelname, _, clo) ->
    Format.fprintf ff "[copt_id = %i | kernelname = %a | clo = %a]\n@?"
      k
      Global_printer.print_qualname kernelname
      (* Note: right now, we do not print the full signature *)
      Obc_printer.print_cloption clo
  ) !mKernelCL

let print_mBufferCL ff =
  IntMap.iter (fun k (kernelname, _, mArgs) ->
    Format.fprintf ff "[[ copt_id = %i | kernelname = %a |\n@?"
      k  Global_printer.print_qualname kernelname;
    BoolIntMap.iter (fun (isInput, pos) (idBuffer, arg) ->
      let strInOut = if isInput then "Input" else "Output" in
      Format.fprintf ff "\t%s #%i => IdBuffer = %i | ArgSig = %a\n@?"
        strInOut pos
        idBuffer  Global_printer.print_sarg arg
    ) mArgs;
    Format.fprintf ff "]]\n@?"
  ) ! mBufferCL

let print_mLocalBuffCL ff =
  IntMap.iter (fun k (kernelname, mArgs) ->
    Format.fprintf ff "[[ copt_id = %i | kernelname = %a |\n@?"
      k  Global_printer.print_qualname kernelname;
    IntMap.iter (fun pos arg ->
      Format.fprintf ff "\tLocal #%i => ArgSig = %a\n@?"
        pos  Global_printer.print_sarg arg
    ) mArgs;
    Format.fprintf ff "]]\n@?"
  ) !mLocalBuffCL



(* ------------------------------------------ *)

let rec find_object obj_id lobjdec = match lobjdec with
  | [] -> raise Not_found
  | h::t ->
    if (h.o_ident = obj_id) then h else (find_object obj_id t)


let get_kernel_sign classdef_objs objref = match objref with
  | Oarray _ ->
    failwith "openclprep internal error : kernel object is not supposed to be a Oarray"
  | Oobj obj_id ->
    try
      let odec = find_object obj_id classdef_objs in
      (odec.o_class, Modules.find_kernel odec.o_class)
    with Not_found ->
      failwith ("openclprep internal error : " ^ (Idents.name obj_id) ^ " not found in environment.")


(* Targetting *)
let act_opencl _ acc act = match act with
  | Acall (_, objref, mname, _) -> begin
    match mname with
    | Mkernel clo -> (
      if (clo.copt_is_launch=false) then act,acc else (* Only do it once per kernel *)

      let idkernelcall = clo.copt_id in
      let (qnameKernel, kernelsign) = get_kernel_sign acc objref in
      mKernelCL := IntMap.add idkernelcall (qnameKernel, kernelsign, clo) !mKernelCL;

      let mBufferCLPart = BoolIntMap.empty in
      let (mBufferCLPart, _) = List.fold_left (fun (macc, numInput) argin ->
        let idbuff = get_fresh_idbuffer () in
        let nmacc = BoolIntMap.add (true, numInput) (idbuff, argin) macc in
        (nmacc, numInput+1)
      ) (mBufferCLPart, 0) kernelsign.k_input in
      let (mBufferCLPart, _) = List.fold_left (fun (macc, numOutput) argout ->
        let idbuff = get_fresh_idbuffer () in
        let nmacc = BoolIntMap.add (false, numOutput) (idbuff,argout) macc in
        (nmacc, numOutput+1)
      ) (mBufferCLPart, 0) kernelsign.k_output in
      mBufferCL := IntMap.add idkernelcall (qnameKernel, kernelsign, mBufferCLPart) !mBufferCL;

      let (mLocalBuffCLPart, _) = List.fold_left (fun (macc, numLocal) argloc ->
        let nmacc = IntMap.add numLocal argloc macc in
        (nmacc, numLocal+1)        
      ) (IntMap.empty, 0) kernelsign.k_local in
      mLocalBuffCL := IntMap.add idkernelcall (qnameKernel, mLocalBuffCLPart) !mLocalBuffCL;

      act, acc
    )
    | _ -> act, acc
  end
  | _ -> act, acc


let class_def_opencl funs acc cd =
  Obc_mapfold.class_def funs cd.cd_objs cd


let program p =
  let funs_opencl = { Obc_mapfold.defaults with
    class_def = class_def_opencl;
    act = act_opencl
  } in
  let p, _ = Obc_mapfold.program funs_opencl [] p in

  (* DEBUG
  let ffout = Format.formatter_of_out_channel stdout in
  Format.fprintf ffout "mKernelCl =\n@?";
  print_mKernelCL ffout;
  Format.fprintf ffout "\nmBufferCL =\n@?";
  print_mBufferCL ffout;
  Format.fprintf ffout "\nmLocalBuffCL =\n@?";
  print_mLocalBuffCL ffout;
  *)

  p

