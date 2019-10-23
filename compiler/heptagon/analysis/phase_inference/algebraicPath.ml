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


(* Algebraic Path problem computation *)
(* Author: Guillaume I *)

(* Equation of the APP:
  (note: * = closure operator / + = plus operator / * = mult operator)

  A[i,j,k] =
    { i=k  && j=k  : (A[i,j,k-1])*
    { i=k  && j!=k : A[i,k,k] * A[k,j,k-1]
    { i!=k && j=k  : A[i,k,k-1] * A[k,j,k]
    { i!=k && j!=k : A[i,j,k-1] + (A[i,k,k] * A[k,j,k-1])
  
  with init being: A[i,j,-1] = mat_coeff[i,j]
  and result being res_coeff[i,j] = A[i,j,n-1]

  * Schedule to do that in-place on mat_coeff:
  For k=0 -> N-1:
    Compute A[k,k,k]

    For i=0 -> N-1, i!=k:
      Compute A[i,k,k]
    
    For j=0 -> N-1, j!=k
      For i=0 -> N-1, i!=k:
        Compute A[i,j,k] (using the old value A[k,j,k-1])
      Compute A[k,j,k]
 *)

let ffout = Format.formatter_of_out_channel stdout
let debug = false (* DEBUG *)
let slow_compilation = debug && true (* DEBUG - for getting the time step *)
let step_slow_compilation = 50

let print_square_mat ff mat_coeff =
  let n = Array.length mat_coeff in
  Format.fprintf ff "[[\n@?";
  for i = 0 to n-1 do
    let tempRow = mat_coeff.(i) in
    Format.fprintf ff "\t[";
    for j = 0 to n-1 do
      let elem = tempRow.(j) in
      match elem with
      | None -> Format.fprintf ff " -inf"
      | Some e -> Format.fprintf ff " %i" e;
    done;
    Format.fprintf ff " ]\n@?";
  done;
  Format.fprintf ff "]]\n@?"

let print_int_opt ff iopt = match iopt with
  | None -> Format.fprintf ff "-inf"
  | Some i -> Format.fprintf ff "%i" i




(* Apply the algebraic path problem to a matrix of coefficient mat_coeff *)
(* This is an inplace computation *)
let algebraic_path_problem_old (op_closure: int option -> int option)
  (op_plus: int option -> int option -> int option)
  (op_mul: int option -> int option -> int option) (mat_coeff : int option array array) =
  let n = Array.length mat_coeff in

  (* DEBUG *)
  if (debug) then
    Format.fprintf ffout "Start of APP - mat_coeff = %a\n@?"
      print_square_mat mat_coeff;

  (* Main loop *)
  for k = 0 to n-1 do
    if (slow_compilation && (k mod step_slow_compilation=0)) then
       Format.fprintf ffout "APP - STEP %i\n@?" k;


    (* A[k,k,k] = (A[k,k,k-1])* *)
    let tempkk = op_closure mat_coeff.(k).(k) in
    mat_coeff.(k).(k) <- tempkk;

    (* For i!=k *)
    for i = 0 to n-1 do
      if (i!=k) then
        (* A[i,k,k] = A[i,k,k-1] * A[k,k,k] *)
        mat_coeff.(i).(k) <- op_mul mat_coeff.(i).(k) tempkk;
    done;

    (* For j!=k *)
    for j = 0 to n-1 do
      if (j!=k) then

        (* For i!=k *)
        for i = 0 to n-1 do
          if (i!=k) then
            (* DEBUG
            Format.fprintf ffout "i = %i | j = %i\n@?" i j;
            Format.fprintf ffout "\tmat_coeff.(i).(j) = %a\n@?" print_int_opt mat_coeff.(i).(j);
            Format.fprintf ffout "\tmat_coeff.(i).(k) = %a\n@?" print_int_opt mat_coeff.(i).(k);
            Format.fprintf ffout "\tmat_coeff.(k).(j) = %a\n@?" print_int_opt mat_coeff.(k).(j);
            Format.fprintf ffout "\tmult = %a\n@?"
              print_int_opt (op_mul mat_coeff.(i).(k) mat_coeff.(k).(j)); *)

            (* A[i,j,k] = A[i,j,k-1] + (A[i,k,k] * A[k,j,k-1]) *)
            mat_coeff.(i).(j) <- op_plus mat_coeff.(i).(j)
                (op_mul mat_coeff.(i).(k) mat_coeff.(k).(j));
        done;
        (* A[k,j,k] = A[k,k,k] * A[k,j,k-1] *)
        mat_coeff.(k).(j) <- op_mul tempkk mat_coeff.(k).(j);
    done;
  done;

  (* DEBUG *)
  if (debug) then
    Format.fprintf ffout "End of APP - mat_coeff = %a\n@?"
      print_square_mat mat_coeff;

  mat_coeff


(* =============================== *)
(* =============================== *)
(* =============================== *)


(* Second implementation - sequential, but better behavior with cache misses & with maps
    => 3 times faster than the first implementation *)

(* Alternate computation (more Array.map & cache friendly)
  A[i,j,k] =
    { i=k  && j=k  : (A[i,j,k-1])*
    { i=k  && j!=k : A[i,k,k] * A[k,j,k-1]
    { i!=k && j=k  : A[i,k,k-1] * A[k,j,k]
    { i!=k && j!=k : A[i,j,k-1] + (A[i,k,k-1] * A[k,j,k])

  Alternate schedule for in-place:
  For k=0 -> N-1:
    Compute A[k,k,k]

    For j=0 -> N-1, j!=k:
      Compute A[k,j,k]
    
    For i=0 -> N-1, i!=k
      For j=0 -> N-1, j!=k:
        Compute A[i,j,k] (using the old value A[i,k,k-1])
      Compute A[i,k,k]
*)

(* Apply the algebraic path problem to a matrix of coefficient mat_coeff *)
(* This is an inplace computation *)
let algebraic_path_problem_sequential (op_closure: int option -> int option)
  (op_plus: int option -> int option -> int option)
  (op_mul: int option -> int option -> int option) (mat_coeff : int option array array) =
  let n = Array.length mat_coeff in

  (* DEBUG *)
  if (debug) then
    Format.fprintf ffout "Start of APP - mat_coeff = %a\n@?"
      print_square_mat mat_coeff;

  (* Main loop *)
  for k = 0 to n-1 do
    if (slow_compilation && (k mod step_slow_compilation=0)) then
       Format.fprintf ffout "APP - STEP %i\n@?" k;


    (* A[k,k,k] = (A[k,k,k-1])* *)
    let tempkk = op_closure mat_coeff.(k).(k) in
    mat_coeff.(k).(k) <- tempkk;

    (* \forall j!=k, A[k,j,k] = A[k,k,k] * A[k,j,k-1] *)
    mat_coeff.(k) <- Array.mapi (fun j elem ->
      if (j!=k) then
        op_mul tempkk elem
      else
        elem
    ) mat_coeff.(k);

    let rowk = mat_coeff.(k) in

    (* \forall i!=k *)
    Array.iteri (fun i rowi ->
      let rowi = if (i!=k) then
        begin
        let coeffik = rowi.(k) in
        (* \forall j *)
        Array.mapi (fun j elem ->
          if (j!=k) then
            (* A[i,j,k] = A[i,j,k-1] + (A[i,k,k-1] * A[k,j,k]) *)
            op_plus elem (op_mul coeffik rowk.(j))
          else
            (* A[i,k,k] = A[i,k,k-1] * A[k,k,k] *)
            op_mul elem tempkk
        ) rowi
        end
        else rowi (* i=k already managed previously *)
      in
      mat_coeff.(i) <- rowi
    ) mat_coeff;
  done;

  (* DEBUG *)
  if (debug) then
    Format.fprintf ffout "End of APP - mat_coeff = %a\n@?"
      print_square_mat mat_coeff;

  mat_coeff


(* =============================== *)
(* =============================== *)
(* =============================== *)



(* Pour activer cette implem, rajouter aussi la ligne "true : package(parmap)" à _tags
    et l'option "-use-ocamlfind" après ocamlbuild dans le Makefile

open Parmap

(* Third implementation - parallel, using Parmap *)
(* Does not seem to work directly => *)
let algebraic_path_problem_parallel (op_closure: int option -> int option)
  (op_plus: int option -> int option -> int option)
  (op_mul: int option -> int option -> int option) (mat_coeff : int option array array) =
  
  let n = Array.length mat_coeff in

  (* Parallelism - uses 4 cores *)
  Parmap.set_default_ncores 4;

  (* DEBUG *)
  if (debug) then
    Format.fprintf ffout "Start of APP - mat_coeff = %a\n@?"
      print_square_mat mat_coeff;

  (* Main loop - sequential *)
  for k = 0 to n-1 do
    if (slow_compilation && (k mod step_slow_compilation=0)) then
       Format.fprintf ffout "APP - STEP %i\n@?" k;


    (* A[k,k,k] = (A[k,k,k-1])* *)
    let tempkk = op_closure mat_coeff.(k).(k) in
    mat_coeff.(k).(k) <- tempkk;

    (* \forall j!=k, A[k,j,k] = A[k,k,k] * A[k,j,k-1] *)
    mat_coeff.(k) <- Array.mapi (fun j elem ->
      if (j!=k) then
        op_mul tempkk elem
      else
        elem
    ) mat_coeff.(k);

    let rowk = mat_coeff.(k) in

    (* \forall i!=k *)
    let smat_coeff = Parmap.A mat_coeff in
    Parmap.pariteri (fun i rowi ->
      let rowi = if (i!=k) then
        begin
        let coeffik = rowi.(k) in
        (* \forall j *)
        Array.mapi (fun j elem ->
          if (j!=k) then
            (* A[i,j,k] = A[i,j,k-1] + (A[i,k,k-1] * A[k,j,k]) *)
            op_plus elem (op_mul coeffik rowk.(j))
          else
            (* A[i,k,k] = A[i,k,k-1] * A[k,k,k] *)
            op_mul elem tempkk
        ) rowi
        end
        else rowi (* i=k already managed previously *)
      in
      mat_coeff.(i) <- rowi
    ) smat_coeff;
    (* Not needed? 
    let mat_coeff = match smat_coeff with
      | A a -> a
      | L _ -> failwith "How did you get a list from an array with Parmap? oO"
    in
    mat_coeff *)
  done;

  (* DEBUG *)
  if (debug) then
    Format.fprintf ffout "End of APP - mat_coeff = %a\n@?"
      print_square_mat mat_coeff;

  mat_coeff
*)