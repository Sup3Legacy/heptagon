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

(* Functions to manage affine constraints (used in model_clocking about phase values) *)

open Format
open Clocks


type affterm = (int * string) list

type affconstr = {
    isEq : bool;                     (* Is an equality, instead of a ">=" constraint *)
    lcoeffVar : affterm; (* list of (coeff,var) => const_coeff  *)
    cst : int;
  }

type boundconstr = {  (* lbound <= varName <= ubound *)
    varName : string;
    lbound : int;
    ubound : int;
  }


(* ==================================================== *)
(* Pretty-printers *)

(* Auxilliary list functions *)
let rec extract_n_first_elems n l =
  if (n=0) then ([],l) else
  match l with
   | [] -> ([],[])
   | h::t ->
      let (lh,r) = extract_n_first_elems (n-1) t in
      (h::lh,r)

let rec partition_list n l = 
  assert(n>=0);
  let (lh,rest) = extract_n_first_elems n l in
  match rest with
    | [] -> lh::[]
    | _ -> lh::(partition_list n rest)

(* Print-out an affine expression *)
let rec print_affterm ?(bfirst = true) ff (affFunc:affterm) =
  if (bfirst && affFunc=[]) then fprintf ff "0" else
  match affFunc with
    | [] -> ()
    | (coeff, varname) :: rest ->
      let coeff = if (not bfirst) then
        begin
           if (coeff>=0) then (fprintf ff " + "; coeff)
              else (fprintf ff " - "; (-coeff))
        end
       else begin
         if (coeff<0) then (fprintf ff "-"; (-coeff)) else coeff
       end in
      if (coeff=1) then fprintf ff "%s" varname
         else fprintf ff "%i %s" coeff varname;
      print_affterm ~bfirst:false ff rest

(* Print "numSep" terms on a line before starting a new line *)
let print_affterm_multilines ?(bfirst = true) numSep ff (affFunc:affterm) =
  let llcoeffVar = partition_list numSep affFunc in
  List.iteri (fun i lcoeffVar ->
      if (i=0) then (fprintf ff "\t%a\n@?" (print_affterm ~bfirst:bfirst) lcoeffVar)
      else (fprintf ff "\t%a\n@?" (print_affterm ~bfirst:false) lcoeffVar)
    ) llcoeffVar


let print_aff_constr ff (constr:affconstr) =
  if (constr.isEq) then
    fprintf ff "\t%a = %i\n@?"
      (print_affterm ~bfirst:true) constr.lcoeffVar
      constr.cst
  else
    fprintf ff "\t%a >= %i\n@?"
      (print_affterm ~bfirst:true) constr.lcoeffVar
      constr.cst

let print_bound_constr ff (bconstr:boundconstr) =
  fprintf ff "\t%i <= %s < %i\n@?"
    bconstr.lbound bconstr.varName bconstr.ubound

let print_constraint_environment ff (lcst : (affconstr list) * (boundconstr list)) =
  let (lac, lbc) = lcst in
  fprintf ff "Affine constraints:\n@?";
  List.iter (fun ac -> fprintf ff "\t%a\n@?" print_aff_constr ac) lac;
  fprintf ff "Boundary constraints:\n@?";
  List.iter (fun bc -> fprintf ff "\t%a\n@?" print_bound_constr bc) lbc


(* ==================================================== *)

(* Constructors *)
let mk_affconstr isEq lcoeffVar cst =
  { isEq = isEq; lcoeffVar = lcoeffVar; cst = cst }

let mk_bound_constr varName l u =
  { varName = varName; lbound = l; ubound = u }

(* ==================================================== *)

(* Naming convention for phase variable & deconstruction *)
let suffix_varname = "ph_"
let lenght_suf_vn = String.length suffix_varname

let varname_from_phase_index phInd = suffix_varname ^ (string_of_int phInd)

let get_phase_index_from_varname varname =
  let strphInd = String.sub varname
    lenght_suf_vn ((String.length varname) - lenght_suf_vn) in
  int_of_string strphInd


(* Returns (varopt, ph) :
  - if varopt=None, then phase is a constant equal to ph
  - if varopt=Some phind, then phase is an affine expression (varname_phind +ph) *)
let rec get_phase_ock ock =
  let ock = ock_repr ock in match ock with
    | Cone (ph,_) -> (None, ph)
    | Cshift (sh, ock) ->
      let (varopt, ph) = get_phase_ock ock in
      (varopt, ph+sh)
    | Covar { contents = ol } -> begin
      match ol with
      | Coindex _ -> raise Unknownperiod
      | Coper ( { contents = phl}, _) -> (match phl with
        | Cophase ph -> (None, ph)
        | Cophshift (sh, phind) -> (Some phind, sh)
        | Cophindex phind -> (Some phind, 0)
      )
      | Colink ock -> get_phase_ock ock
    end
  

(* ==================================================== *)

module IntMap = Map.Make(struct type t=int let compare = Pervasives.compare end)

(* Solve the system of affine and boundary constraints.
  Returns a IntMap, associating the phase number to its value
*)
let solve_constraints (lcst : (affconstr list) * (boundconstr list)) =
  (* TODO: if list of affconstraint empty, take a default solution *)


  (* TODO *)


  (* Base option: no objective function *)

  (* TODO:
    base option: do our own resolution
    option 2: generate the constraint file
    option 3: get the sol form constraint file*)

  (* Add compiler option "-ldb" for load balancing obj function, with WCETs: no objectif function *)

  IntMap.empty


