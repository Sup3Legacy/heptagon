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
open Containers
open Clocks

(* For debugging *)
let debug = false  (* DEBUG *)
let ffout = Format.formatter_of_out_channel stdout

let max_default_phase_for_solving = 7777 (* Should be distinctive enough *)



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

let num_elem_max_per_line = 7  (* TODO: expose option ? *)

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
  List.iter (fun ac -> fprintf ff "\t%a@?" print_aff_constr ac) lac;
  fprintf ff "Boundary constraints:\n@?";
  List.iter (fun bc -> fprintf ff "\t%a@?" print_bound_constr bc) lbc

let print_list_aff_constr ff (lconstr:affconstr list) =
  List.iter (fun constr -> print_aff_constr ff constr) lconstr

let print_list_bound_constr ff (lbconstr: boundconstr list) =
  List.iter (fun constr -> print_bound_constr ff constr) lbconstr

let print_list_varname ff lvarname =
  List.iter (fun v -> fprintf ff "\t%s\n@?" v) lvarname


(* Print-out constraints using the CPLEX LP format (cf glpk doc, Appendix C) *)
let print_out_cplex_constraint ff obj_func lac lbc lgeneral linteger lbinary =
  fprintf ff "Minimize\n@?";
  print_affterm_multilines ~bfirst:true num_elem_max_per_line ff obj_func;
  fprintf ff "Subject To\n@?";
  print_list_aff_constr ff lac;
  if (lbc!=[]) then begin
    fprintf ff "Bounds\n@?";
    print_list_bound_constr ff lbc
  end;
  if (lgeneral!=[]) then begin
    fprintf ff "General\n@?";
    print_list_varname ff lgeneral;
  end;
  if (linteger!=[]) then begin
    fprintf ff "Integer\n@?";
    print_list_varname ff linteger;
  end;
  if (lbinary!=[]) then begin
    fprintf ff "Binary\n@?";
    print_list_varname ff lbinary;
  end;
  fprintf ff "End\n\n@?"


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


(* ==================================================== *)

(* Constraint manipulation *)

(* Add a term of an affine term, in order to maintain the "max 1 term per variable" property *)
let rec add_term (a,v) affterm = match affterm with
  | [] -> (a,v)::[]
  | (at,vt)::rt ->
    if (vt=v) then (
      if (at+a=0) then rt else (at+a,v)::rt
    ) else
      (at,vt)::(add_term (a,v) rt)

(* Substitution inside a constraint *)
let subst_constraint (var, optphid2, laffterm2, sh) constr =
  let rec subst_constraint_aux (var, optphid2, laffterm2, sh) affterm = match affterm with
    | [] -> ([],0)
    | (a,v)::r ->
      let (nr, shcst) = subst_constraint_aux (var, optphid2, laffterm2, sh) r in
      if (v=var) then (
        let nshcst = shcst - a*sh in  (* constant is in the other side of the (in)equality *)

        (* We multiply "laffterm2" by "a", then add it to the term of the constraints *)
        let a_times_laffterm2 = List.map (fun (c,v) -> (a*c,v)) laffterm2 in
        let nr = List.fold_left (fun acc affterm ->
          add_term affterm acc
        ) nr a_times_laffterm2 in
        match optphid2 with
        | None -> (nr, nshcst)
        | Some var2 -> ((add_term (a,var2) nr), nshcst)
      )
      else
        ((a,v)::nr,shcst)
  in
  let (lcoeffVar, shcst) = subst_constraint_aux (var, optphid2, laffterm2, sh) constr.lcoeffVar in
  { constr with lcoeffVar = lcoeffVar; cst = constr.cst + shcst }

(* Update bound constraint with a cst<=varname pr a varname<=cst *)
let rec update_bound_constraints isLowBound varname cst lbc = match lbc with
  | [] ->
    failwith "update_bound_constraints : Boundary constraint not found"
  | bc::r ->
    if (bc.varName = varname) then (
      if (isLowBound) then
        { bc with lbound = max bc.lbound cst }::r
      else
        { bc with ubound = min bc.ubound (cst+1) }::r  (* Bound constraint is "var < cst"*)
    ) else
      bc::(update_bound_constraints isLowBound varname cst r)

let transfer_1term_ac_to_bc lbc lac =
  let (lac,lbc) = List.fold_left (fun (lac_acc, lbc_acc) affconstr ->
    (* Note: The following case should probably be managed separately *)
    if (affconstr.isEq=true) then (affconstr::lac_acc, lbc_acc) else
    if ((List.length affconstr.lcoeffVar)>1) then (affconstr::lac_acc, lbc_acc) else

    if ((List.length affconstr.lcoeffVar)=0) then ( (* While we are at it... *)
      if (affconstr.cst>0) then
        failwith "Constraint: [0 >= strictly positive integer] is unsolvable";
      (lac_acc, lbc_acc)
    ) else (
      assert((List.length affconstr.lcoeffVar)=1);
      let (c,v) = List.hd affconstr.lcoeffVar in

      (* Note: coefficient is 1 or -1 if there are no decision variable
        We might have anything non-0 there if the phase var is None *)
      let lbc_acc = if (c>0) then
          let temp_float = (float affconstr.cst) /. (float c) in
          let temp = int_of_float temp_float in  (* Trunk toward 0 *)
          update_bound_constraints true v temp lbc_acc
        else if (c<0) then
          let temp_float = (float affconstr.cst) /. (float c) in
          let temp = int_of_float temp_float in  (* Trunk toward 0 *)
          update_bound_constraints false v temp lbc_acc
        else
          failwith "Coefficient in front of variable is 0."
      in
      (lac_acc, lbc_acc)
    )
  ) ([],lbc) lac in
  (lac, lbc)

(* Get rid of equalities with only one term *)
let manage_equalities lbc lac =
  let (lac,lbc) = List.fold_left (fun (lac_acc, lbc_acc) affconstr ->
    if (affconstr.isEq=false) then (affconstr::lac_acc, lbc_acc) else

    (* We have an equality *)
    (* If there is only one argument *)
    if ((List.length affconstr.lcoeffVar)>1) then (affconstr::lac_acc, lbc_acc) else


    if ((List.length affconstr.lcoeffVar)=0) then ( (* While we are at it... *)
      if (affconstr.cst!=0) then
        failwith "Constraint: [0 = non-zero constant] is unsolvable";
      (lac_acc, lbc_acc)
    ) else (
      assert((List.length affconstr.lcoeffVar)=1);
      let (c,v) = List.hd affconstr.lcoeffVar in

      (* We update the boundary condition *)
      if ((affconstr.cst mod c) != 0) then (
        fprintf ffout "Constraint : %a\n@?" print_aff_constr affconstr;
        failwith "Constraint: [c.v = cst] where c does not divide cst: v cannot be rational"
      ) else
      let value_v = affconstr.cst / c in

      (* We update the boundary constraint to be value_v <= v < value_v+1 *)
      let lbc_acc = update_bound_constraints true v value_v lbc_acc in
      let lbc_acc = update_bound_constraints false v value_v lbc_acc in

      (lac_acc, lbc_acc)
    )
  ) ([],lbc) lac in
  (lac, lbc)


(* ==================================================== *)

(* IntMap; Type of the output of the constraint resolution *)
(* StringMap: Internal type of the constraint resolution: Var_name ==> value *)

(* Convert the StringMap solution to a IntMap solution *)
let solution_to_phase_number smap =
  StringMap.fold (fun strk v imap ->
    try
      let intk = get_phase_index_from_varname strk in
      IntMap.add intk v imap
    with Failure _ -> imap  (* If variable is not ph_NNNN, then it's a binary var *)
  ) smap IntMap.empty

let check_coherency (lac : affconstr list) (lbc : boundconstr list) (lbinary : string list) msol =
  (* Check the binary constraints *)
  List.iter (fun vname ->
    try (
      let value = StringMap.find vname msol in
      if (value<0) then
        failwith ("Solution invalid - binary variable " ^ vname ^ " is negative.");
      if (value>1) then
        failwith ("Solution invalid - binary variable " ^ vname ^ " is greater than 2.");
    ) with
    | Not_found ->
      failwith ("Solution invalid - binary variable " ^ vname ^ " not found.")
  ) lbinary;

  (* Check the boundary constraints *)
  List.iter (fun bc ->
    try
      let value = StringMap.find bc.varName msol in
      if (value<bc.lbound) then
        failwith ("Solution invalid - variable " ^ bc.varName
            ^ " violates the lbound of a boundary constraint.");
      if (value>=bc.ubound) then
        failwith ("Solution invalid - binary variable " ^ bc.varName
            ^ " violates the ubound of a boundary constraint.");
    with
    | Not_found ->
      eprintf "Solution invalid - boundary constraint variable %a was not found."
        print_bound_constr bc;
      failwith "Solution invalid"
  ) lbc;

  (* Check the affine constraints *)
  List.iter (fun ac ->
    (* We evaluate the value of lcoeffVar *)
    let valcoeff = List.fold_left (fun acc (c,var) ->
      try
        let value = StringMap.find var msol in
        acc + c * value
      with
      | Not_found ->
        eprintf "Solution invalid - variable %s in constraint %a was not found."
          var  print_aff_constr ac;
        failwith "Solution invalid"
    ) 0 ac.lcoeffVar in

    (* Check the constraint *)
    if (ac.isEq) then (
      if (valcoeff!=ac.cst) then (
        eprintf "Solution invalid - equality constraint %a is not satisfied (valcoeff = %i)."
          print_aff_constr ac  valcoeff;
        failwith "Solution invalid"
      )
    ) else (
      if (valcoeff<ac.cst) then (
        eprintf "Solution invalid - inequality constraint %a is not satisfied (valcoeff = %i)."
          print_aff_constr ac  valcoeff;
        failwith "Solution invalid"
      )
    )
  ) lac


(* ==================================================== *)

(* Internal solver of constraint. Limited compared to the general case
  => It only tries to find the minimal solution to a list of affine and boundary constraint.
    "minimal" in the sense of "the earliest phase possible" *)

(* Graph structure for the constraint resolution (discarded once a solution is found ??? ) *)
(* Edge (varL, varR, c) = "varL + c <= varR" *)
type grConstrNodes = {
  name : string;
  ind : int;                      (* Position in the array of containing "grConstr" *)
  in_edges : (int * int) list;    (* (elem_index, weight) *)
  out_edges : (int * int) list;   (* (elem_index, weight) *)
  max_val : int;                  (* Max value from the cycle (min_val with same rules is 0) *)

  (* Solution currently found *)
  val_sol : int;

  (* val_sol \in [min_val_sol; max_val_sol] *)
  (* Deduced from the dependence graph and max_val *)
  min_val_sol : int;
  max_val_sol : int;
}

type grConstr = grConstrNodes array

(* Pretty-printing *)
let print_sol_grConstr ff grConstr =
  Array.iter (fun elem ->
    Format.fprintf ff "\t(i=%i) %s -> %i  ( < %i  | [%i ; %i[ )\n@?"
      elem.ind elem.name
      elem.val_sol  elem.max_val
      elem.min_val_sol elem.max_val_sol
  ) grConstr;
  Format.fprintf ff "Edges:\n";
  Array.iter (fun elem ->
    List.iter (fun (e_dst, w) ->
      Format.fprintf ff "\t%i ==(%i)==> %i\n@?"
        elem.ind w e_dst
    ) elem.out_edges
  ) grConstr


let print_msol ff msol =
  StringMap.iter (fun k v ->
    fprintf ff "\t%s => %i\n@?" k v
  ) msol

(* --- *)

(* Construction of the list of variables and associated upper bound *) 
let get_list_variable lac lbc =
  let (lres, svar_registered) = List.fold_left (fun (lacc, sreg) bc ->
    let nlacc = (bc.varName, bc.lbound, bc.ubound)::lacc in
    let nsreg = StringSet.add bc.varName sreg in
    (nlacc, nsreg)
  ) ([], StringSet.empty) lbc in

  (* Check that we did not miss any variable from lac *)
  (* By default: lbound = 0 / ubound = max_default_phase_for_solving *)
  let (lres, _) = List.fold_left (fun (lacc, sreg) ac ->
    let lvarac = List.map (fun (_,v) -> v) ac.lcoeffVar in
    let (lacc, sreg) = List.fold_left (fun (lacc, sreg) var ->
      if (StringSet.mem var sreg) then (lacc, sreg) else (* No issue *)
      (* New variable not in bounds !!! *)
      let nlacc = (var, 0, max_default_phase_for_solving)::lacc in
      let nsreg = StringSet.add var sreg in
      (nlacc, nsreg)
    ) (lacc, sreg) lvarac in
    (lacc, sreg)
  ) (lres, svar_registered) lac in
  lres


(* Construction of a table associating a variable to the affine constraints containing it *)
let build_htbl_var_to_constraint lvarname depConstrs =
  let numVars = List.length lvarname in
  let htblVar2Constr = Hashtbl.create numVars in

  List.iter (fun depConstr ->
      assert(depConstr.isEq=false);
      List.iter (fun (_,varName) ->
        try
          let lDepConstr = Hashtbl.find htblVar2Constr varName in
          let lnDepConstr = depConstr::lDepConstr in
          Hashtbl.replace htblVar2Constr varName lnDepConstr
        with
        | Not_found -> (* New element found! *)
          Hashtbl.add htblVar2Constr varName (depConstr::[])
      ) depConstr.lcoeffVar
    ) depConstrs;
  htblVar2Constr

(* Assume that we have only constraints of the form p_1 - p_2 >= c*)
let get_edge_from_dep_affconstr affconstr =
  assert(affconstr.isEq=false);
  assert((List.length affconstr.lcoeffVar)=2);
  let (c1,v1) = List.hd affconstr.lcoeffVar in
  let (c2,v2) = List.hd (List.tl affconstr.lcoeffVar) in
  assert(c1 * c2 = (-1));
  let (varL, varR) = if (c1=1) then (v2,v1) else (v1,v2) in
  (varL, varR, affconstr.cst)  (* varL + c <= varR *)

(* Split "ledges" into the one coming to "elem" and the one leaving "elem" *)
let partition_inout_edges elem ledges =
  List.fold_left (fun (accIn, accOut) edge ->
    let (varSrc, varDst, c) = edge in
    if (varDst=elem) then ((varSrc,c)::accIn, accOut) else
    if (varSrc=elem) then (accIn, (varDst,c)::accOut) else
    failwith ("Edge associated to element " ^ elem ^ " does not have it as src/dst")
  ) ([],[]) ledges

(* Initialization of the grConstr data structure *)
let build_graph_from_constraints lvarname htblVar2Constr =
  (* Build the nodes mapping preemptively, in order to use it later *)
  let mvarNameNodeGrConstr = StringMap.empty in
  let mvarNameNodeGrConstr = List.fold_left (fun macc (strVar, lb, ub) ->
    let constrNode = {
      name = strVar;
      ind = -1;
      in_edges = [];
      out_edges = [];
      max_val = ub;

      min_val_sol = lb;
      max_val_sol = ub;
      
      val_sol = (-1);
    } in
    StringMap.add strVar constrNode macc
  ) mvarNameNodeGrConstr lvarname in

  (* Build the array *)
  let (_, nodeRandom) = StringMap.choose mvarNameNodeGrConstr in
  let gr = Array.make (StringMap.cardinal mvarNameNodeGrConstr) nodeRandom in (* cardinal correct? *)
  let indgr = ref 0 in

  let mvarNameNodeGrConstr = StringMap.fold (fun varName node nmap ->
    let node = { node with ind = !indgr } in
    Array.set gr !indgr node;
    indgr := !indgr + 1;
    StringMap.add varName node nmap
  ) mvarNameNodeGrConstr StringMap.empty in

  
  (* Build the edges *)
  Hashtbl.iter (fun varName lconstr ->
    let ledges = List.map get_edge_from_dep_affconstr lconstr in
    let (lInedges, lOutedges) = partition_inout_edges varName ledges in

    let lInedges = List.map (fun (strName, w) ->
      let nodeStrName = StringMap.find strName mvarNameNodeGrConstr in
      (nodeStrName.ind, w)
    ) lInedges in
    let lOutedges = List.map (fun (strName, w) ->
      let nodeStrName = StringMap.find strName mvarNameNodeGrConstr in
      (nodeStrName.ind, w)
    ) lOutedges in

    let constrNode = StringMap.find varName mvarNameNodeGrConstr in
    let nConstrNode = {constrNode with in_edges = lInedges; out_edges = lOutedges } in
    Array.set gr nConstrNode.ind nConstrNode
  ) htblVar2Constr;
  gr



(* --- *)

(* Conversion of a grConstr to a matrix of coefficient *)
let conversion_to_mat_coeff grConstr =
  let fill_row_conv_to_mat_coeff matRow grConstrNode =
    let loutEdges = grConstrNode.out_edges in
    List.iter (fun (elem_ind, w) ->
      (* If already a constraint (redundancy), take the max *)
      match matRow.(elem_ind) with
      | None ->
        matRow.(elem_ind) <- Some w
      | Some w0 ->
        matRow.(elem_ind) <- Some (max w0 w)
    ) loutEdges;
    matRow;
  in

  let n = Array.length grConstr in

  (* Alloc *)
  let arr1 = Array.make n None in
  let mat = Array.make n arr1 in
  for i = 0 to n-1 do
    let arrTemp = Array.make n None in
    arrTemp.(i) <- Some 0;
    mat.(i) <- arrTemp;
  done;

  (* Filling mat *)
  for i = 0 to n-1 do
    mat.(i) <- fill_row_conv_to_mat_coeff mat.(i) grConstr.(i);
  done;
  mat

(* Uses the dependences of the graph to obtain tighter intevals in which the solution MUST belong *)
let find_boundaries_from_constraints grConstr =
  (* Building the matrix of coefficient *)
  let mat_coeff = conversion_to_mat_coeff grConstr in

  (* Algebraic path algorithm *)
  let cl_op = (fun iopt -> iopt) in
  let plus_op = (fun aopt bopt -> match aopt with
    | None -> bopt
    | Some a -> begin
      match bopt with
      | None -> aopt
      | Some b -> Some (max a b)
    end
  ) in
  let mul_op = (fun aopt bopt -> match aopt with
    | None -> None
    | Some a -> begin
      match bopt with
      | None -> None
      | Some b -> Some (a + b)
    end
  ) in
  let mat_coeff = AlgebraicPath.algebraic_path_problem_sequential cl_op plus_op mul_op mat_coeff in
  
  (* Update grConstr *)
  let n = Array.length grConstr in
  for i = 0 to (n-1) do
    let grNodei = grConstr.(i) in

    (* min_val_sol = maximum weigth of any path from any node to the node i *)
    let minvsol = ref grNodei.min_val_sol in
    for j = 0 to (n-1) do
      match mat_coeff.(j).(i) with
      | None -> ()
      | Some e -> minvsol := max !minvsol (e + grConstr.(j).min_val_sol);
    done;

    (* max_val_sol = min (max_val.nodej - max weigth of any path from i to this node j) *)
    let maxvsol = ref grNodei.max_val_sol in
    for j = 0 to (n-1) do
      match mat_coeff.(i).(j) with
      | None -> ()
      | Some e ->
        let candidate = grConstr.(j).max_val - e in
        maxvsol := min !maxvsol candidate;
    done;

    (* Update *)
    let grNodei = { grNodei with min_val_sol = !minvsol; max_val_sol = !maxvsol } in
    grConstr.(i) <- grNodei;
  done;
  grConstr


(* Build the solution using grConstr *)
let build_initial_solution grConstr =
  let grConstr = find_boundaries_from_constraints grConstr in

  if (debug) then (
    Format.fprintf ffout "DEBUG - find_boundaries_from_constraints done\n@?";
    Format.fprintf ffout "grConstr = %a\n@?" print_sol_grConstr grConstr
  );

  (* Minimal solution = lower boundary *)
  let linfoStrongOver = ref [] in
  let linfoSoftOver = ref [] in
  for i = 0 to (Array.length grConstr)-1 do
    let grConstrNodei = grConstr.(i) in

    (* Detection of no solution *)
    if (grConstrNodei.min_val_sol>=grConstrNodei.max_val) then
      linfoStrongOver := grConstrNodei :: !linfoStrongOver;
    if (grConstrNodei.min_val_sol>=grConstrNodei.max_val_sol) then
      linfoSoftOver := grConstrNodei :: !linfoSoftOver;

    let grConstrNodei = { grConstrNodei with val_sol = grConstrNodei.min_val_sol } in
    grConstr.(i) <- grConstrNodei;
  done;

  (* Error management *)
  if (!linfoStrongOver!=[]) then (
    Format.fprintf ffout "%a\n@?" print_sol_grConstr grConstr;
    List.iter (fun node ->
      Format.fprintf ffout "Overflow node - violent : %s (min_val = %i / max_absolute_val = %i)\n@?"
        node.name node.min_val_sol node.max_val
    ) !linfoStrongOver;
    List.iter (fun node ->
      Format.fprintf ffout "Overflow node - soft : %s (min_val = %i / max_val = %i)\n@?"
        node.name node.min_val_sol node.max_val_sol
    ) !linfoSoftOver;
    failwith ("System not solvable - constraints before the nodes makes its minimal solution overflow")
  );

  grConstr

(* --- *)

(* Main solving function *)
let solve_constraint_on_our_own lac lbc =
  (* List of variables and associated upper bound *)  
  let lvarname : (string * int * int) list = get_list_variable lac lbc in
  
  (* Table associated a variable to the affine constraints containing it *)
  let htblVar2Constr = build_htbl_var_to_constraint lvarname lac in
  
  (* Build the graph of constraint (initialized) *)
  let grConstr = build_graph_from_constraints lvarname htblVar2Constr in

  if (debug) then (
    Format.fprintf ffout "DEBUG - graph of constraints built\n@?";
    Format.fprintf ffout "grConstr = %a\n@?" print_sol_grConstr grConstr
  );

  (* Solving ! *)
  let grConstr = build_initial_solution grConstr in

  if (debug) then (
    Format.fprintf ffout "DEBUG - minimal solution found\n@?";
    Format.fprintf ffout "grConstr = %a\n@?" print_sol_grConstr grConstr
  );

  (* Going back to a StringMap *)
  let msol = Array.fold_left (fun macc grConstrNode ->
    StringMap.add grConstrNode.name grConstrNode.val_sol macc
  ) StringMap.empty grConstr in
  msol


(* ==================================================== *)

(* Name of the variable in the constraint to minimize *)
let varobj = "upBoundWeight"

let get_binary_varname varname k =
  if (k>=0) then
    varname ^ "_phval_" ^ (string_of_int k)
  else
    varname ^ "_phval_m" ^ (string_of_int (-k))

let rec gcd a b =
  assert(a>0);
  assert(b>=0);
  if (a<b) then gcd b a else
  if (b=0) then a else
  gcd b (a mod b)

let lcm a b =
  let g = gcd a b in
  a*(b/g)

let get_lcm_period lwcet = List.fold_left (fun acc (_,_,_,per,_,_) -> lcm acc per) 1 lwcet

let get_ressource_max name_ress =
  (Modules.find_ressource (Modules.qualify_ressource name_ress)).Signature.r_max

(* mmbinary: [varname : string] --> ( [phase_num : int] --> [binvarname : string]) *)
let rec fill_int_maps varname k lbound imDeltaAct =
  assert(k>=lbound);
  if (k=lbound) then imDeltaAct else (* Termination *)

  let varDeltaAct = get_binary_varname varname (k-1) in
  let imDeltaAct = IntMap.add (k-1) varDeltaAct imDeltaAct in
  fill_int_maps varname (k-1) lbound imDeltaAct

let get_mmbinary lbc =
  (* mmbinary: [varname : string] --> ( [phase_num : int] --> [binvarname : string]) *)
  let mmbinary = List.fold_left (fun mmacc bc -> 
    let mvarbin = fill_int_maps bc.varName bc.ubound bc.lbound IntMap.empty in
    StringMap.add bc.varName mvarbin mmacc
  ) StringMap.empty lbc in
  mmbinary


(* Find the min/max values of expression [opt_varphase + laffterm + sh] *)
let get_min_max_affterm lbc opt_varphase laffterm sh =
  let (minq, maxq) = match opt_varphase with
    | None -> (sh, sh)
    | Some varphase ->
      let bc_varphase = List.find (fun bc -> bc.varName=varphase) lbc in
      (sh + bc_varphase.lbound, sh + (bc_varphase.ubound-1))
  in
  let (minq, maxq) = List.fold_left (fun (accmin,acccmax) (c,v) ->
    let bc_v = List.find (fun bc -> bc.varName=v) lbc in
    if (c>0) then
      (accmin + c * bc_v.lbound, acccmax + c * (bc_v.ubound-1))
    else (
      assert(c<0);
      (accmin + c * (bc_v.ubound-1), acccmax + c * bc_v.lbound)
    )
  ) (minq, maxq) laffterm in
  assert(maxq>=minq);
  (minq, maxq)

(* Compute the phase distribution of a phase expression [opt_varphase + laffterm + sh] *)
let get_phase_distribution mmbinary opt_varphase laffterm sh =
  (* We get all the combination of contribution to the phases (ie, the equalities between qi and pi/(di)s) *)
  let m_constr_contrib_phase = IntMap.empty in

  (* Initialisation with opt_varphase and sh contribution *)
  let m_constr_contrib_phase = match opt_varphase with
    | None -> IntMap.add sh ([]::[]) m_constr_contrib_phase  (* Phase must be sh, no condition *)
    | Some varname_int -> (
      let mbinvar = try
          StringMap.find varname_int mmbinary
        with Not_found -> failwith ("Internal error: lwcet contains a linear contribution to "
            ^ varname_int ^ " which is not part of the constraint variables (place: lb - laffterm).")
      in
      IntMap.fold (fun k p_binvar macc ->
        IntMap.add (k+sh) ([p_binvar]::[]) macc  (* Remark: sum of product, from outer to inner list *)
      ) mbinvar m_constr_contrib_phase
    )
  in

  (* Adding the contribution of the laffterm one by one *)
  let shift_contrib c val_v binvar_name_v m_old_distr =
    IntMap.fold (fun val_distr lldistr macc ->
      let nlldistr = List.rev_map (fun ldistr -> binvar_name_v::ldistr) lldistr in
      IntMap.add (val_distr + c*val_v) nlldistr macc
    ) m_old_distr IntMap.empty
  in
  (* Combine the distrib by adding their terms together *)
  let combine_distrib mdistr1 mdistr2 =
    IntMap.merge (fun k odistr1 odistr2 -> match (odistr1, odistr2) with
      | (None, None) -> None
      | (Some ll, None) -> Some ll
      | (None, Some ll) -> Some ll
      | (Some ll1, Some ll2) -> Some (List.rev_append ll1 ll2)
    ) mdistr1 mdistr2
  in

  let m_constr_contrib_phase = List.fold_left (fun macc (c, intname_v) ->  (* For each term in laffterm... *)
    let mbinvar_v = try
        StringMap.find intname_v mmbinary
      with Not_found -> failwith ("Internal error: lwcet contains an affine contribution to "
          ^ intname_v ^ " which is not part of the constraint variables (place: lb - laffterm).")
    in

    (* For each possible binary value of v : (val_v, binvar_name_v)... *)
    let nmacc = IntMap.fold (fun val_v binvar_name_v nmacc ->

      (* We update nmacc by taking macc (the old distribution), shifted by the contrib of this value of v,
        Then, adding it to nmacc *)
      let mshifted_contrib = shift_contrib c val_v binvar_name_v macc in
      let nmacc = combine_distrib nmacc mshifted_contrib in
      nmacc
    ) mbinvar_v IntMap.empty in

    nmacc
  ) m_constr_contrib_phase laffterm in
  m_constr_contrib_phase

(* Pretty printer for the phase distribution (produced by "get_phase_distribution") *)
let print_phase_distrib ff m_contrib =
  let print_contrib ff lcontrib =
    fprintf ff "(";
    List.iter (fun s -> fprintf ff "%s * " s) lcontrib;
    fprintf ff ")"
  in
  IntMap.iter (fun k vdistr ->
    fprintf ff "%i -> [ " k;
    List.iter (fun lcontrib -> fprintf ff "%a + " print_contrib lcontrib) vdistr;
    fprintf ff "]\n@?"
  ) m_contrib


(* For load balancing and ac_to_binary_conversion
   Naming convention for when a contribution phase depend on an underspecified operator *)
let count_temp_wcet_contrib = ref 0
let get_temp_wcet_contrib_name _ =
  count_temp_wcet_contrib := !count_temp_wcet_contrib + 1;
  "tmp_wcontr_" ^ (string_of_int !count_temp_wcet_contrib)


(* ==================================================== *)


(* For binary load balancing - transform the dependence constraints *)
let convert_ac_to_binary_simplecase mperiods mmbinary ac_int =
  (* Checking the form of ac_int *)
  (* Note: ac_int was preprocessed: there are 2 terms in it *)
  assert((List.length ac_int.lcoeffVar)=2);
  assert((not ac_int.isEq));

  let (c1, v1) = List.hd ac_int.lcoeffVar in
  let (c2, v2) = List.hd (List.tl ac_int.lcoeffVar) in
  let (posvar,negvar) = match c1 with
    | 1 -> ( assert(c2=(-1)); (v1, v2) )
    | (-1) -> ( assert(c2=1); (v2, v1) )
    | _ -> (failwith "Unrecognized dependence constraint form")
  in
  let cst = ac_int.cst in
  (* The constraint is " posvar - negvar >= cst " *)

  let perT = StringMap.find posvar mperiods in
  let perS = StringMap.find negvar mperiods in
  let mbinvarT = StringMap.find posvar mmbinary in
  let mbinvarS = StringMap.find negvar mmbinary in


  (* Conversion of the constraint *)
  (* v_T - v_S >= C   =====>
    (\forall S->T) (\forall i) \delAct_{S,i} <= \sum_{max(0, i+C)}^{period(T)} \delAct_{T,j} *)
  
  (* Aux function: get the list of j such that max(0,min) <= j < current *)
  let rec get_list_of_j min current res =
    if ((current<0) || (current < min)) then res
    else get_list_of_j min (current-1) (current::res)
  in
  let rec convert_bool info_dep info_constr res i =
    assert(i>=0); if (i=0) then res else

    let (perT, mbinvarT, mbinvarS) = info_dep in
    let (posvar, negvar, cst) = info_constr in

    (* \delAct_{S,i} <= \sum_{j = max(0, i+C)}^{period(T)} \delAct_{T,j} *)

    if (not (IntMap.mem (i-1) mbinvarS)) then
      (* \delAct_{S,i} does not exists because it falls outside of the
          preprocessed bounding range => do not add any constraint *)
      convert_bool info_dep info_constr res (i-1)
    else
    let deltaSi = try IntMap.find (i-1) mbinvarS
      with Not_found -> failwith ("Internal error  (convert_bool) - should not happen")
    in
    let lcoeff_bool = (-1, deltaSi)::[] in  


    let lj = get_list_of_j (i-1+cst) (perT-1) [] in
    let lcoeff_bool = List.fold_left (fun acc j ->
      try
        let deltaTj = IntMap.find j mbinvarT in
        (1, deltaTj)::acc
      with Not_found ->
        acc  (* \delAct_{T,j} does not exists because it falls outside of the
                   preprocessed bounding range => do not add any term *)
    ) lcoeff_bool lj in


    let ac_bool = mk_affconstr false lcoeff_bool 0 in
    convert_bool info_dep info_constr (ac_bool::res) (i-1)
  in

  let lac_bool = convert_bool (perT, mbinvarT, mbinvarS) (posvar, negvar, cst) [] perS in
  lac_bool

let debug_ac_bin_fc = false (* DEBUG for the convert_ac_to_binary_fullcase function *)

let convert_ac_to_binary_fullcase mperiods lbc mmbinary ac_int =
  (* Constraint ac_int might have additional terms coming from the decision variables *)
  (* Note: we cannot guarranty that there must be a term with a +/-1 as coefficient in ac_int *)

  (* Heuristic (probably not optimal): we find the term with the most variability and put it on the right *)
  (* It should minimize the amount of combinations... :/ *)
  let lcoeffVar = ac_int.lcoeffVar in
  let cst = ac_int.cst in

  (* Heuristic of selection *)
  let select_1_or_highest_coeff mperiods lcoeffVar =
    (* We check if there is a term with a 1 coeff somewhere *)
    let o_1coeff_term = List.fold_left (fun oacc (c,v) ->
      if (c=1) then (
        if (oacc=None) then (Some (c,v)) else oacc
      ) else oacc
    ) None lcoeffVar in 
    match o_1coeff_term with
    | Some term -> term
    | None ->

    (* Else, we select the term with the highest period (HEURISTIC) *)
    let (_, o_hicoeff_term) = List.fold_left (fun (cand_acc, oterm_acc) (c,v) ->
      let per_v = try StringMap.find v mperiods
        with Not_found -> failwith ("convert_ac_to_binary: period for " ^ v ^ " was not found.")
      in
      let candidate = abs (c * per_v) in
      if (candidate > cand_acc) then
        (candidate, (Some (c,v)))
      else
        (cand_acc, oterm_acc)
    ) (0, None) lcoeffVar in
    match o_hicoeff_term with
    | None -> failwith "Internal compilation error: should have selected at least a term"
    | Some term -> term
  in

  (* DEBUG *)
  if (debug_ac_bin_fc) then
    fprintf ffout "\nDEBUG ac_to_binary - Starting - ac_int = %a\n@?" print_aff_constr ac_int;

  let right_term : (int * string) = select_1_or_highest_coeff mperiods lcoeffVar in
  let lcoeffVar_left = List.filter (fun term -> not (right_term=term)) lcoeffVar in
  let lcoeffVar_left = List.map (fun (c,v) -> (-c,v)) lcoeffVar_left in
  assert( (List.length lcoeffVar) = 1 + (List.length lcoeffVar_left));

  (* Comparaison: lcoeffVar_left + cst <= right_term *)
  (* We use get_phase_distrib to get all combination going into a given phase *)
  let mdistrib_left = get_phase_distribution mmbinary None lcoeffVar_left cst in
  let mdistrib_right = get_phase_distribution mmbinary None (right_term::[]) 0 in

  (* Note: mdistrib_right has only one term with one variable *)


  (* DEBUG *)
  if (debug_ac_bin_fc) then (
    fprintf ffout "DEBUG ac_to_binary - m_distrib_left = %a\n@?" print_phase_distrib mdistrib_left;
    fprintf ffout "DEBUG ac_to_binary - mdistrib_right = %a\n@?" print_phase_distrib mdistrib_right
  );


  (* We (maybe) create new temporary variables for the left side *)
  let b_create_var_left_side = if ((List.length lcoeffVar_left) > 1) then true else (
      assert((List.length lcoeffVar_left) = 1);
      let (c,v) = List.hd lcoeffVar_left in
      (c!=1)
    ) in
  let (qvname, mbinvar_temp_left) = if (b_create_var_left_side) then
      (* Create a new temporary variable for lcoeffVar_left, in all cases *)
      let (minq, maxq) = get_min_max_affterm lbc None lcoeffVar_left cst in
      (* DEBUG
      fprintf ffout "DEBUG ac_to_binary - minq = %i | maxq = %i\n@?" minq maxq; *)
      let qvname = get_temp_wcet_contrib_name () in
      let mqbinvar = fill_int_maps qvname (maxq+1) minq IntMap.empty in
      (qvname, mqbinvar)
    else (
      (* We just recover the binary variables of the unique left term with a 1 coefficient *)
      assert((List.length lcoeffVar_left) = 1);
      let (c,v) = List.hd lcoeffVar_left in
      let mbinvar_v = StringMap.find v mmbinary in
      ("UNUSED_VAR_NAME", mbinvar_v)    (* If this appear in the resulting program, there is an issue*)
  ) in


  (* DEBUG *)
  if (debug_ac_bin_fc) then (
    fprintf ffout "DEBUG ac_to_binary - temp var left side created\n@?";
    fprintf ffout "DEBUG ac_to_binary - b_create_var_left_side = %b\n@?" b_create_var_left_side;
    fprintf ffout "DEBUG ac_to_binary - mbinvar_temp_left = [@?";
    IntMap.iter (fun k v ->
      fprintf ffout "\n\t%i -> %s@?" k v
    ) mbinvar_temp_left;
    fprintf ffout " ]\n@?"
  );

  (* Unicity constraint if b_create_var_left_side *)
  let lac_unicity = if (b_create_var_left_side) then
    let lcoeff_unicity = IntMap.fold (fun _ varbin acc ->
      (1, varbin)::acc
    ) mbinvar_temp_left [] in
    let ac_unicity = mk_affconstr true lcoeff_unicity 1 in
    ac_unicity::[]
  else
    []
  in


  (* Building the constraints between the left and the right side *)
  let m_binvar_right = IntMap.map (fun lldistr -> 
    assert((List.length lldistr)=1);
    let ldistr = List.hd lldistr in
    assert((List.length ldistr)=1);
    List.hd ldistr
  ) mdistrib_right in

  let lac_bin = if (not (ac_int.isEq)) then
    (* (\forall phase) [mbinvar_temp_left]_{phase} <= \sum_{phase'>=phase} [mdistrib_right]_{phase'} *)
    IntMap.fold (fun phval binvar_left lacc ->
      let lcoeffVar = ((-1), binvar_left)::[] in 
      let lcoeffVar = IntMap.fold (fun k binvar_r lacc ->
        if (k>=phval) then
          (1, binvar_r)::lacc
        else
          lacc
      ) m_binvar_right lcoeffVar in

      let nac_phasek = mk_affconstr false lcoeffVar 0 in
      nac_phasek::lacc
    ) mbinvar_temp_left []
  else
    (* (\forall phase) [mbinvar_temp_left]_{phase} <= [mdistrib_right]_{phase} *)
    IntMap.fold (fun phval binvar_left lacc ->
      let binvar_r = IntMap.find phval m_binvar_right in
      let lcoeffVar = (1, binvar_r)::((-1), binvar_left)::[] in 
      let nac_phasek = mk_affconstr false lcoeffVar 0 in
      nac_phasek::lacc
    ) mbinvar_temp_left []
  in


  (* DEBUG *)
  if (debug_ac_bin_fc) then (
    fprintf ffout "DEBUG ac_to_binary - lac_bin built\n@?";
    fprintf ffout "lac_bin = %a\n@?" print_list_aff_constr lac_bin
  );


  (* Building the constraints on the new temporary variable from the left side *)
  let lac_temp = if (b_create_var_left_side) then
    IntMap.fold (fun k lldistr_left lacc ->
      let temp_binvar_phasek = IntMap.find k mbinvar_temp_left in
      List.fold_left (fun lacc ldistr ->
        (* Constraint: (\sum ldistr) - (size(ldistr)-1) <= q_{kval} *)
        let lcoeff_ac_temp = (1, temp_binvar_phasek)::[] in
        let lcoeff_ac_temp = List.fold_left (fun acc elemdistr ->
          (-1, elemdistr)::acc
        ) lcoeff_ac_temp ldistr in

        let ac_temp = mk_affconstr false lcoeff_ac_temp (1-(List.length ldistr)) in
        ac_temp::lacc
      ) lacc lldistr_left
    ) mdistrib_left []
  else [] in


  (* DEBUG *)
  if (debug_ac_bin_fc) then (
    fprintf ffout "lac_temp = %a\n@?" print_list_aff_constr lac_temp;
    fprintf ffout "DEBUG ac_to_binary - Additional bin constraints built. Ending\n@?"
  );

  (* Returns built objects *)
  let mbuilt_binvar = if (b_create_var_left_side) then Some (qvname, mbinvar_temp_left) else None in
  let lac_res = List.rev_append lac_bin (List.rev_append lac_unicity lac_temp) in
  (lac_res, mbuilt_binvar)

let convert_ac_to_binary b_no_underspec_ops mperiods lbc mmbinary lac =
  (* DEBUG *)
  if (debug) then
    fprintf ffout "... Load balancing - convert_ac_to_binary started\n@?";

  List.fold_left (fun (lac_acc, mmbinary_acc) ac_int ->

    (* Very quick check*)
    let bcasesimple = b_no_underspec_ops in

    (* Bit more complicated check: is "ac_int" of the form "p1 - p2 >= c" ?*)
    let bcasesimple = if (bcasesimple) then true else begin
      if ((List.length ac_int.lcoeffVar)!=2) then false else
      if (ac_int.isEq) then false else

      let (c1, v1) = List.hd ac_int.lcoeffVar in
      let (c2, v2) = List.hd (List.tl ac_int.lcoeffVar) in
      match c1 with
        | 1    -> (c2==(-1))
        | (-1) -> (c2==1)
        | _ -> false
    end in

    (* Convertion enabled ! *)
    let (lac_bin, onbinvar) = if bcasesimple then
      let lac_bin = convert_ac_to_binary_simplecase mperiods mmbinary_acc ac_int in
      (lac_bin, None)
    else 
      let (lac_bin, oint_name_mnbinvar) = convert_ac_to_binary_fullcase mperiods lbc mmbinary_acc ac_int in
      (lac_bin, oint_name_mnbinvar)
    in

    (* Merge the newly built object with the accumulators *)
    let mmbinary_res = match onbinvar with
      | None -> mmbinary_acc
      | Some (int_name, mbinvar) -> StringMap.add int_name mbinvar mmbinary_acc
    in
    (List.rev_append lac_bin lac_acc), mmbinary_res
  ) ([], mmbinary) lac


(* Load_balancing cost function *)
(* Most of this function is used for the boolean version (busedforbool remove unneeded constraints) *)
(*      binversion => Do we generate the binary version of the constraints? *)
let load_balancing binversion b_no_underspec_ops mperiods lwcet lac lbc =
  (* * Binary variable to create:
       For each phase variable T, create (u-l) variable delAct_{i,T}, as described in "lbc"
     * Set of constraints to add:
      -> (\forall T) \sum_i i*delAct_{i,T} - v_T = 0
      -> \forall T) \sum_i delAct_{i,T} = 1
      -> (\forall j) \sum_{T} delAct_{j mod per(T),T} * W_T \leq [varobj]
     * Objective function is "minimize [varobj]" *)

  (* DEBUG *)
  if (debug) then
    fprintf ffout "Entering Load balancing constraints generation/adaptation\n@?";

  (* 1) Binary variables - lbc should list all variable needed *)
  
  (* mmbinary: [varname : string] --> ( [phase_num : int] --> [binvarname : string]) *)
  let mmbinary = get_mmbinary lbc in
  let lbinary = StringMap.fold (fun _ mv acc ->
    IntMap.fold (fun _ binvar acc ->
      binvar::acc
    ) mv acc
  ) mmbinary [] in

  (* DEBUG *)
  if (debug) then
    fprintf ffout "... Load balancing - binary variable created\n@?";

  (* 2) Objective function *)
  let obj_func = (1, varobj)::[] in
  let lgeneral = varobj::[] in
  let linteger = if (binversion) then [] else
      (StringMap.fold (fun k _ acc -> k::acc) mmbinary [])
  in

  (* 3) Adding affine constraints *)
  let lac_link_unic = List.fold_left (fun acc bc ->
    let varname_int = bc.varName in
    let mbinvar = StringMap.find varname_int mmbinary in

    (* a) Link between integral and binary constraints:
      (\forall T) \sum_i i*delAct_{i,T} - v_T = 0 *)
    let lcoeff_link = (-1, varname_int)::[] in
    let lcoeff_link = IntMap.fold (fun i varbin acc -> 
      if (i!=0) then (i, varbin)::acc else acc
    ) mbinvar lcoeff_link in
    let ac_link = mk_affconstr true lcoeff_link 0 in

    (* b) Unicity of the 1 value acrodd binary constraints:
      (\forall T) \sum_i delAct_{i,T} = 1  *)
    let lcoeff_unicity = IntMap.fold (fun _ varbin acc ->
      (1, varbin)::acc
    ) mbinvar [] in
    let ac_unicity = mk_affconstr true lcoeff_unicity 1 in

    if (binversion) then ac_unicity :: acc else  (* Binary case: no ac_link *)
    ac_link :: ac_unicity :: acc
  ) [] lbc in

  (* DEBUG *)
  if (debug) then
    fprintf ffout "... Load balancing - non-wcet/ressources constraints managed\n@?";

  (* c) (\forall j) \sum_{T} delAct_{j mod per(T),T} * W_T <= [varobj] *)
  (* d) (\forall Ressource) (\forall j) \sum_{T} delAct_{j mod per(T),T} * R_T <= R_max *)
  (*  We get this constraint from the information from lwcet *)
  (* Note: lwcet : (opt_varphase, sh, per, owcet, lress) list *)
  let max_phase = get_lcm_period lwcet in

  let arr_wcet_lcoeff = Array.make max_phase [] in (* jth cell => - \sum_{T} delAct_{j mod per(T),T} * W_T *)
  let arr_wcet_const = Array.make max_phase 0 in   (* jth cell => Const of the jth constraint *)

  (* Ressources map: m_arr_ress : name_ressource ==> (arr_lcoeff, arr_const) *)
  let m_arr_ress = List.fold_left (fun mres (_,_,_,_,_,lress) ->
    List.fold_left (fun mres (name_ress, v) ->
      if (v=0) then mres else
      if (StringMap.mem name_ress mres) then mres else

      let ress_max = get_ressource_max name_ress in
    
      let arr_lcoeff = Array.make max_phase [] in
      let arr_const = Array.make max_phase (-ress_max) in
      StringMap.add name_ress (arr_lcoeff, arr_const) mres
    ) mres lress
  ) StringMap.empty lwcet in


  let (mqbinvar, lac_qtemp) = List.fold_left (fun (mqbinvar_acc, lac_qtemp_acc) (opt_varphase, laffterm, sh, per, owcet, lress) ->
    match owcet with None -> (mqbinvar_acc, lac_qtemp_acc) (* ASSUMPTION "no wcet" => "wcet = 0" *)
    | Some wcet ->

    assert(max_phase mod per = 0);
    let ninstance = max_phase / per in

    if (laffterm=[]) then (
      match opt_varphase with
      | None ->
        (* We update the constant
          The constant is on the right side of the >=, so it's a "+" *)
        for k = 0 to (ninstance-1) do
          arr_wcet_const.(sh + k*per) <- arr_wcet_const.(sh + k*per) + wcet
        done;

        List.iter (fun (rname, rval) ->
          let (_, arr_ress_const) = StringMap.find rname m_arr_ress in
          for k = 0 to (ninstance-1) do
            arr_ress_const.(sh + k*per) <- arr_ress_const.(sh + k*per) + rval
          done
        ) lress;
        (mqbinvar_acc, lac_qtemp_acc)

      | Some varname_int ->
        (* TODO DEBUG
        fprintf ffout "\t(%s + %i, per = %i => wcet = %i);\n" varname_int  sh per wcet;
        fprintf ffout "\t(ninstance = %i);\n" ninstance;
        *)

        (* We recover the binary variables *)
        let mbinvar = try
            StringMap.find varname_int mmbinary
          with Not_found -> failwith ("Internal error: lwcet contains a contribution to "
              ^ varname_int ^ " which is not part of the constraint variables.")
        in
        
        (* Wcet constraints *)
        IntMap.iter (fun shvar binvar ->
          (* By construction, we should not have an overflow there *)
          assert(0<=sh+shvar);
          assert(sh+shvar<per);

          (* The terms are on the left side of the >=, so it's a "-" *)
          for k = 0 to (ninstance-1) do
            arr_wcet_lcoeff.(k*per + sh + shvar) <- ((-wcet), binvar) :: arr_wcet_lcoeff.(k*per + sh + shvar)
          done
        ) mbinvar;

        (* Ressource constraints *)
        List.iter (fun (rname, rval) ->
          let (arr_ress_lcoeff, _) = StringMap.find rname m_arr_ress in
          IntMap.iter (fun shvar binvar ->
            (* By construction, we should not have an overflow there *)
            assert(0<=sh+shvar);
            assert(sh+shvar<per);

            (* The terms are on the left side of the >=, so it's a "-" *)
            for k = 0 to (ninstance-1) do
              arr_ress_lcoeff.(k*per + sh + shvar) <- ((-rval), binvar) :: arr_ress_lcoeff.(k*per + sh + shvar)
            done
          ) mbinvar
        ) lress;

        (mqbinvar_acc, lac_qtemp_acc)
    ) else (
      (* laffterm is not empty => no constant term (arr_XXX_const are untouched) *)
      
      (* Because the contribution to a given phase introduce products between binary decision variable
        and binary phase variable, we need to trick! :D *)
      (* Example: WCET/ressource contribution at phase "p+2d+1"
        (i.e.: opt_varphase = Some p / laffterm = [(2,d)] / ph = 1 / per = 4)
          => With pi the binary variable associated to p, di the binary variable associated to d

          Classical way (if no trick is used): the contribution to the 4 phases are:
            phase 0 => 0
            phase 1 => wcet * (p0.d0)
            phase 2 => wcet * (p1.d0)
            phase 3 => wcet * (p2.d0 + p0.d1)
          ... which is clearly an issue, because the pi and di are both binary variable.

          Trick: We introduce "q = p+2d+1" and consider its binary variables qi
              (defined on all the possible values "i" of q, and not only the one below per !!!)
            => we can directly use the "qi*wcet" in the wcet/ressource constraint
            => However, we need to add the following constraints:
              => qi are binary variables
              => Unicity of the qi (\sum_i qi = 1)
              => Link between the qi, the pi and the di
          Remark: no need to actually introduce q. The qi are the only ones needed.

          Link between the qi, pi and di (qi defined for 1=min_value <= i <= max_value=6):
            q1 = p0.d0  |  q2 = p1.d0  |  q3 = p2.d0 + p0.d1
            q4 = p3.d0 + p1.d1  |  q5 = p2.d1  |  q6 = p3.d1
          
          => Associated linear constraints to replace these equalities (using the fact everyone is binary):
            p0+d0-1 <= q1
            p1+d0-1 <= q2
            p2+d0-1 <= q3    p0+d1-1 <= q3
            p3+d0-1 <= q4    p1+d1-1 <= q4
            p2+d1-1 <= q5
            p3+d1-1 <= q6

            (note: we need all of these constraint so that it is valid)
      *)

      (* qbinvar : ( [phase_num : int] --> [binvarname : string]) where minq <= phase_num <= maxq *)
      let (minq, maxq) = get_min_max_affterm lbc opt_varphase laffterm sh in

      let qvname = get_temp_wcet_contrib_name () in  (* Naming convention *)
      let mqbinvar = fill_int_maps qvname (maxq+1) minq IntMap.empty in

      (* DEBUG *)
      if (debug) then (
        let print_opt_string ff ovarph = match ovarph with
          | None -> fprintf ff "None"
          | Some varph -> fprintf ff "%s" varph
        in
        fprintf ffout "DEBUG - laffterm non-null - introducing qvname = %s (for phase (%a %a + %i), per = %i)\n@?"
          qvname  print_opt_string opt_varphase (print_affterm ~bfirst:false) laffterm sh per;
        fprintf ffout "\t\tminq = %i | maxq = %i\n@?" minq maxq
      );

      (* We fill the arrays - Wcet constraints *)
      IntMap.iter (fun shvar qbinvar ->
        (* By construction, we should not have an overflow there *)
        assert(0<=shvar);
        if (shvar>=per) then () else (* Ignore the binary variable of q above the period *)
        (* The terms are on the left side of the >=, so it's a "-" *)
        for k = 0 to (ninstance-1) do
          arr_wcet_lcoeff.(k*per + shvar) <- ((-wcet), qbinvar) :: arr_wcet_lcoeff.(k*per + shvar)
        done
      ) mqbinvar;

      (* Ressource constraints *)
      List.iter (fun (rname, rval) ->
        let (arr_ress_lcoeff, _) = StringMap.find rname m_arr_ress in
        IntMap.iter (fun shvar qbinvar ->
          (* By construction, we should not have an overflow there *)
          assert(0<=shvar);
          if (shvar>=per) then () else (* Ignore the binary variable of q above the period *)

          (* The terms are on the left side of the >=, so it's a "-" *)
          for k = 0 to (ninstance-1) do
            arr_ress_lcoeff.(k*per + shvar) <- ((-rval), qbinvar) :: arr_ress_lcoeff.(k*per + shvar)
          done
        ) mqbinvar
      ) lress;

      (* We now build the constraints about the binary variable qi *)
      (* First constraint: \sum_i q_i = 1 *)
      let lcoeff_unicity = IntMap.fold (fun _ varbin acc ->
        (1, varbin)::acc
      ) mqbinvar [] in
      let ac_unicity = mk_affconstr true lcoeff_unicity 1 in

      (* DEBUG
      if (debug) then
        fprintf ffout "DEBUG - laffterm non-null: ac_unicity = %a\n@?" print_aff_constr ac_unicity; *)

      (* Second set of constraint: linking the qi with the pi and the (di)s *)
      let m_constr_contrib_phase = get_phase_distribution mmbinary opt_varphase laffterm sh in

      (* DEBUG TODO *)
      if (debug) then
        fprintf ffout "DEBUG - laffterm non-null: m_constr_contrib_phase = %a\n@?"
          print_phase_distrib m_constr_contrib_phase;

      (* We use m_constr_contrib_phase to build the constraints on the mqbinvar *)
      let lqvar_constr = IntMap.fold (fun kval lldistr lacc ->
        assert(kval>=minq);
        assert(kval<=maxq);
        let qbinvar_k = IntMap.find kval mqbinvar in

        (* For each list in lldistr, do a constraint *)
        let nlconstr = List.map (fun ldistr ->
          (* Constraint: (\sum ldistr) - (size(ldistr)-1) <= q_{kval} *)
          let lcoeff_qvar = (1, qbinvar_k)::[] in
          let lcoeff_qvar = List.fold_left (fun acc elemdistr ->
            (-1, elemdistr)::acc
          ) lcoeff_qvar ldistr in

          let ac_qvar = mk_affconstr false lcoeff_qvar (1-(List.length ldistr)) in
          ac_qvar
        ) lldistr in
        List.rev_append nlconstr lacc
      ) m_constr_contrib_phase [] in

      (* We complete lqvar_constr with the qi which does not have anything associated in its distribution *)
      let lqvar_constr = IntMap.fold (fun valph qbinvar lacc ->
        if (IntMap.mem valph m_constr_contrib_phase) then lacc else
        
        (* We add the constraint "qi=0" *)
        let ac_qvar = mk_affconstr true ((1,qbinvar)::[]) 0 in
        ac_qvar::lacc
      ) mqbinvar lqvar_constr in


      (* Save the new constraints and binary variable in a data structure*)
      let n_lac_qtemp_acc = ac_unicity::(List.rev_append lqvar_constr lac_qtemp_acc) in
      let n_mqbinvar_acc = StringMap.add qvname mqbinvar mqbinvar_acc in

      (n_mqbinvar_acc, n_lac_qtemp_acc)
    )
  ) (StringMap.empty, []) lwcet in


  (* DEBUG
  fprintf ffout "arr_wcet_lcoeff = [";
  Array.iter (fun lelem ->
    fprintf ffout "%a; " (print_affterm ~bfirst:true) lelem
  ) arr_wcet_lcoeff;
  fprintf ffout "]\n@?";

  fprintf ffout "arr_wcet_const = [";
  Array.iter (fun el ->
    fprintf ffout "%i; " el
  ) arr_wcet_const;
  fprintf ffout "]\n@?"; *)
  
  let arr_ac_wcet = Array.map2 (fun lcoeff_weight cst ->
    let lcoeff_weight = (1, varobj)::lcoeff_weight in
    mk_affconstr false lcoeff_weight cst
  ) arr_wcet_lcoeff arr_wcet_const in
  let lac_wcet = Array.to_list arr_ac_wcet in

  (* For all ressource *)
  let larr_ac_ress = StringMap.fold (fun _ (arr_lcoeff, arr_const) lacc ->
    (* For all phases *)
    let arr_ac = Array.map2 (fun lcoeff_weight cst ->
      mk_affconstr false lcoeff_weight cst
    ) arr_lcoeff arr_const in
    arr_ac :: lacc
  ) m_arr_ress [] in
  let lac_ress = List.fold_left (fun lacc arr ->
    (Array.to_list arr) @ lacc
  ) [] larr_ac_ress in

  (* Filter ressource with no variable constraint *)
  let lac_ress = List.fold_left (fun lacc ac -> 
    if (ac.lcoeffVar=[]) then (
      assert(ac.cst<=0);
      lacc
    ) else ac::lacc
  ) [] lac_ress in

  (* Boolean version: convertion of the original ac *)
  let (lac, mmbinary) = if (binversion) then
    convert_ac_to_binary b_no_underspec_ops mperiods lbc mmbinary lac
  else (lac, mmbinary) in
  let lbc = if (binversion) then [] else lbc in


  (* Wrapping things up! *)
  let lbinary = StringMap.fold (fun _ mbinvar lacc ->
    IntMap.fold (fun _ binvar lacc -> binvar::lacc) mbinvar lacc
  ) mqbinvar lbinary in
  let lac = List.rev_append lac_qtemp (
        List.rev_append lac_ress
          (List.rev_append lac_wcet
           (List.rev_append lac_link_unic lac)
          )
      )
  in

  (* DEBUG *)
  if (debug) then
    fprintf ffout "... Load balancing - done\n@?";

  (lac, lbc, lgeneral, linteger, lbinary, obj_func, mmbinary)


(* ==================================================== *)
(* Export of constraints and import of solution *)

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

(* Generate a constraint file, then stop the compilation flow *)
(* Option: -genphconstr [file_name] *)
let generate_constraint lac lbc lgeneral linteger lbinary obj_func =
  let ocout = open_out !Compiler_options.constraint_filename in
  let ffout = formatter_of_out_channel ocout in
  print_out_cplex_constraint ffout obj_func lac lbc lgeneral linteger lbinary;
  close_out ocout;

  (* === Stopping compiler flow now === *)
  failwith "Constraint file generation successfully done - compilation flow terminated."

(* Solution file is a serie of lines "[namevar] -> [integral value]"*)
(* Option: -solphconstr [file] *)
let parse_solution lac lbc lbinary =
  let lsol = parse_file (Parser_sol.solution Lexer_sol.main)
                  !Compiler_options.solution_filename in
  let msol = List.fold_left (fun macc (k,v) ->
    StringMap.add k v macc
  ) StringMap.empty lsol in

  (* DEBUG *)
  if (debug) then
    fprintf ffout "Solution found:\n%a\n@?" print_msol msol;

  check_coherency lac lbc lbinary msol;

  (* DEBUG *)
  if (debug) then
    fprintf ffout "Solution is coherent.\n@?";

  msol

(* The binary load balancing destroy the integral variable => we recover them *)
let recover_integral_var mmbinary msol =
  let msol = StringMap.fold (fun var_int mbinvar macc ->
    let mbinvar_true = IntMap.filter (fun ph binvar ->
      let val_var_bin = try
        StringMap.find binvar msol
      with Not_found ->
        failwith "recover_integral_var: binvar not found in macc"
      in
      (val_var_bin = 1)
    ) mbinvar in
    assert((IntMap.cardinal mbinvar_true) = 1);
    let (val_var_int, _) = IntMap.min_binding mbinvar_true in

    StringMap.add var_int val_var_int macc
  ) mmbinary StringMap.empty in

  (* DEBUG *)
  if (debug) then
    fprintf ffout "Solution after recovery:\n%a\n@?" print_msol msol;

  msol

let print_wcet_balance lwcet msol =
  (* lwcet : (potential phase_variable_name, list of affine terms, shift of ock, period of ock,
                    potential assigned WCET, list of ressources used *)

  (* We initialize the data structure to collect the contributions of everybody *)
  let max_phase = get_lcm_period lwcet in
  let arr_wcet = Array.make max_phase 0 in

  (* Ressources map: m_arr_ress : name_ressource ==> arr_contrib *)
  let m_arr_ress = List.fold_left (fun mres (_,_,_,_,_,lress) ->
    List.fold_left (fun mres (name_ress, v) ->
      if (v=0) then mres else
      if (StringMap.mem name_ress mres) then mres else

      let ress_max = get_ressource_max name_ress in
    
      let arr_contrib = Array.make max_phase 0 in
      StringMap.add name_ress arr_contrib mres
    ) mres lress
  ) StringMap.empty lwcet in

  (* Collection start *)
  List.iter (fun (ophvar, laffterm, sh, per, owcet, lress) ->
    (* We evaluate the phase: ophvar + laffterm + sh *)
    let phase_val = match ophvar with
      | None -> sh
      | Some phvar -> StringMap.find phvar msol
    in
    let phase_val = List.fold_left (fun acc (c,v) ->
      let value_v = StringMap.find v msol in
      acc + c * value_v
    ) phase_val laffterm in

    (* For every instance of the phase *)
    assert(max_phase mod per = 0);
    let ninstance = max_phase / per in
    for k = 0 to (ninstance-1) do (
      match owcet with
      | None -> ()
      | Some wcet -> arr_wcet.(phase_val + k*per) <- arr_wcet.(phase_val + k*per) + wcet
      ;
      List.iter (fun (rname, rval) ->
        let arr_ress = StringMap.find rname m_arr_ress in
        arr_ress.(phase_val + k*per) <- arr_ress.(phase_val + k*per) + rval
      ) lress
    ) done
  ) lwcet;

  (* Printing out the infos *)
  let ocout = open_out !Compiler_options.wcet_balance_info_filename in
  let ffout = formatter_of_out_channel ocout in

  fprintf ffout "*** Load balancing infos ***\n@?";
  fprintf ffout "*** WCET ***\n@?";
  Array.iteri (fun i wcet -> 
    fprintf ffout "\tPhase %i => %i\n@?" i wcet
  ) arr_wcet;
  fprintf ffout "\n*** RESSOURCES ***\n@?";
  StringMap.iter (fun rname arr_res ->
    fprintf ffout "* Ressource: %s\n" rname;
    Array.iteri (fun i rval -> 
      fprintf ffout "\tPhase %i => %i\n@?" i rval
    ) arr_res
  ) m_arr_ress

(* ==================================================== *)

(* Main flow functions *)
type v_constr_type =
  | Default
  | Load_Balancing_Int
  | Load_Balancing_Bin

let get_version_constraint _ = match !Compiler_options.v_constr with
  | 0 -> Default
  | 1 -> Load_Balancing_Int
  | 2 -> Load_Balancing_Bin
  | _ -> failwith "Unrecognized constraints version."

(* Get the period associated which each phase variable,
  before the preprocessing scramble the upper bounds *)
let get_period_info lbc =
  List.fold_left (fun macc bc ->
    assert(bc.lbound=0);
    StringMap.add bc.varName bc.ubound macc
  ) StringMap.empty lbc


(* Preprocessing of the constraints *)
let preprocess_constraints lcst =
  let (lac, lbc) = lcst in

  (* DEBUG *)
  if (debug) then (
    fprintf ffout "Affine constraints:\n%a\n@?" print_list_aff_constr lac;
    fprintf ffout "Boundary constraints:\n%a\n@?" print_list_bound_constr lbc
  );

  (* We transfer the 1-term affine constraints to the boundary constraints *)
  let (lac, lbc) = transfer_1term_ac_to_bc lbc lac in

  (* We remove the affine constraints already satified by the boundary constraints *)
  let lac = List.fold_left (fun lac_acc ac -> 
    if (ac.isEq) then ac::lac_acc else  (* Equality constraint => we do not touch it *)
    let (kmin,_) = get_min_max_affterm lbc None ac.lcoeffVar (-ac.cst) in
    if (kmin>=0) then (
      (* DEBUG
      fprintf ffout "\t~> Removed constraint: %a\n@?" print_aff_constr ac; *)
      lac_acc  (* Constraint is already trivialy satisfied by the boundaries condition *)
    ) else
      ac::lac_acc
  ) [] lac in

  let (lac, lbc) = manage_equalities lbc lac in

  (* DEBUG *)
  if (debug) then (
    fprintf ffout "Affine constraints (after 1term elim):\n%a\n@?" print_list_aff_constr lac;
    fprintf ffout "Boundary constraints (after 1term elim):\n%a\n@?" print_list_bound_constr lbc
  );
  (lac, lbc)


(* Default Solution: get the minimum for all boundconstr *)
(* Note: cover all phase variable, because the system was normalized beforehand *)
let get_lower_bound_solution lbc =
  let msol = List.fold_left (fun msol bc ->
    StringMap.add bc.varName bc.lbound msol
  ) StringMap.empty lbc in

  (* DEBUG *)
  if (debug) then
    fprintf ffout "Solution found:\n%a\n@?" print_msol msol;

  msol


(* Solve the system of affine and boundary constraints.
  Returns a StringMap, associating the variable name to its value *)
let solve_constraints_main bquickres
  (lwcet : (string option * (int * string) list * int * int * (int option) * (string * int) list) list)
  (lcst : (affconstr list) * (boundconstr list))
  (b_no_underspec_ops:bool) =

  let (lac, lbc) = lcst in
  let mperiods = get_period_info lbc in

  let (lac, lbc) = preprocess_constraints lcst in

  (* Needs to be there, because of model2node transformation *)
  if (bquickres) then (
    assert(lac=[]);
    get_lower_bound_solution lbc
  ) else

  let version_constr = get_version_constraint () in
  let (lac, lbc, lgeneral, linteger, lbinary, obj_func, mmbinary) = match version_constr with
    | Default ->
      (* No cost function - default option *)
      let vname = (List.hd lbc).varName in
      let (obj_func:affterm) = (1, vname)::[] in
      let lgeneral = [] in
      let linteger = List.map (fun bc -> bc.varName) lbc in
      let lbinary = [] in
      let dummy_mmbinary = StringMap.empty in
      (lac, lbc, lgeneral, linteger, lbinary, obj_func, dummy_mmbinary)
    | Load_Balancing_Int ->
      load_balancing false b_no_underspec_ops mperiods lwcet lac lbc
    | Load_Balancing_Bin ->
      load_balancing true b_no_underspec_ops mperiods lwcet lac lbc
  in

  (* Case where we want the WCET of all phase to be smaller than a constant *)
  let (lac, lgeneral, obj_func) = if ((!Compiler_options.fixed_wcet_ub != 0)
      && ((version_constr=Load_Balancing_Int) || (version_constr=Load_Balancing_Bin)) ) then
    let nac = mk_affconstr true [(1,varobj)] !Compiler_options.fixed_wcet_ub in
    let var_random = (List.hd lbc).varName in
    (nac::lac, [], [(1, var_random)])
  else
    (lac, lgeneral, obj_func)
  in


  (* Base case - no affine constraint - simplest resolution *)
  (* Happens when there are no buffer operator used in the program *)
  let no_ressource_used = List.exists (fun (_,_,_,_,_,lress) -> lress!=[]) lwcet in
  let no_underspec_ops = b_no_underspec_ops in
  if (lac = [] && (version_constr=Default) && no_ressource_used && no_underspec_ops) then
    get_lower_bound_solution lbc
  else

  (* Export of constraints and import of solution *)
  (* Option: -genphconstr [file_name]   and   -solphconstr [file] *)
  if (!Compiler_options.generate_constraint_file) then
    generate_constraint lac lbc lgeneral linteger lbinary obj_func
  else

  if (!Compiler_options.parse_solution_file) then (
    let msol = parse_solution lac lbc lbinary in

    let msol = if (version_constr=Load_Balancing_Bin) then
      recover_integral_var mmbinary msol
    else msol in

    (* If option enabled, we print the balance of WCET/ressource usage
      across all phases here *)
    (* lwcet : (potential phase_variable_name, list of affine terms, shift of ock, period of ock,
                    potential assigned WCET, list of ressources used *)
    if (!Compiler_options.b_print_wcet_balance) then
      print_wcet_balance lwcet msol;

    msol
  ) else

  (* We do our own resolution - Note: only on limited options when ND *)
  if (version_constr!=Default || (not no_underspec_ops)) then
    failwith ("Internal constraint resolution algorithm is limited. "
        ^ "Please use the -genphconstr options and an external ILP solver.")
  else

  (* Note: no objective function managed here - TODO: check that and issue a warning if option *)
  let msol = solve_constraint_on_our_own lac lbc in

  (* DEBUG *)
  if (debug) then
    fprintf ffout "Solution found:\n%a\n@?" print_msol msol;

  msol


