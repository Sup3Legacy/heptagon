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
let debug = false
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

let print_list_binary ff lbinary =
  List.iter (fun v -> fprintf ff "\t%s\n@?" v) lbinary


(* Print-out constraints using the CPLEX LP format (cf glpk doc, Appendix C) *)
let print_out_cplex_constraint ff obj_func lac lbc lbinary =
  fprintf ff "Minimize\n@?";
  print_affterm_multilines ~bfirst:true num_elem_max_per_line ff obj_func;
  fprintf ff "Subject To\n@?";
  print_list_aff_constr ff lac;
  fprintf ff "Bounds\n@?";
  print_list_bound_constr ff lbc;
  if (lbinary!=[]) then begin
    fprintf ff "Binary\n@?";
    print_list_binary ff lbinary;
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

(* Constraint manipulation*)

(* Add a term of an affine term, in order to maintain the "max 1 term per variable" property *)
let rec add_term (a,v) affterm = match affterm with
  | [] -> (a,v)::[]
  | (at,vt)::rt ->
    if (vt=v) then (at+a,v)::rt else
    (at,vt)::(add_term (a,v) rt)

(* Substitution inside a constraint *)
let subst_constraint (var, optphid2, sh) constr =
  let rec subst_constraint_aux (var, optphid2, sh) affterm = match affterm with
    | [] -> ([],0)
    | (a,v)::r ->
      let (nr, shcst) = subst_constraint_aux (var, optphid2, sh) r in
      if (v=var) then (
        let nshcst = shcst - a*sh in  (* constant is in the other side of the (in)equality *)
        match optphid2 with
        | None -> (nr, nshcst)
        | Some var2 -> ((add_term (a,var2) nr), nshcst)
      )
      else
        ((a,v)::nr,shcst)
  in
  let (lcoeffVar, shcst) = subst_constraint_aux (var, optphid2, sh) constr.lcoeffVar in
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
      assert(0>=affconstr.cst);
      (lac_acc, lbc_acc)
    ) else (
      assert((List.length affconstr.lcoeffVar)=1);
      let (c,v) = List.hd affconstr.lcoeffVar in
      let lbc_acc = if (c=1) then
          update_bound_constraints true v affconstr.cst lbc_acc
        else if (c=(-1)) then
          update_bound_constraints false v (- affconstr.cst) lbc_acc
        else
          failwith "Coefficient in from of variable not a 1 or a (-1)."
      in
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
    let intk = get_phase_index_from_varname strk in
    IntMap.add intk v imap
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

let default_obj_func lbc =
 let vname = (List.hd lbc).varName in
 (1, vname)::[]

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

(* Solve the system of affine and boundary constraints.
  Returns a StringMap, associating the variable name to its value *)
let solve_constraints_main (lcst : (affconstr list) * (boundconstr list)) =
  let (lac, lbc) = lcst in

  (* DEBUG *)
  if (debug) then (
    fprintf ffout "Affine constraints:\n%a\n@?" print_list_aff_constr lac;
    fprintf ffout "Boundary constraints:\n%a\n@?" print_list_bound_constr lbc
  );

  (* We transfer the 1-term affine constraints to the boundary constraints *)
  let (lac, lbc) = transfer_1term_ac_to_bc lbc lac in

  (* DEBUG *)
  if (debug) then (
    fprintf ffout "Affine constraints (after 1term elim):\n%a\n@?" print_list_aff_constr lac;
    fprintf ffout "Boundary constraints (after 1term elim):\n%a\n@?" print_list_bound_constr lbc
  );

  (* Base case - no affine constraint (aka, no buffer operator) *)
  if (lac = []) then
    (* Default Solution: get the minimum for all boundconstr *)
    (* Note: cover all phase variable, because the system was normalized beforehand *)
    let msol = List.fold_left (fun msol bc ->
      StringMap.add bc.varName bc.lbound msol
    ) StringMap.empty lbc in

    (* DEBUG *)
    if (debug) then
      fprintf ffout "Solution found:\n%a\n@?" print_msol msol;

    msol
  else

  (* TODO: objective function management (cf WCET extension)  *)
  (* Add compiler option "-ldb" for load balancing obj function, with WCETs: no objective function *)
  (* Default: no objective function *)
  let (obj_func:affterm) = default_obj_func lbc in (* No cost function*)
  let lbinary = [] in

  (* TODO: if varation of the constraints, put it here *)
  

  (* Generate a constraint file, then stop the compilation flow *)
  (* Option: -genphconstr [file_name] *)
  if (!Compiler_options.generate_constraint_file) then
    let ocout = open_out !Compiler_options.constraint_filename in
    let ffout = formatter_of_out_channel ocout in
    print_out_cplex_constraint ffout obj_func lac lbc lbinary;
    close_out ocout;

    (* === Stopping compiler flow now === *)
    failwith "Constraint file generation successfully done - compilation flow terminated."
  else


  let msol = if (!Compiler_options.parse_solution_file) then
    (* Option: -solphconstr [file] *)
    (* Solution file is a serie of lines "[namevar] => [integral value]"*)
    let lsol = parse_file (Parser_sol.solution Lexer_sol.main)
                    !Compiler_options.solution_filename in
    let msol = List.fold_left (fun macc (k,v) ->
      StringMap.add k v macc
    ) StringMap.empty lsol in

    check_coherency lac lbc lbinary msol;
    msol
  else (
    (* We do our own resolution - Note: only on limited options when ND *)
    if (lbinary!=[]) then
      failwith ("Internal constraint resolution algorithm is "
          ^ "limited - please use an external tool.");

    (* Note: no objective function managed here - TODO: check that and issue a warning if option *)
    solve_constraint_on_our_own lac lbc
  ) in

  (* DEBUG *)
  if (debug) then
    fprintf ffout "Solution found:\n%a\n@?" print_msol msol;

  msol
