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

(* Author: Guillaume I. *)
(* This file was also written as training to familiarize myself with the compiler, thus the numerous comments *)
(* It is slightly redundant with mls_printer with the option "Compiler_option.full_type_info", but not completely *)

open Misc				(* Various things, including "optional", name management, list manipulation, iterators,
							size checks, ...  / in "compiler/utilites" *)
open Names				(* management of modules and object names / in "compiler/global" *)
open Linearity			(* manage "linearity" type / in "compiler/global" *)

open Format				(* OCaml module - contain in particular "fprintf" *)
						(* Cf page 417 of the OCaml manual for a description of the formating of "fprintf" *)

open Global_printer		(* Utilitaries about printing some globally defined types / in "compiler/global" *)
open Pp_tools			(* Utilitaries about pretty printing / in "compiler/utilities" *)
open Minils				(* Definition of the AST + constructors / in "compiler/minils" *)

(* This file contains an alternate pretty-printer for miniLS programs
	 which is showing the whole AST (constructors included) *)



(*********************************)
(* *** Base level of the AST *** *)
(*********************************)

(* Variant of the print_linearity function to force it to print, even if its value is "T" *)
let print_linearity_full ff linearity = fprintf ff " %s" (lin_to_string linearity)


(* print_extvalue *)
let rec print_extvalue_desc ff extvaldesc = match extvaldesc with
  | Wconst st_exp -> print_static_exp ff st_exp
  | Wvar var_id -> print_ident ff var_id
  | Wfield (extval, fname) -> fprintf ff "%a.%a" print_extvalue extval print_qualname fname
  | Wwhen (extval, constrname, var_id) -> fprintf ff "@[<2>(%a@ when %a(%a))@]"
       print_extvalue extval print_qualname constrname print_ident var_id
  | Wreinit (extval1, extval2) ->
      fprintf ff "@[reinit@,(%a, %a)@]" print_extvalue extval1  print_extvalue extval2

and print_extvalue ff extval =
  fprintf ff "(%a : %a%a :: %a)" print_extvalue_desc extval.w_desc
      print_type extval.w_ty
      print_linearity_full extval.w_linearity
      print_ck extval.w_ck

(* iterator_type *)
let iterator_to_string i =
  match i with
    | Imap -> "map"
    | Imapi -> "mapi"
    | Ifold -> "fold"
    | Ifoldi -> "foldi"
    | Imapfold -> "mapfold"


(*************************************)
(* *** Equation level of the AST *** *)
(*************************************)


let print_params ff l =
  fprintf ff "@[<2>%a@]" (print_list_r print_static_exp "<<"","">>") l


let print_index ff idx =
  fprintf ff "@[<2>%a@]" (print_list print_static_exp "[""][""]") idx

let print_dyn_index ff idx =
  fprintf ff "@[<2>%a@]" (print_list print_extvalue "[""][""]") idx

let print_trunc_index ff idx =
  fprintf ff "@[<2>%a@]" (print_list print_extvalue "[>""<][>""<]") idx


let print_w_tuple ff l = fprintf ff "@[<2>(%a)@]" (print_list_r print_extvalue """,""") l

let print_every ff reset = print_opt (fun ff id -> fprintf ff " every %a" print_ident id) ff reset

let print_handler ff c =
  fprintf ff "@[<2>%a@]" (print_couple print_qualname print_extvalue "("" -> "")") c

let print_tag_w_list ff tag_w_list =
  fprintf ff "@[%a@]" (print_list print_handler "" "" "") tag_w_list


(* Expressions *)
let rec print_exp ff {e_desc = edesc;
       e_level_ck = level_ck;
       e_ct = ct;
       e_ty = typ;
       e_linearity = lin} =
   fprintf ff "(%a : %a%a :: %a (%a))"
      print_exp_desc edesc
      print_type typ
      print_linearity lin
      print_ct ct
      print_ck level_ck
and print_exp_desc ff edesc = match edesc with
  | Eextvalue w -> print_extvalue ff w
  | Efby ((Some c), w) -> fprintf ff "@[<2>%a fby@ %a@]" print_static_exp c print_extvalue w
  | Efby (None, w) -> fprintf ff "pre %a" print_extvalue w
  | Eapp (app, args, reset) ->
      fprintf ff "@[<2>%a@,%a@]" print_app (app, args) print_every reset
  | Emerge (x, tag_w_list) ->
      fprintf ff "@[<2>merge %a@ %a@]" print_ident x print_tag_w_list tag_w_list
  | Ewhen (e,c,x) ->
      fprintf ff "@[<2>(%a@ when %a(%a))@]" print_exp e print_qualname c print_ident x
  | Estruct f_w_list ->
      print_record (print_couple print_qualname print_extvalue """ = """) ff f_w_list
  | Eiterator (it, f, params, pargs, args, reset) ->
      fprintf ff "@[<2>(%s (%a)<<%a>>)@,(%a)%a@]%a"
        (iterator_to_string it)
        print_app (f, [])
        (print_list_r print_static_exp """, """) params
        print_w_tuple pargs
        print_w_tuple args
        print_every reset


and print_cl_option ff clopt =
  fprintf ff "[gl_worksize = %i | loc_worksize = %i ]"
    clopt.copt_gl_worksize  clopt.copt_loc_worksize

and print_app ff (app, args) =
  (match app.a_op with
    | Eequal ->
      let e1, e2 = assert_2 args in
        fprintf ff "@[<2>%a@ = %a@]" print_extvalue e1  print_extvalue e2
    | Efun ({ qual = Pervasives; name = n } as f) when (is_infix n) ->
	begin match args with
	  [a1;a2] ->
	    fprintf ff "@[(%a@, %s@, %a)@]"
	      print_extvalue a1
	      n
	      print_extvalue a2
	| _ ->
            fprintf ff "@[%a@,%a@,%a@]"
              print_qualname f print_params app.a_params  print_w_tuple args
	end
    | Efun f | Enode f ->
        fprintf ff "@[%a@,%a@,%a@]"
          print_qualname f print_params app.a_params  print_w_tuple args
    | Eifthenelse ->
      let e1, e2, e3 = assert_3 args in
        fprintf ff "@[<hv>if %a@ then %a@ else %a@]"
          print_extvalue e1 print_extvalue e2 print_extvalue e3
    | Efield_update ->
      let r,e = assert_2 args in
      let f = assert_1 app.a_params in
        fprintf ff "@[<2>{%a with .%a =@ %a}@]"
          print_extvalue r print_static_exp f print_extvalue e
    | Earray -> fprintf ff "@[<2>%a@]" (print_list_r print_extvalue "["";""]") args
    | Earray_fill ->
      let e = assert_1 args in
      let n_list = app.a_params in
        fprintf ff "%a@[<2>%a@]" print_extvalue e (print_list print_static_exp "^""^""") n_list
    | Eselect ->
      let e = assert_1 args in
        fprintf ff "%a%a" print_extvalue e print_index app.a_params
    | Eselect_slice ->
      let e = assert_1 args in
      let idx1, idx2 = assert_2 app.a_params in
        fprintf ff "%a[%a..%a]"
          print_extvalue e  print_static_exp idx1  print_static_exp idx2
    | Eselect_dyn ->
      let r, d, e = assert_2min args in
        fprintf ff "%a%a default %a"
          print_extvalue r  print_dyn_index e  print_extvalue d
    | Eselect_trunc ->
      let e, idx_list = assert_1min args in
        fprintf ff "%a%a" print_extvalue e print_trunc_index idx_list
    | Eupdate ->
      let e1, e2, idx = assert_2min args in
          fprintf ff "@[<2>(%a with %a =@ %a)@]"
            print_extvalue e1 print_dyn_index idx print_extvalue e2
    | Econcat ->
      let e1, e2 = assert_2 args in
        fprintf ff "@[<2>%a@ @@ %a@]" print_extvalue e1  print_extvalue e2
  );
  match app.a_cloption with
  | None -> ()
  | Some clopt -> print_cl_option ff clopt


(* lhs of equations *)
let rec print_pat ff pat = match pat with
  | Evarpat n -> print_ident ff n
  | Etuplepat pat_list ->
      fprintf ff "@[<2>(%a)@]" (print_list_r print_pat "" "," "") pat_list


let print_eq ff {eq_lhs = lhs;
       eq_rhs = rhs;
       eq_unsafe = unsafe;
       eq_base_ck = base_ck} =
  fprintf ff "@[<2>%a :: %a (unsafe: %b)=@ %a@]"
    print_pat lhs  print_ck base_ck  unsafe  print_exp rhs

let print_eqs ff leqs =
  fprintf ff "@[<v2>@ %a@]" (print_list_r print_eq "" ";" "") leqs

(******************************)
(* *** Parallel scheduler *** *)
(******************************)

let print_parsched_comp ff psch_comp = match psch_comp with
  | Comp_eq eq ->
    fprintf ff "Comp_eq(%a)" print_eq eq
  | Comp_ocl_launch (eq, ndev) ->
    fprintf ff "Comp_ocl_launch(%s, %a)" ndev print_eq eq
  | Comp_ocl_recover (eq, ndev) ->
    fprintf ff "Comp_ocl_recover(%s, %a)" ndev print_eq eq
  | Comp_signal signame ->
    fprintf ff "Comp_signal(%s)" signame
  | Comp_wait (signame, n) ->
    fprintf ff "Comp_wait(%s, %i)" signame n

let print_parsched_eqs ff psch_eqs =
  List.iteri (fun k lcomp ->
    fprintf ff "=> Core_%i:\n@?" k;
    List.iter (fun comp ->
      fprintf ff "\t- %a\n@?" print_parsched_comp comp
    ) lcomp
  ) psch_eqs


let print_parsched_info ff psch_info =
  fprintf ff "[ncore = %i | ndevice = %i]\n@?"
    psch_info.psch_ncore psch_info.psch_ndevice;
  fprintf ff "%a" print_parsched_eqs psch_info.psch_eqs



(*********************************)
(* *** Node level of the AST *** *)
(*********************************)


(* Node parameters *)
let print_node_params ff params =
  fprintf ff "@[<2>%a@]" (print_list_r print_param "<<" "," ">>") params


(* Constraints on parameters *)
let print_constrnt_list ff lparam_constraints =
  fprintf ff "@[<v1>%a@]" (print_list_r print_constrnt "(" ";" ")") lparam_constraints


(* Variable declaration *)
let print_vardecl ff { v_ident = n; v_type = ty; v_linearity = lin; v_clock = ck } =
  fprintf ff "%a : %a%a :: %a" print_ident n print_type ty print_linearity_full lin print_ck ck


let print_vardecl_tuple ff lvardecl =
  fprintf ff "@[<v1>%a@]" (print_list_r print_vardecl "(" ";" ")") lvardecl


(* Contract *)
let print_objective_kind ff okind = match okind with
  | Obj_enforce -> fprintf ff "Obj_enforce"
  | Obj_reachable -> fprintf ff "Obj_reachable"
  | Obj_attractive -> fprintf ff "Obj_attractive"

let print_objective ff {o_kind = kind; o_exp = exp} =
  fprintf ff "%a %a\n" print_objective_kind kind print_extvalue exp

let print_contract ff {c_assume = assume;
       c_objectives = lobjectives;
       c_assume_loc = assume_loc;
       c_enforce_loc = enforce_loc;
       c_controllables = lcontrollables;
       c_local = llocal;
       c_eq = leq} =
  fprintf ff "@[<v4>@ * assume = %a\n\
        objectives =\n@[<2>%a@]@\n\
        assume_loc = %a\n\
        enforce_loc = %a\n\
        controllables =\n@[<2>%a@]@\n\
        local =\n@[<2>%a@]@\n\
        eq =\n@[<2>%a@]@]@\n" print_extvalue assume
           (print_list print_objective "@ " "@ " "") lobjectives
           print_extvalue assume_loc
           print_extvalue enforce_loc
           print_vardecl_tuple lcontrollables
           print_vardecl_tuple llocal
           print_eqs leq


(* Memory allocation *)
let print_list_nocut print lp sep rp ff = function
  | [] -> ()
  | x :: l ->
      fprintf ff "%s%a" lp print x;
      List.iter (fprintf ff "%s %a" sep print) l;
      fprintf ff "%s" rp

let print_memalloc ff memalloc = 
  let (t,interf_var) = memalloc in
  fprintf ff "[type: %a | ivar: %a]" print_type t (print_list_nocut Interference_graph.print_ivar "(" "," ")") interf_var

let print_mem_alloc ff lmem_alloc =
  fprintf ff "@[<v2>@ %a@]" (print_list_l print_memalloc "" "| " "") lmem_alloc


let print_typeparam ff tp =
  fprintf ff "%a of %a"
    print_full_qualname tp.t_nametype
    print_full_qualname tp.t_nameclass

let print_type_param_dec ff ltypeparams =
  fprintf ff "@[<v2>@ %a@]" (print_list_l print_typeparam "" "| " "") ltypeparams

(* Node *)
let print_node ff {n_name = name;
       n_stateful = stateful;
       n_unsafe = unsafe;
       n_typeparams = ltypeparams;
       n_input = linput;
       n_output = loutput;
       n_contract = optcontract;
       n_local = llocal;
       n_equs = leq;
       n_params = lparams;
       n_param_constraints = lparam_constraints;
       n_mem_alloc = lmem_alloc} =
  fprintf ff "@[<v2>node %a (stateful: %b | unsafe: %b)@\n\
  		params = %a@\n\
  		param_constraints = %a@\n\
  		typeparams = %a@\n\
  		inputs  = %a@\n\
  		outputs = %a@\n\
  		locals  = %a@\n\
  		contract =@[<2>%a@]@\n\
  		equations =@[<2>%a@]@\n\
  		mem alloc =@[<2>%a@]@\n\
  		@]@\n@." print_full_qualname name stateful unsafe
  		   print_node_params lparams
  		   print_type_param_dec ltypeparams
  		   print_constrnt_list lparam_constraints
           print_vardecl_tuple linput
           print_vardecl_tuple loutput
           print_vardecl_tuple llocal
           (print_opt print_contract) optcontract
           print_eqs leq
           print_mem_alloc lmem_alloc


(************************************************)
(* *** Program description level of the AST *** *)
(************************************************)
(* Static constant declaration *)
let print_const_dec ff cdecl =
  let {c_name = name; c_type = typ; c_value = vopt} = cdecl in
  match vopt with
    | None -> fprintf ff "@[const %a (type: %a)@]@\n@."
          print_full_qualname name  print_type typ
    | Some value ->
      fprintf ff "@[const %a (type: %a)@ = %a@]@\n@."
          print_full_qualname name  print_type typ  print_static_exp value


(* Type declaration *)
let print_tdesc ff desc = match desc with
  | Type_abs -> fprintf ff "Type_abs"
  | Type_alias t -> fprintf ff "(Type_alias@ %a)" print_type t
  | Type_enum lconstname -> fprintf ff "(Type_enum@ %a)" (print_list print_qualname "" "|" "") lconstname
  | Type_struct struc -> fprintf ff "(Type_struct@ %a)" (print_record print_field) struc


let print_type_dec ff tdecl =
  let {t_name = name; t_desc = desc} = tdecl in
  fprintf ff "@[type %a :@ %a@]@\n@." print_full_qualname name   print_tdesc desc


let print_classtype_dec ff cdecl =
  fprintf ff "@[class %a (%a)@]@\n@." print_full_qualname cdecl.c_nameclass
    (print_list print_full_qualname "" ", " "") cdecl.c_insttypes


let print_vardecl_loc_kernel ff vd = fprintf ff "__cllocal %a" print_vardecl vd

let print_kernel_dec ff
    { k_namekernel = n; k_input = ki; k_output = ko;
    k_issource = issrc; k_srcbin = filename; k_dim = dim;
    k_local = kl} =
  fprintf ff "@[__clkernel fun %a%a returns %a@]\n@."
    print_qualname n
    print_vardecl_tuple ki
    print_vardecl_tuple ko;
  (if issrc then
    fprintf ff "\t__clsource \"%s\" __cldim %i\n@." filename dim
  else
    fprintf ff "\t__clbinary \"%s\" __cldim %i\n@." filename dim);
  if (kl != []) then
    fprintf ff "\t%a\n@."
    (print_list print_vardecl_loc_kernel "" " " "") kl



(************************************)
(* *** Program level of the AST *** *)
(************************************)

let print_open_module ff name = fprintf ff "@[<2>* %s@]@." (modul_to_string name)

let printAST_program oc prog =
  let print_program_desc ff pdesc = match pdesc with
    | Pnode ndecl -> print_node ff ndecl
    | Pconst cdecl -> print_const_dec ff cdecl
    | Ptype tdecl -> print_type_dec ff tdecl
    | Pclasstype cdecl -> print_classtype_dec ff cdecl
    | Pkernel kdecl -> print_kernel_dec ff kdecl
  in
  let {p_modname=modname; p_format_version=format_version;
       p_opened=lopened; p_desc = ldesc} = prog in
  let ff = formatter_of_out_channel oc in
  
  let old_full_type_info = !Compiler_options.full_type_info in (* print the type with the static expr *)
  Compiler_options.full_type_info := true;
  
  fprintf ff "@[Modname = %s@]@." (modul_to_string modname);
  fprintf ff "@[Format version = %s@]@." format_version;

  fprintf ff "@[Opened modules =@]@.";
  List.iter (print_open_module ff) lopened;

  fprintf ff "@[--- Program description ---@]@.";
  List.iter (print_program_desc ff) ldesc;
  fprintf ff "@?";			(* Flush the buffer at the very end *)
  Compiler_options.full_type_info := old_full_type_info
