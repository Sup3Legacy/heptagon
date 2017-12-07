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

(* Pretty-printer for the AST of "hept_parsetree.ml" *)

open Format                 (* OCaml module *)

open Names
open Linearity
open Pp_tools
open Hept_parsetree         (* The AST for which this "pretty"-printer is for*)

let print_dec_name ff dec_name = fprintf ff "%s" dec_name
let print_var_name ff var_name = fprintf ff "%s" var_name
let print_state_name ff state_name = fprintf ff "%s" state_name
let print_type_name ff type_name = fprintf ff "%s" type_name
let print_class_name ff class_name = fprintf ff "%s" class_name


(* Qualified name *)
let print_qualname ff qname = match qname with
  | Q nqname -> fprintf ff "(Q %s)" (Names.fullname nqname)
  | ToQ nname -> fprintf ff "(ToQ %s)" nname

let print_const_name ff const_name = print_qualname ff const_name
let print_field_name ff field_name = print_qualname ff field_name
let print_fun_name ff fun_name = print_qualname ff fun_name

let rec print_pat ff pat = match pat with
  | Etuplepat lpat -> fprintf ff "Etuplepat %a" (print_list print_pat """,""") lpat
  | Evarpat vname -> fprintf ff "Evarpat %a" print_var_name vname

(* Clocks *)
let rec print_ck ff ck = match ck with
  | Cbase -> fprintf ff "Cbase"
  | Con (ck, constname, varname) -> fprintf ff "Con (%a, %a, %a)" print_ck ck
    print_const_name constname  print_var_name varname

let rec print_ct ff ct = match ct with
  | Ck ck -> fprintf ff "Ck %a" print_ck ck
  | Cprod lct -> fprintf ff "Cprod %a" (print_list print_ct "(" ", " ")") lct


(* Static expressions *)
let rec print_static_exp_desc ff sedesc = match sedesc with
  | Svar const_name -> fprintf ff "Svar %a" print_const_name const_name
  | Sint i -> fprintf ff "Sint %d" i
  | Sfloat f -> fprintf ff "Sfloat %f" f
  | Sbool b -> if (b) then fprintf ff "Sbool true" else fprintf ff "Sbool false"
  | Sstring str -> fprintf ff "Sstring %s" str
  | Sconstructor const_name -> fprintf ff "Sconstructor %a" print_const_name const_name
  | Sfield field_name -> fprintf ff "Sfield %a" print_field_name field_name
  | Stuple lstexp -> fprintf ff "Stuple %a" (print_list print_static_exp "(" ", " ")") lstexp
  | Sarray_power (stexp, lpower) -> fprintf ff "Sarray_power %a %a" print_static_exp stexp
       (print_list print_static_exp "(" ", " ")") lpower
  | Sarray lstexp -> fprintf ff "Sarray %a" (print_list print_static_exp "(" ", " ")") lstexp
  | Srecord lfname_stexp -> fprintf ff "Srecord %a"
      (print_list (print_couple print_field_name print_static_exp "" "=" "") "(" ", " ")") lfname_stexp
  | Sop (f_name,lstexp) -> fprintf ff "Sop %a %a" print_fun_name f_name
      (print_list print_static_exp "(" ", " ")") lstexp

and print_static_exp ff { se_desc = sedesc } =
  print_static_exp_desc ff sedesc


(* Iterators type *)
let print_iterator_type ff it_type = match it_type with
  | Imap -> fprintf ff "Imap"
  | Imapi -> fprintf ff "Imapi"
  | Ifold -> fprintf ff "Ifold"
  | Ifoldi -> fprintf ff "Ifoldi"
  | Imapfold -> fprintf ff "Imapfold"


(* Expressions *)
let print_op ff op = match op with
  | Etuple -> fprintf ff "Etuple"
  | Enode qname -> fprintf ff "Enode %a" print_qualname qname
  | Efun qname -> fprintf ff "Efun %a" print_qualname qname
  | Eifthenelse -> fprintf ff "Eifthenelse"
  | Earrow -> fprintf ff "Earrow"
  | Efield -> fprintf ff "Efield"
  | Efield_update -> fprintf ff "Efield_update"
  | Earray -> fprintf ff "Earray"
  | Earray_fill -> fprintf ff "Earray_fill"
  | Eselect -> fprintf ff "Eselect"
  | Eselect_dyn -> fprintf ff "Eselect_dyn"
  | Eselect_trunc -> fprintf ff "Eselect_trunc"
  | Eselect_slice -> fprintf ff "Eselect_slice"
  | Eupdate -> fprintf ff "Eupdate"
  | Econcat -> fprintf ff "Econcat"
  | Ereinit -> fprintf ff "Ereinit"

let rec print_app ff { a_op = op; a_params = lexp; a_inlined = binl} =
  fprintf ff "%a%a [inlined:%b]" print_op op
     (print_list print_exp "(" "," ")") lexp
     binl

and print_edesc ff edesc = match edesc with
  | Econst st_exp -> fprintf ff "Econst %a" print_static_exp st_exp
  | Evar varname -> fprintf ff "Evar %a" print_var_name varname
  | Elast varname -> fprintf ff "Elast %a" print_var_name varname
  | Epre (oexp, exp) -> fprintf ff "Epre %a%a" (print_opt print_exp) oexp  print_exp exp
  | Efby (exp1, exp2) -> fprintf ff "Efby %a %a" print_exp exp1 print_exp exp2
  | Estruct lqnameexp -> fprintf ff "%a" (print_list
      (print_couple print_qualname print_exp "" ":" "") "(" ", " ")") lqnameexp
  | Eapp (ap,lexp) -> fprintf ff "Eapp %a %a" print_app ap
      (print_list print_exp "(" "," ")") lexp
  | Eiterator (it_type, app, lexp1, lexp2, lexp3) ->
     fprintf ff "Eiterator %a %a (%a,%a,%a)"
       print_iterator_type it_type
       print_app app
       (print_list print_exp "("","")") lexp1
       (print_list print_exp "("","")") lexp2
       (print_list print_exp "("","")") lexp3
  | Ewhen (exp, cons_name, var_name) -> fprintf ff "Ewhen %a%a%a" print_exp exp
      print_const_name cons_name  print_var_name var_name
  | Emerge (var_name, lconstname_exp) -> fprintf ff "Emerge %a%a" print_var_name var_name
     (print_list (print_couple print_const_name print_exp "" "|" "") "" "," "") lconstname_exp
  | Ecurrent (cons_name, var_name, expInit, exp) -> fprintf ff "Ecurrent(%a(%a), %a, %a)"
      print_const_name cons_name  print_var_name var_name  print_exp expInit  print_exp expr
  Ebuffer (c1, ce1, c2, ce2, eInit, e) -> fprintf ff "Ebuffer(%a(%a), %a(%a), %a, %a)"
      print_const_name c1  print_var_name ce1
      print_const_name c2  print_var_name ce2
      print_exp eInit  print_exp e
  | Esplit (var_name, exp) -> fprintf ff "Esplit %a%a" print_var_name var_name print_exp exp

and print_exp ff { e_desc= edesc; e_ct_annot= optct } =
  fprintf ff "%a (%a)" print_edesc edesc (print_opt print_ct) optct


(* Types *)
let rec print_type ff typ = match typ with
  | Tprod ltyp -> fprintf ff "Tprod %a" (print_list print_type "(" ", " ")") ltyp
  | Tid qname -> fprintf ff "Tid %a" print_qualname qname
  | Tarray (typ,exp) -> fprintf ff "Tarray %a^(%a)" print_type typ print_exp exp
  | Tinvalid -> fprintf ff "Tinvalid"


(* Automata and equations *)
let print_last ff lst = match lst with
  | Var -> fprintf ff "Var"
  | Last oexp -> fprintf ff "Last %a" (print_opt print_exp) oexp


let rec print_var_dec ff {v_name=vname; v_type=typ; v_linearity=lin; v_clock=clk; v_last=lst} =
  fprintf ff "%a::(%a) (lin:%a |cl:%a |last:%a)"
    print_var_name vname
    print_type typ
    print_linearity lin
    (print_opt print_ck) clk
    print_last lst

and print_present_handler ff {p_cond= cond; p_block=bl} = 
  fprintf ff "%a%a" print_exp cond  print_block bl

and print_switch_handler ff {w_name=consname; w_block=bl } =
  fprintf ff "%a(%a)" print_const_name consname print_block bl

and print_escape ff {e_cond = cond; e_reset=bres; e_next_state=nxtstate } =
  fprintf ff "%a (reset:%b |next:%a)" print_exp cond  bres  print_state_name nxtstate

and print_state_handler ff {s_state=stname; s_block=bl; s_until=lesc_until; s_unless=lesc_unless} =
  fprintf ff "%a%a(until: %a@ unless: %a)"
    print_state_name stname
    print_block bl
    (print_list print_escape "(" "," ")") lesc_until
    (print_list print_escape "(" "," ")") lesc_unless

and print_block ff {b_local=lvardec; b_equs=leq} =
  fprintf ff "%a@\n%a" (print_list print_var_dec "(" "," ")") lvardec
     (print_list print_eq "(" "," ")") leq

and print_eqdesc ff eqd = match eqd with
  | Eautomaton lsthand -> fprintf ff "Eautomaton %a"
     (print_list print_state_handler "(" "," ")") lsthand
  | Eswitch (exp, lsthand) -> fprintf ff "Eswitch %a%a"
     print_exp exp (print_list print_switch_handler "(" "," ")") lsthand
  | Epresent (lprhand, block) -> fprintf ff "Epresent %a%a"
     (print_list print_present_handler "(" "," ")") lprhand print_block block
  | Ereset (bl, exp) -> fprintf ff "Ereset %a%a" print_block bl print_exp exp
  | Eblock bl -> fprintf ff "Eblock %a" print_block bl
  | Eeq (pat, init, exp) -> fprintf ff "Eeq %a%a%a" print_pat pat
    Linearity.print_init init   print_exp exp

and print_eq ff {eq_desc=eqd} = fprintf ff "%a" print_eqdesc eqd


(* Node declaration *)
let print_objective_kind ff objkind = match objkind with
  | Obj_enforce -> fprintf ff "Obj_enforce"
  | Obj_reachable -> fprintf ff "Obj_reachable"
  | Obj_attractive -> fprintf ff "Obj_attractive"

let print_objective ff {o_kind=okind; o_exp=e} =
  fprintf ff "%a %a" print_objective_kind okind print_exp e

let print_contract ff {c_assume = assume;
       c_objectives = lobjectives;
       c_assume_loc = assume_loc;
       c_enforce_loc = enforce_loc;
       c_controllables = lcontrollables;
       c_block = bl} =
  fprintf ff "@[<v4>@ * assume = %a\n\
        objectives =\n@[<2>%a@]@\n\
        assume_loc = %a\n\
        enforce_loc = %a\n\
        controllables =\n@[<2>%a@]@\n\
        block =\n@[<2>%a@]@\n" print_exp assume
           (print_list print_objective "@ " "@ " "") lobjectives
           print_exp assume_loc
           print_exp enforce_loc
           (print_list print_var_dec "(" ";" ")") lcontrollables
           print_block bl

let print_typeparam_dec ff { t_nametype = tyname; t_nameclass = clname} = 
  fprintf ff "%a of %a" print_type_name tyname print_class_name clname

let print_node_dec ff {n_name = dname;
       n_stateful = stateful;
       n_unsafe = unsafe;
       n_typeparams = ltyparamdec;
       n_input = linput;
       n_output = loutput;
       n_contract = optcontract;
       n_block = bl;
       n_params = lparams;
       n_constraints = lexp_constr} =
  fprintf ff "@[<v2>node %a (stateful: %b | unsafe: %b)@\n\
        typeparams = %a@\n\
  		params = %a@\n\
  		inputs = @[<2>%a@]@\n\
  		outputs = @[<2>%a@]@\n\
  		contract = @[<2>%a@]@\n\
  		block =@[<2>%a@]@\n\
  		constraints =@[<2>%a@]@\n\
  		@]@\n@." print_dec_name dname
  		   stateful
  		   unsafe
  		   (print_list print_typeparam_dec "[" ";" "]") ltyparamdec
           (print_list print_var_dec "(" "; " ")") lparams
           (print_list print_var_dec "(" "; " ")") linput
           (print_list print_var_dec "(" "; " ")") loutput
           (print_opt print_contract) optcontract
           print_block bl
           (print_list print_exp "(" "," ")") lexp_constr


(* Constant declaration *)
let print_const_dec ff { c_name=dname; c_type=typ; c_value=vopt } =
  fprintf ff "%a::%a" print_dec_name dname  print_type typ;
  match vopt with
    | None -> ()
    | Some v -> fprintf ff "=%a" print_exp v


(* Type declaration *)
let print_type_desc ff tdesc = match tdesc with
  | Type_abs -> fprintf ff "Type_abs"
  | Type_alias talias -> fprintf ff "Type_alias %a" print_type talias
  | Type_enum ldname -> fprintf ff "(Type_enum %a)" (print_list print_dec_name "" "|" "") ldname
  | Type_struct lfield_type -> fprintf ff "(Type_struct %a)" (print_list
    (print_couple print_dec_name print_type "" ":" "") "" ", " "") lfield_type

let print_type_dec ff {t_name = name; t_desc = desc} =
  fprintf ff "@[type %a :@ %a@]@\n@." print_dec_name name  print_type_desc desc


let print_class_dec ff cdec = 
  fprintf ff "class %a (%a)@\n"
    print_class_name cdec.c_nameclass
    (print_list print_type_name "" ", " "") cdec.c_insttypes



(************************************)
(* *** Program level of the AST *** *)
(************************************)

let print_module_name ff name = fprintf ff "%s" (modul_to_string name)

let print_pdesc ff pdesc = match pdesc with
  | Ppragma (pr_name, str_content) -> fprintf ff "@[#%a %s@]"
          print_var_name pr_name str_content
  | Ptype t_dec -> print_type_dec ff t_dec
  | Pconst c_dec -> print_const_dec ff c_dec
  | Pclass c_dec -> print_class_dec ff c_dec
  | Pnode n_dec -> print_node_dec ff n_dec

(* Pretty-print a Hept_parsetree AST - Entry point*)
let print_AST oc { p_modname = pname; p_opened = po; p_desc = pd } =
  let ff = Format.formatter_of_out_channel oc in
  
  fprintf ff "@[<v>";
  fprintf ff "@[Modname = %a@]@." print_dec_name pname;
  fprintf ff "@[Opened modules = %a @]@." (print_list print_module_name "" " | " "") po;
  
  fprintf ff "@[--- Program description ---@]@.";
  List.iter (print_pdesc ff) pd;
  fprintf ff "@]";
  fprintf ff "@?"  (* Flush at the end *)

