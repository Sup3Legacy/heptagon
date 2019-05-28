
(* === Internal state exposal transformation ===
  Expose the internal state of any stateful function in a program
    by introducing a new argument to that function (as the FIRST input and output),
    by introducing a new (empty) datatype for the internal state of this function,
    by introducing a new "zero" constant for this datatype,
    and by creating 2 new variables (one for the input and one for the output),
    linked by a fby equation.

  Assume the program has be normalized beforehand (such that all equations
    containing a stateful function have )

  Author: Guillaume I
  *)
open Names
open Signature
open Modules
open Types
open Heptagon
open Hept_mapfold


(* === Naming conventions === *)
let pass_name = "internStateExposal"

let name_internal_state_var fun_name = "var_state_" ^ (Names.shortname fun_name)
let ident_internal_state_var fun_name =
  Idents.gen_var pass_name (name_internal_state_var fun_name)

let name_internal_state_var_fby fun_name = "fby_" ^ (name_internal_state_var fun_name)
let ident_internal_state_var_fby fun_name =
  Idents.gen_var pass_name (name_internal_state_var_fby fun_name)

let prefix_type_internal_state = "state_"
let name_type_internal_state fun_name = prefix_type_internal_state ^ (Names.shortname fun_name)
let qname_type_internal_state fun_name =
  Modules.current_qual (name_type_internal_state fun_name)
  (* Modules.fresh_type pass_name (name_type_internal_state fun_name) *)

let prefix_zero_constant_internal_state = "init_state_"
let name_zero_constant_internal_state fun_name = prefix_zero_constant_internal_state ^ (Names.shortname fun_name)
let qname_zero_constant_internal_state fun_name =
  Modules.current_qual (name_zero_constant_internal_state fun_name)
  (* Modules.fresh_const pass_name (name_zero_constant_internal_state fun_name) *)

(* Naming convention for the shared location of internal states *)
let get_loc_name_int_state fun_name = name_internal_state_var fun_name


(* ========================= *)


(* Function to know if a given function has an internal state *)
let has_internal_state fun_name =
  try
    let node = Modules.find_value fun_name in
    node.Signature.node_stateful
  with
    Not_found -> failwith ("internalStateExposal: " ^ (Names.fullname fun_name) ^ " is not a known function/node")

let add_first_tuple_ty tyFirst ty = match ty with
  | Tprod lty -> Tprod (tyFirst::lty)
  | _ -> Tprod (tyFirst::ty::[])

let exp_int_state funs acc exp = match exp.e_desc with
  | Eapp (ap, lsexp, optexp) -> begin
    match ap.a_op with
    | Efun fun_name | Enode fun_name -> begin
    
    (* Check if we have an internal state *)
    let bint_state = has_internal_state fun_name in
    if (not bint_state) then
      Hept_mapfold.exp funs acc exp
    else

    (* Doing the modification now *)
    let (ltydecl, lcstdecl, lvardecl, leqfby, oStart) = acc in
    assert(oStart=None); (* Should be cleaned up at equation level *)

    (* Getting the new names *)
    let id_int_qname = ident_internal_state_var fun_name in
    let id_fby_int_qname = ident_internal_state_var_fby fun_name in
    let ty_int_qname = qname_type_internal_state fun_name in
    let zero_int_qname = qname_zero_constant_internal_state fun_name in

    (* Type and constant declaration *)
    let tyIntState = Tid ty_int_qname in 
    let ntydecl = Hept_utils.mk_type_dec ty_int_qname Type_abs in
    let ncstdecl = {
        c_name = zero_int_qname;
        Heptagon.c_type = tyIntState;
        c_value = None;
        Heptagon.c_loc = Location.no_location;
      } in
    let loc_name_int_state = get_loc_name_int_state fun_name in
    
    (* Variable declaration *)
    let nvardecl = Hept_utils.mk_var_dec id_int_qname tyIntState
      ~linearity:(Linearity.Lat loc_name_int_state) in
    let nvardeclfby = Hept_utils.mk_var_dec id_fby_int_qname tyIntState
      ~linearity:(Linearity.Lat loc_name_int_state) in

    (* Inner calls *)
    (* Fby equation: var_fby = zero_const fby var_id *)
    (* var_fby is used inside the current equation *)
    let prhseqfby = Evarpat id_fby_int_qname in
    let sezerocst = Types.mk_static_exp tyIntState (Svar zero_int_qname) in
    (*let ezerocst = Hept_utils.mk_exp (Econst sezerocst) tyIntState ~linearity:Linearity.Ltop in *)
    let evarid = Hept_utils.mk_exp (Evar id_int_qname) tyIntState
      ~linearity:(Linearity.Lat loc_name_int_state) in
    let elhsfby = Hept_utils.mk_exp (Epre ((Some sezerocst), evarid)) tyIntState
      ~linearity:(Linearity.Lat loc_name_int_state) in
    let neqfby = Hept_utils.mk_simple_equation prhseqfby elhsfby in
    let neqfby = { neqfby with eq_inits = Linearity.Linit_var loc_name_int_state} in


    let sexpfirstarg = Hept_utils.mk_exp (Evar id_fby_int_qname) tyIntState
      ~linearity:(Linearity.Lat loc_name_int_state) in
    let nlsexp = sexpfirstarg :: lsexp (* @ [sexplastarg] *) in
    let nedesc = Eapp (ap, nlsexp, optexp) in

    let ntyexp = add_first_tuple_ty tyIntState exp.e_ty in
    let nexp = Hept_utils.mk_exp nedesc ntyexp ~linearity:(Linearity.Lat loc_name_int_state) in

    (* We need also to add variable as first (old: last) arg in the lhs of this equation *)
    (* => option "optlhsadd" with the varid to add to the lhs *)


    

    (* Finishing all that *)
    let nacc = if (not (Modules.check_type ty_int_qname)) then
      (* First time encountening this node call *)
      begin
      (* Update typedecl in Modules.g_env (by adding the new internal state types) *)
      Modules.add_type ty_int_qname Signature.Tabstract;
      (* Needed? Modules.add_const name *)

      (* Update the signature of the node *)
      let signode = Modules.find_value fun_name in
      let nStInArg = Signature.mk_arg None tyIntState Linearity.Ltop Cbase in
      let nlInArg = nStInArg :: signode.node_inputs in
      
      let nStOutArg = Signature.mk_arg None tyIntState Linearity.Ltop Cbase in
      let nlOutArg = nStOutArg :: signode.node_outputs in

      let n_signode = { signode with node_inputs = nlInArg; node_outputs = nlOutArg } in
      Modules.replace_value fun_name n_signode;

      (* Building the nacc *)
      let nltydecl = ntydecl :: ltydecl in
      let nlcstdecl = ncstdecl :: lcstdecl in
      let nlvardecl = nvardecl :: nvardeclfby :: lvardecl in
      let nleqfby = neqfby :: leqfby in
      let optlhsadd = Some id_int_qname in
      (nltydecl, nlcstdecl, nlvardecl, nleqfby, optlhsadd)
      end
    else
      (* Not the first time to encounter that node call => type decl and const decl already there *)
      begin
      let nltydecl = ltydecl in
      let nlcstdecl = lcstdecl in
      let nlvardecl = nvardecl :: nvardeclfby :: lvardecl in
      let nleqfby = neqfby :: leqfby in
      let optlhsadd = Some id_int_qname in
      (nltydecl, nlcstdecl, nlvardecl, nleqfby, optlhsadd)
     end
    in
    nexp, nacc
    end
    | _ -> Hept_mapfold.exp funs acc exp
  end
  | _ -> Hept_mapfold.exp funs acc exp

(* Add "vid" at the end of a pattern for equation lhs *)
(*let add_last_pattern vid plhs = match plhs with
  | Etuplepat pl -> Etuplepat (pl @ [Evarpat vid])
  | Evarpat vidpat -> Etuplepat ((Evarpat vidpat) :: (Evarpat vid) :: []) *)


(* Add "vid" at the beginning of a pattern for equation lhs *)
let add_first_pattern vid plhs = match plhs with
  | Etuplepat pl -> Etuplepat ((Evarpat vid) :: pl)
  | Evarpat vidpat -> Etuplepat ((Evarpat vid) :: (Evarpat vidpat) :: [])


let eqdesc_int_state funs acc eqdesc = match eqdesc with
  | Eeq (plhs, erhs) ->
    begin
      let (_,_,_,_,oStartInit) = acc in
      assert(oStartInit=None);
      let nerhs, acc = exp_int_state funs acc erhs in
      let (ltydecl, lcstdecl, lvardecl, leqfby, oStart) = acc in
      match oStart with
      | None -> eqdesc, acc
      | Some vid ->
        let nplhs = (* add_last_pattern*) add_first_pattern vid plhs in
        let neqdesc = Eeq (nplhs, nerhs) in
        let nacc = (ltydecl, lcstdecl, lvardecl, leqfby, None) in (* Reset *)

        neqdesc, nacc

    end
  | _ -> failwith "Internal state exposal: Equations should only be of the Eeq form at that point"


(* ========================= *)

(* Main functions *)
let node ltydecl lcstdecl nd =
  (* Mapfold here to get the function calls *)
  let funs_int_state = { defaults with exp = exp_int_state; eqdesc = eqdesc_int_state } in
  let nd, (ltydecl, lcstdecl, lvardecl, leqfby, _) =
    Hept_mapfold.node_dec funs_int_state (ltydecl, lcstdecl, [], [], None) nd in

  (* Integrating lvardecl and leqfby to the whole structure *)
  let bl = nd.n_block in
  let nlocVar = List.rev_append lvardecl bl.b_local in
  let neqs = List.rev_append leqfby bl.b_equs in

  let nbl = { nd.n_block with b_local = nlocVar; b_equs = neqs } in
  let nd = { nd with n_block = nbl } in

  (nd, ltydecl, lcstdecl)


let is_main_node nd =
  List.mem nd.n_name.name (List.map (fun qname -> qname.name) !Compiler_options.mainnode)


let program p =
  (* Calling the function on the nodes *)
  let (nlpdesc, ltydecl, lcstdecl) = List.fold_left
    (fun (acc, ltydecl, lcstdecl) pdesc -> match pdesc with
      | Pnode nd ->
        (* Only main node *)
        if (not (is_main_node nd)) then (Pnode nd)::acc, ltydecl, lcstdecl else
        let nd, ltydecl, lcstdecl = node ltydecl lcstdecl nd in
        (Pnode nd)::acc, ltydecl, lcstdecl
      | _ ->
        pdesc::acc, ltydecl, lcstdecl
    ) ([], [], []) p.p_desc in
  
  (* Adding the type declaration to the AST *)
  let nlpdesc = List.fold_left
    (fun acc elem -> (Ptype elem)::acc)
    nlpdesc ltydecl in

  (* Adding the constant declaration to the AST *)
  let nlpdesc = List.fold_left
    (fun acc elem -> (Pconst elem)::acc)
    nlpdesc lcstdecl in

  (* Update signatures in Modules.g_env *)
  (* let l_sig_glenv = Modules.g_env.values in
  let nl_sig_glenv = QualEnv.fold (fun k signode acc ->
    if (signode.node_stateful) then
      let name_tyStInt = Modules.current_qual (name_type_internal_state k) in
      let tyStInt = Tid name_tyStInt in

      let nStInArg = Signature.mk_arg None tyStInt Linearity.Ltop Cbase in
      let nlInArg = nStInArg :: signode.node_inputs in
      
      let nStOutArg = Signature.mk_arg None tyStInt Linearity.Ltop Cbase in
      let nlOutArg = nStOutArg :: signode.node_outputs in

      let n_signode = { signode with node_inputs = nlInArg; node_outputs = nlOutArg } in
      QualEnv.add k n_signode acc
    else
      QualEnv.add k signode acc
  ) l_sig_glenv QualEnv.empty in
  g_env.values <- nl_sig_glenv; *)

  {p with p_desc = nlpdesc}



