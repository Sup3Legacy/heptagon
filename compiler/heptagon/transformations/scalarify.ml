
(* Scalarification program transformation *)
(* Assumes Typing, Normalization has been done and only Eeq equations remains *)
(* It is preferable that inlining has been done (so that the newly created nodes do not interfere) *)
(* For each node of the main node:
  - Check its signature
  - If it contains an array:
     * Create a encapsulating node, with only a scalar interface, such that:
        -> The equation remains at the start
        -> Each input arrays are rebuilt
        -> Each output arrays are destructed
  NOTE: only manage 1D arrays (not higher-dim, even if it can be extended)
 *)

open Names
open Types
open Signature
open Heptagon


(* TODO DEBUG *)
let debug_scalarify = false (* DEBUG *)
let ffout = Format.formatter_of_out_channel stdout



(* fold-like iterator with an integer counter *)
let fold_k_times f k =
  let rec fold_k_times_aux f k res =
    assert(k>=0); match k with
    | 0 -> res
    | _ -> fold_k_times_aux f (k-1) ((f (k-1))::res)
  in
  fold_k_times_aux f k []


(* Detection functions *)

(* Check if an equation is Eeq, and extract its lhs/rhs *)
let get_lhs_rhs_eq eq = match eq.eq_desc with
  | Eeq (plhs, erhs) -> (plhs, erhs)
  | _ -> failwith "Scalarify: equation in the main node is not in Eeq form."

(* Get the list of variable id inside a pattern *)
let rec extract_varId p = match p with
  | Evarpat vid -> [vid]
  | Etuplepat pl ->
    let llvid = List.map extract_varId pl in
    let lvid = List.flatten llvid in
    lvid

(* Check if an equation is a function call *)
let is_function_call eq =
  let (plhs, erhs) = get_lhs_rhs_eq eq in
  match erhs.e_desc with
  | Eapp (app, lsexp, _) -> begin
    match app.a_op with
      | Enode (f,_) | Efun (f, _) -> Some (f, plhs, lsexp)
      | _ -> None 
    end
  | _ -> None

(* Assume that a static expression is an integer and extract it*)
let sexp_assert_int se = match se.se_desc with
  | Sint i -> i
  | _ -> failwith "scalarify::sexp_assert_int : not an integer"

(* Check if a type is an array *)
let not_an_array ty = match ty with
  | Tarray _ -> false
  | _ -> true

(* Get the base type and the size of the array, from an array type*)
let get_info_ty_array ty = match ty with
  | Tarray (basety, sesize) ->
      (basety, (sexp_assert_int sesize))
  | _ -> failwith "scalarify::get_info_ty_array : type is not an Tarray"


(* Check if a signature contains only scalar as input and output *)
let signature_only_scalar s =
  let inputs = s.node_inputs in
  let outputs = s.node_outputs in
  let no_array = List.fold_left (fun acc elem ->
    acc && (not_an_array elem.a_type)
  ) true inputs in
  let no_array = List.fold_left (fun acc elem ->
    acc && (not_an_array elem.a_type)
  ) no_array outputs in
  no_array

(* =============================================================== *)

(* New scalar variable naming convention *)
let pref_scal_var_name = "var_1d_"
let scal_var_name strVar strcounter = pref_scal_var_name ^ strcounter ^ "_" ^ strVar


(* Given an array variable declaration "Var" and a naming convention,
    build the list of variable declartion for the "Var_i" *)
let build_lvd_array idvar vty fun_scal_name =
  (* This function should not be applied to a non-array*)
  if (not_an_array vty) then
    failwith "build_lvd_array : not an array"
  else
  
  let (base_ty, size_array) = get_info_ty_array vty in

  (* List of new variable declaration for the cells of the array *)
  let lvdVari = fold_k_times (fun k -> 
      let namevari = fun_scal_name (Idents.name idvar) (string_of_int k) in
      let idvari = Idents.gen_var "scalarify" namevari in
      Hept_utils.mk_var_dec idvari base_ty ~linearity:Linearity.Ltop
    ) size_array in

  assert((List.length lvdVari) = size_array);
  lvdVari

(* Given an array variable declaration "Var" and
    a list of variable declarations associated to its cells
    build the equation: "Var = [ ... Var_i ... ]" *)
let reconstruction_eq_array idvar vty lvdVari =
  (* This function should not be applied to a non-array*)
  if (not_an_array vty) then
    failwith "reconstruction_eq_array : not an array"
  else
  
  let (base_ty, size_array) = get_info_ty_array vty in
  assert((List.length lvdVari) = size_array);

  (* Build the equation *)
  let lsexprhs = List.map (fun vd ->
    Hept_utils.mk_exp (Evar vd.v_ident) base_ty ~linearity:Linearity.Ltop
  ) lvdVari in
  
  let appArray = Hept_utils.mk_app Earray in
  let edescrhs = Eapp (appArray, lsexprhs, None) in
  let erhs = Hept_utils.mk_exp edescrhs vty ~linearity:Linearity.Ltop in

  let eq = Hept_utils.mk_simple_equation (Evarpat idvar) erhs in
  eq


(* Given an array variable declaration "Var" and
    a list of variable declarations associated to its cells
    build the list of equation: "Var_i = Var[i]" *)
let deconstruction_eq_array idvar vty lvdVari =
  (* This function should not be applied to a non-array*)
  if (not_an_array vty) then
    failwith "deconstruction_eq_array : not an array"
  else
  
  let (base_ty, size_array) = get_info_ty_array vty in
  assert((List.length lvdVari) = size_array);

  (* Build the list of equation *)
  let leq = List.mapi (fun i vdVari ->
    let sexprhs = Hept_utils.mk_exp (Evar idvar) vty ~linearity:Linearity.Ltop in
    let lsexprhs = sexprhs::[] in

    let seinti = mk_static_exp Initial.tint (Sint i) in
    let appSelect = Hept_utils.mk_app ~params:(seinti::[]) Eselect in
    let edescrhs = Eapp (appSelect, lsexprhs, None) in
    let erhs = Hept_utils.mk_exp edescrhs base_ty ~linearity:Linearity.Ltop in

    Hept_utils.mk_simple_equation (Evarpat vdVari.v_ident) erhs
  ) lvdVari in
  leq


(* =============================================================== *)

(* New scalarified nodes naming convention *)
let scalarified_node_name nameOrig = "scalarified_" ^ nameOrig


(* Build the scalarified node from the original signature and the func call *)
let build_scalarified_node_call fun_name sig_fun =

  let counter_in = ref 0 in
  let suffix_var_in = "in_" in
  let get_name_in _ =
    let name_in = suffix_var_in ^ (string_of_int !counter_in) in
    counter_in := !counter_in + 1;
    name_in
  in

  let counter_out = ref 0 in
  let suffix_var_out = "out_" in
  let get_name_out _ =
    let name_out = suffix_var_out ^ (string_of_int !counter_out) in
    counter_out := !counter_out + 1;
    name_out
  in

  (* 1) Part of the node before the function call *)
  (* l_inputs: list of var decl input of the node  (order matters)
     l_locvar: list of var decl local of the node
     leq : list of equations of the form "locVar = [list of inputs in an array]"
     linarg : list of argument of the main equation of the node (calling sig_fun.node_name - order matters) *)
  let (l_inputs, l_locvar, leq, linarg) = List.fold_right (fun inSig (accin, accloc, acceq, accarg) ->
    let name_in = get_name_in () in
    let id_varin = Idents.gen_var "scalarify" name_in in
    
    (* Get the new variable declaration to be put as an input *)
    let nvardecl = Hept_utils.mk_var_dec id_varin inSig.a_type ~linearity:Linearity.Ltop in
    let narg = Hept_utils.mk_exp (Evar id_varin) inSig.a_type ~linearity:Linearity.Ltop in

    if (not_an_array inSig.a_type) then
      (* Plug directly in the func call *)
      (nvardecl :: accin, accloc, acceq, narg::accarg)
    else
      (* Reconstruction equation needed at the middle *)
      let lnvardecl = build_lvd_array id_varin inSig.a_type scal_var_name in
      let neq = reconstruction_eq_array id_varin inSig.a_type lnvardecl in
      (lnvardecl @ accin, nvardecl::accloc, neq::acceq, narg::accarg)
  ) sig_fun.node_inputs ([], [], [], []) in

  (* 2) Part of the node after the function call *)
  (* l_outputs: list of var decl output of the node  (order matters)
     loutvd : list of outputs of the main equation of the node (calling sig_fun.node_name - order matters) *)
  let (l_outputs, l_locvar, leq, loutvd) = List.fold_right (fun outSig (accout, accloc, acceq, accarg) ->
    let name_out = get_name_out () in
    let id_varout = Idents.gen_var "scalarify" name_out in

    (* Get the new variable declaration to be put as an input *)
    let nvardecl = Hept_utils.mk_var_dec id_varout outSig.a_type ~linearity:Linearity.Ltop in

    if (not_an_array outSig.a_type) then
      (* Plug directly out of the func call *)
      (nvardecl :: accout, accloc, acceq, nvardecl::accarg)
    else
      (* Deconstruction equations needed at the middle *)
      let lnvardecl = build_lvd_array id_varout outSig.a_type scal_var_name in
      let nleq = deconstruction_eq_array id_varout outSig.a_type lnvardecl in
      (lnvardecl @ accout, nvardecl :: accloc, nleq @ acceq, nvardecl::accarg)
  ) sig_fun.node_outputs ([], l_locvar, leq, []) in

  (* 3) Function call equation *)
  let app_funcall = Hept_utils.mk_app (Enode (fun_name,[])) in
  let sexp_funcall = linarg in
  let edesc_funcall = Eapp (app_funcall, sexp_funcall, None) in
  let ty_funcall = if ((List.length loutvd)=1) then
      (List.hd loutvd).v_type
    else
      Tprod (List.map (fun vdec -> vdec.v_type) loutvd)
  in
  let erhs_funcall = Hept_utils.mk_exp edesc_funcall ty_funcall ~linearity:Linearity.Ltop in

  let plhs_funcall = if ((List.length loutvd)=1) then
      Evarpat ((List.hd loutvd).v_ident)
    else
      Etuplepat (List.map (fun vdec -> Evarpat vdec.v_ident) loutvd)
  in
  let eq_funcall = Hept_utils.mk_simple_equation plhs_funcall erhs_funcall in

  let leq = eq_funcall :: leq in

  (* 4) Building the whole node *)
  let block = Hept_utils.mk_block ~locals:l_locvar leq in
  let name_scal_node = scalarified_node_name fun_name.name in
  let qname_scal_node = Modules.current_qual name_scal_node in

  (* TODO: traduire typeparam_def (Signature) into typparam_dec *)

  let typaramdecs = List.map (fun typardef ->
    let qname_type = Modules.current_qual typardef.tp_nametype in
    let qname_class = Modules.qualify_class typardef.tp_nameclass in
    Hept_utils.mk_typeparam_dec qname_type qname_class
  ) sig_fun.node_typeparams in

  let nd = Hept_utils.mk_node
    ~typeparamdecs:typaramdecs ~input:l_inputs ~output:l_outputs
    ~param:sig_fun.node_params  ~constraints:sig_fun.node_param_constraints
    qname_scal_node block
  in
  nd


(* We memorize the created nodes:
   macc : Node_name --> Scalarified node
 *)
let eq_scalarify mvid_vdec macc eq =
  (* Note: program has been normalized *)
  (* Is eq a function call? *)
  let optInfoCall = is_function_call eq in
  match optInfoCall with
  | None -> (eq::[], [], macc)
  | Some (fun_name, lplhs, lsexp) -> begin

    (* We get the signature of fun_name *)
    let sig_fun = Modules.find_value fun_name in
    if (signature_only_scalar sig_fun) then (eq::[], [], macc) else
    begin

    if (debug_scalarify) then
      Format.fprintf ffout "... Scalarifying node call to \"%a\"\n@?"
        Global_printer.print_qualname fun_name;

    (* We have arrays => we build the a new (scalar) node *)
    (* If a new node is built, we update macc *)
    let (nd_scal, macc) = try
        (QualEnv.find fun_name macc, macc)
      with Not_found ->
        let nd = build_scalarified_node_call fun_name sig_fun in
        let macc = QualEnv.add fun_name nd macc in
        (nd, macc)
    in
    Modules.add_value nd_scal.n_name (Hept_utils.signature_of_node nd_scal);

    if (debug_scalarify) then
      Format.fprintf ffout "... ... Scalarified node built\n@?";


    (* Build adaptation equations *)
    (* a) Inputs of the fun_call : check lsexp
      (which must bea list of Evar or Econst, because of normalization) *)
    (* If this is a constant, no need to adapt *)
    let (nleq_in, nllocvar_in, lexpr_in) = List.fold_right (fun sexp (acceq, accloc, accexp) ->
      match sexp.e_desc with
      | Econst _ -> 
        (* Do not touch the constant, even if it is an array *)
        (acceq, accloc, sexp::accexp)
      | Evar vid -> begin
        let vd = Idents.Env.find vid mvid_vdec in
        if (not_an_array vd.v_type) then
          let varexp = Hept_utils.mk_exp (Evar vd.v_ident) vd.v_type ~linearity:Linearity.Ltop in
          (acceq, accloc, varexp::accexp)
        else

        (* Deconstruct *)
        let lvd_loc = build_lvd_array vd.v_ident vd.v_type scal_var_name in
        let leq = deconstruction_eq_array vd.v_ident vd.v_type lvd_loc in
        let nlsexp = List.map (fun vd ->
          Hept_utils.mk_exp (Evar vd.v_ident) vd.v_type ~linearity:Linearity.Ltop
        ) lvd_loc in

        ((List.rev_append leq acceq), (List.rev_append lvd_loc accloc), nlsexp @ accexp)
      end
      | _ -> failwith
        "scalarify::eq_scalarify : subexpression of fun call is neither a variable or a constant"
    ) lsexp ([], [], []) in

    if (debug_scalarify) then
      Format.fprintf ffout "... ... Input adaptation to the scalarified fun call done\n@?";

    (* b) Outputs of the fun_call : check lplhs *)
    let lvid_out = extract_varId lplhs in
    let lvd_out = List.map (fun vid -> Idents.Env.find vid mvid_vdec) lvid_out in
    let (nleq_out, nllocvar_out, lvd_out) = List.fold_left (fun (acceq, accloc, accvdarg) vd ->
      (* If not an array : do nothing*)
      if (not_an_array vd.v_type) then (acceq, accloc, vd::accvdarg) else

      let lvd_loc = build_lvd_array vd.v_ident vd.v_type scal_var_name in
      let eq = reconstruction_eq_array vd.v_ident vd.v_type lvd_loc in

      (eq :: acceq, (List.rev_append lvd_loc accloc), lvd_loc @ accvdarg)
    ) ([],[],[]) lvd_out in

    if (debug_scalarify) then
      Format.fprintf ffout "... ... Output adaptation to the scalarified fun call done\n@?";

    (* Build the new equation issuing the scalarified function call *)
    let fun_name_scalarified = nd_scal.n_name in
    let app_funcall = Hept_utils.mk_app (Enode (fun_name_scalarified,[])) in
    let sexp_funcall = lexpr_in in
    let edesc_funcall = Eapp (app_funcall, sexp_funcall, None) in
    let ty_funcall = if ((List.length lvd_out)=1) then
        (List.hd lvd_out).v_type
      else
        Tprod (List.map (fun vdec -> vdec.v_type) lvd_out)
    in
    let erhs_funcall = Hept_utils.mk_exp edesc_funcall ty_funcall ~linearity:Linearity.Ltop in
    let plhs_funcall = if ((List.length lvd_out)=1) then
        Evarpat ((List.hd lvd_out).v_ident)
      else
        Etuplepat (List.map (fun vdec -> Evarpat vdec.v_ident) lvd_out)
    in
    let eq_funcall = Hept_utils.mk_simple_equation plhs_funcall erhs_funcall in

    if (debug_scalarify) then
      Format.fprintf ffout "... ... Scalarified fun call equation done\n@?";

    (* Putting everything together *)
    let nleq = eq_funcall :: (nleq_out @ nleq_in) in
    let nlocvar = nllocvar_in @ nllocvar_out in

    (nleq, nlocvar, macc)
    end
  end

(* Note: no need to do anything on the input/outputs array of the node
    (already managed by array destruct) *)


(* =============================================================== *)

(* Only applied to the main node *)
let node nd =

  if (debug_scalarify) then
    Format.fprintf ffout "Entering main node \"%a\"...\n@?" Global_printer.print_qualname nd.n_name;

  let bl = nd.n_block in
  
  (* Building a map vid -> variable declaration to make searchs faster *)
  let mvid_vdec = Idents.Env.empty in
  let mvid_vdec = List.fold_left
    (fun acc vd -> Idents.Env.add vd.v_ident vd acc) mvid_vdec nd.n_input in
  let mvid_vdec = List.fold_left
    (fun acc vd -> Idents.Env.add vd.v_ident vd acc) mvid_vdec nd.n_output in
  let mvid_vdec = List.fold_left
    (fun acc vd -> Idents.Env.add vd.v_ident vd acc) mvid_vdec bl.b_local in

  (* Go over all equations to build the scalarified nodes and the corresponding adaptations *)
  let (neqs, nlocvar, mscalarified_nodes) = List.fold_left (fun (acceq, accloc, macc) eq ->
    let (neqs, nlocvar, macc) = eq_scalarify mvid_vdec macc eq in
    ( (List.rev_append neqs acceq), (List.rev_append nlocvar accloc), macc)
  ) ([], bl.b_local, QualEnv.empty) bl.b_equs in

  let nbl = { bl with b_equs = neqs; b_local = nlocvar } in
  let nd = { nd with n_block = nbl }  in

  (* We add the new scalarified nodes *)
  let new_nd = QualEnv.fold (fun _ v acc -> v::acc) mscalarified_nodes [] in
  nd :: new_nd


let is_main_node nd =
  List.mem nd.n_name.name (List.map (fun qname -> qname.name) !Compiler_options.mainnode)

let program p =
  let npdesc = List.fold_left (fun acc pdesc ->
    match pdesc with
      | Pnode nd ->
        (* Only main node *)
        if (not (is_main_node nd)) then
          (Pnode nd)::acc
        else
          let lnew_nd = node nd in
          let new_pnode = List.rev_map (fun nd1 -> Pnode nd1) lnew_nd in
          List.rev_append new_pnode acc
      | _ -> pdesc::acc
    ) [] p.p_desc in
  { p with p_desc = npdesc }

