
(* This transformation remove the Epre(None, ...) from the AST,
  and replace them by Efby(stexp, ...), with a dummy static expression *)

(* Also perform alias substitution *)

(* Author: Guillaume I *)

open Names
open Idents
open Types
open Signature
open Heptagon
open Hept_mapfold



(* Produce a static expression "0" (for the left size of a fby) of type "ty" *)
(*let tyAliasInfoRef = ref []
let rec find_aliasInfo tyAliasInfo strTyid = match tyAliasInfo with
  | [] -> None
  | (nty, ty)::r ->
    if (strTyid = nty.name) then Some ty
    else find_aliasInfo r strTyid *)

(* WARNING! Safran specific => make it general purpose !!! *)

let rec init_stexp_fby t = match t with
  | Tid qname ->
    let name = qname.name in
    let se_desc = match name with
    | "int" -> Sint 0
    | "real" -> Sfloat 0.0
    | "float" -> Sfloat 0.0
    | "string" -> Sstring ""
    | "bool" -> Sbool false
    | _ ->
      (* The type name was defined somewhere in the program *)
      
      (* TODO Specific to Safran - change here !!! *)
      

      (* We use Safran type naming convention to get the type => DIRTY ! *)
      if ( (String.sub name 0 7)="Vector_") then
        let l = String.length name in
        let stri = String.sub name 7 (l-8) in
        let num_array = int_of_string stri in
        let sexp_numarray = mk_static_exp (Tid Initial.pint) (Sint num_array) in
        let sexp_ty = match (String.get name (l-1)) with
          | 'i' -> mk_static_exp (Tid Initial.pint) (Sint 0)
          | 'r' -> mk_static_exp (Tid Initial.pfloat) (Sfloat 0.0)
          | 'b' -> mk_static_exp (Tid Initial.pbool) (Sbool false)
          | _ -> failwith "unrecognized last char"
        in
        Sarray_power (sexp_ty, [sexp_numarray])
      else if ((String.sub name 0 7)="Matrix_") then
        let l = String.length name in
        let strSizes = String.sub name 7 (l-8) in
        let lstrSplit = Str.split (Str.regexp "x") strSizes in
        let (str_num_array1, str_num_array2) = Misc.assert_2 lstrSplit in
        let num_array1 = int_of_string str_num_array1 in
        let num_array2 = int_of_string str_num_array2 in
        let sexp_numarray1 = mk_static_exp (Tid Initial.pint) (Sint num_array1) in
        let sexp_numarray2 = mk_static_exp (Tid Initial.pint) (Sint num_array2) in

        let sexp_ty = match (String.get name (l-1)) with
          | 'i' -> mk_static_exp (Tid Initial.pint) (Sint 0)
          | 'r' -> mk_static_exp (Tid Initial.pfloat) (Sfloat 0.0)
          | 'b' -> mk_static_exp (Tid Initial.pbool) (Sbool false)
          | _ -> failwith "unrecognized last char"
        in
        Sarray_power(sexp_ty, sexp_numarray1::sexp_numarray2::[])
      else
        failwith ("get_dummy_st_expr - unrecognized type " ^ name)
    in
    mk_static_exp t se_desc
  | Tarray (ty, sexpr) ->
    let st_exp_ty = init_stexp_fby ty in
    let se_desc = Sarray_power (st_exp_ty, [sexpr]) in
    mk_static_exp t se_desc
  | Tprod lty ->
    let lst_exp = List.map init_stexp_fby lty in
    let se_desc = Stuple lst_exp in
    mk_static_exp t se_desc
  | Tclasstype _ -> failwith "init_stexp_fby : Classtype not managed."
  | Tinvalid -> failwith "init_stexp_fby : Constant declaration with Tinvalid type."



(* ---------------------------------------- *)
(* Transformation which replace the "pre" by "fby" *)

let edescPreRemoval funs acc edesc = match edesc with
  | Epre(None, sexp) ->
    let sexp, _ = funs.exp funs acc sexp in
    let se_dummy = init_stexp_fby sexp.e_ty in
    Epre(Some se_dummy, sexp), acc
  | _ ->
    Hept_mapfold.edesc funs acc edesc

let preRemoval nd = 
  let funsPreRemoval = { Hept_mapfold.defaults with edesc = edescPreRemoval } in
  let nd, _ = funsPreRemoval.node_dec funsPreRemoval [] nd in
  nd

(* ---------------------------------------- *)

(* Getting infos about aliased type declarations *)
(* tyAliasInfo: (qualname * ty) list *)
let getTyAliasInfo p =
  let tyAliasInfo = List.fold_left
    (fun acc pdesc -> match pdesc with
      | Ptype td -> begin
        match td.t_desc with
          | Type_alias ty -> (td.t_name, ty)::acc
          | _ -> acc
        end
      | _ -> acc
    ) [] p.p_desc in
  tyAliasInfo


let rec find_aliasInfo tyAliasInfo tid = match tyAliasInfo with
  | [] -> None
  | (nty, ty)::r ->
    if (tid.name = nty.name) then Some ty
    else find_aliasInfo r tid

let replaceType tyAliasInfo tyVarLoc = match tyVarLoc with
  | Tid tid ->
    begin
    let optTy = find_aliasInfo tyAliasInfo tid in
    match optTy with
      | None -> tyVarLoc
      | Some ty -> ty
    end
  | _ -> tyVarLoc


(* Iterate over all local variables and replace their type with the aliased expression, if needed *)
let aliasSubstitution tyAliasInfo nd =
  let replaceAliasType tyAliasInfo varLoc =
    let tyVarLoc = varLoc.v_type in
    { varLoc with v_type = replaceType tyAliasInfo tyVarLoc }
    (* match tyVarLoc with
      | Tid tid ->
        begin
        let optTy = find_aliasInfo tyAliasInfo tid in
        match optTy with
          | None -> varLoc
          | Some ty -> { varLoc with v_type = ty }
        end
      | _ -> varLoc *)
  in
  let lVarLoc = nd.n_block.b_local in
  let nlVarLoc = List.map (replaceAliasType tyAliasInfo) lVarLoc in
  let nbl = { nd.n_block with b_local = nlVarLoc } in

  let nlVarIn = List.map (replaceAliasType tyAliasInfo) nd.n_input in
  let nlVarOut = List.map (replaceAliasType tyAliasInfo) nd.n_output in

  { nd with n_block = nbl; n_input = nlVarIn; n_output = nlVarOut }


(* ---------------------------------------- *)

(* TODO: code duplication with dirty_hyperperiod_expansion ? => contract that ???*)
(* TODO: get informations of types and make the init_stexp_fby initialisation more general *)


(* Alias substitution in the arguments of the signature of the global environment *)
let arg_subst_ty tyAliasInfo arg =
  { arg with a_type = replaceType tyAliasInfo arg.a_type}


let program p =
  let tyAliasInfo = getTyAliasInfo p in

  (* Substitution on the signatures in Modules *)
  let n_env_values = QualEnv.fold (fun k sign acc ->
    let ninputs = List.map (fun argin ->
      arg_subst_ty tyAliasInfo argin
    ) sign.node_inputs in
    let noutputs = List.map (fun argout ->
      arg_subst_ty tyAliasInfo argout
    ) sign.node_outputs in
    let nsign = { sign with node_inputs = ninputs; node_outputs = noutputs } in
    QualEnv.add k nsign acc
  ) Modules.g_env.values QualEnv.empty in
  Modules.g_env.values <- n_env_values;

  (* Substitution on the nodes of the program *)
  let lnpdesc = List.map (fun pdesc -> match pdesc with
    | Pnode nd ->
      let nd = aliasSubstitution tyAliasInfo nd in
      let nd = preRemoval nd in
      Pnode nd
    | _ -> pdesc
  ) p.p_desc in
  { p with p_desc = lnpdesc }

