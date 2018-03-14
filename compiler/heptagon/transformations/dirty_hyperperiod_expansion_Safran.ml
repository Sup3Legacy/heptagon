(* Quick and dirty hyperperiod expansion for the Safran usecase *)

(* Author: Guillaume I *)

(* Valid only if all the equations are on the base clock, like in the Safran usecase *)
(* Output a code to be parsed by Lopht (with release/deadline) *)
(* Perform the following modifications:
     - Var ===> Var_XXX (+ log the different version in a HashTable)
     - Eq  ===> If not fby, duplicates it, while adding the _XXX at the end of all its equations
     			If pre, then error (should not remain at that point)
     			If fby, then do "Var_0 = 0.0 fby Var_(num_period-1)"
     							"Var_i = Var_(i-1)"
     - Annotations release/deadline for Safran

  Input/output management => Also duplicate them
  *)
open Idents
open Names
open Types
open Heptagon

exception PreShouldNotAppearHere (* "pre" equations were already removed manually beforehand *)
exception Equation_not_in_Eeq_form
exception VariableNotFoundInHashTbl
exception VariableNotFoundInLVarDec
exception Empty_list
exception Sequenceur_call_not_found (* The call to the sequenceur was not found *)

(* Number of times we should unroll *)
let num_period = 16


(* Naming convention for the new variables *)
let strDelimEnd_varid = "_sh"

let name_varid_instances varId i =
  let strNameVar = (Idents.name varId) ^ strDelimEnd_varid ^ (string_of_int i) in
  Idents.gen_var "hyperExpans" strNameVar

(* Reverse function of the previous convention *)
let remove_suffix_hypexp vid =
  let lstrSplit = Str.split (Str.regexp strDelimEnd_varid) (Idents.name vid) in
  List.hd lstrSplit

let rec search_in_lvardec str lvid = match lvid with
  | [] -> raise VariableNotFoundInLVarDec
  | h::t -> if ((Idents.name h.v_ident)=str) then h else
    search_in_lvardec str t


(* Function which creates the num_period instances of a var *)
let create_all_var_instances var num_period =
  let rec create_all_var_instances_aux var i =
    if (i=num_period) then [] else
    let tl_res = create_all_var_instances_aux var (i+1) in
    let nVardec = Hept_utils.mk_var_dec ~last:var.v_last ~clock:Clocks.Cbase (* NOTE! do not do a copy here *)
    (name_varid_instances var.v_ident i) var.v_type ~linearity:var.v_linearity in
    nVardec :: tl_res
  in
  create_all_var_instances_aux var 0


(* Clock management *)
(* SEQ_Seq_B (first arg of  Wfz02_00_seq.wfz02_00_seq) + all outputs of Wfz02_00_seq.wfz02_00_seq *)
type clock_safran = {
  period : int;           (* 1, 2, 4, 8 or 16 / note: 1 => the clock is the base clock (=true) *)
  shift : int;            (* 0<= shift < period *)
  got_InitCmpl_B : bool;  (* true: the clock got a " and InitCmpl_B" in its expression *)
  special_case : int;    (* SEQ_Idp_B => 1 | SEQ_SelCcr16_4_B => 2 *)
}

let mk_clock_safran p s init = {period = p; shift = s; got_InitCmpl_B = init; special_case = 0}

let mk_clock_safran_special_case spcase = {period = 16; shift = 0; got_InitCmpl_B=false; special_case = spcase}

(* Correspondance (from the equations of Wfz02_00_seq.wfz02_00_seq)
  00   SEQ_NumHTR_I : int ;             = OSASI_MFCnt_I

  01   SEQ_P1MF0_B : bool ;             = InitCmpl_B
  02   SEQ_P2MF0_B : bool ;             = ((OSASI_MFCnt_I - S2S_Prod(OSASI_MFCnt_I , 2) * 2) = 0) and InitCmpl_B
  03   SEQ_P2MF1_B : bool ;             = ((OSASI_MFCnt_I - S2S_Prod(OSASI_MFCnt_I , 2) * 2) = 1) and InitCmpl_B
  04   SEQ_P4MF1_B : bool ;             = ((OSASI_MFCnt_I - S2S_Prod(OSASI_MFCnt_I , 4) * 4) = 1) and InitCmpl_B
  05   SEQ_P4MF2_B : bool ;             = ((OSASI_MFCnt_I - S2S_Prod(OSASI_MFCnt_I , 4) * 4) = 2) and InitCmpl_B
  06   SEQ_P4MF3_B : bool ;             = ((OSASI_MFCnt_I - S2S_Prod(OSASI_MFCnt_I , 4) * 4) = 3) and InitCmpl_B
  07   SEQ_P8MF0_B : bool ;             = ((OSASI_MFCnt_I - S2S_Prod(OSASI_MFCnt_I , 8) * 8) = 0) and InitCmpl_B
  08   SEQ_P8MF1_B : bool ;             = ((OSASI_MFCnt_I - S2S_Prod(OSASI_MFCnt_I , 8) * 8) = 1) and InitCmpl_B
  09   SEQ_P8MF2_B : bool ;             = ((OSASI_MFCnt_I - S2S_Prod(OSASI_MFCnt_I , 8) * 8) = 2) and InitCmpl_B
  10   SEQ_P8MF3_B : bool ;             = ((OSASI_MFCnt_I - S2S_Prod(OSASI_MFCnt_I , 8) * 8) = 3) and InitCmpl_B
  11   SEQ_P8MF5_B : bool ;             = ((OSASI_MFCnt_I - S2S_Prod(OSASI_MFCnt_I , 8) * 8) = 5) and InitCmpl_B
  12   SEQ_P8MF6_B : bool ;             = ((OSASI_MFCnt_I - S2S_Prod(OSASI_MFCnt_I , 8) * 8) = 6) and InitCmpl_B
  13   SEQ_P8MF7_B : bool               = ((OSASI_MFCnt_I - S2S_Prod(OSASI_MFCnt_I , 8) * 8) = 7) and InitCmpl_B
  14   SEQ_P16MF0_B : bool ;            = ((OSASI_MFCnt_I - (S2S_Prod(OSASI_MFCnt_I , 16) * 16)) = 0) and InitCmpl_B
  15   SEQ_P16MF1_B : bool ;            = ((OSASI_MFCnt_I - (S2S_Prod(OSASI_MFCnt_I , 16) * 16)) = 1) and InitCmpl_B
  16   SEQ_P16MF7_B : bool ;            = ((OSASI_MFCnt_I - (S2S_Prod(OSASI_MFCnt_I , 16) * 16)) = 7) and InitCmpl_B
  17   SEQ_P16MF9_B : bool ;            = ((OSASI_MFCnt_I - (S2S_Prod(OSASI_MFCnt_I , 16) * 16)) = 9) and InitCmpl_B

  18   SEQ_Xchs_B : bool ;              = true
  19   SEQ_Xchr_B : bool ;              = true
  20   SEQ_Hlth_B : bool ;              = true
  21   SEQ_Pwrsup_B : bool ;            = true
  22   SEQ_Idp_B : bool ;               = (not (InitCmpl_B)) and (OSASI_MFCnt_I = 3)

  23   SEQ_P1MF0NoInit_B : bool ;       = true
  24   SEQ_P2MF0NoInit_B : bool ;       = ((OSASI_MFCnt_I - S2S_Prod(OSASI_MFCnt_I , 2) * 2) = 0)
  25   SEQ_P2MF1NoInit_B : bool ;       = ((OSASI_MFCnt_I - S2S_Prod(OSASI_MFCnt_I , 2) * 2) = 1)
  26   SEQ_P4MF1NoInit_B : bool ;       = ((OSASI_MFCnt_I - S2S_Prod(OSASI_MFCnt_I , 4) * 4) = 1)
  27   SEQ_P4MF2NoInit_B : bool ;       = ((OSASI_MFCnt_I - S2S_Prod(OSASI_MFCnt_I , 4) * 4) = 2)
  28   SEQ_P4MF3NoInit_B : bool ;       = ((OSASI_MFCnt_I - S2S_Prod(OSASI_MFCnt_I , 4) * 4) = 3)
  29   SEQ_P8MF0NoInit_B : bool ;       = ((OSASI_MFCnt_I - S2S_Prod(OSASI_MFCnt_I , 8) * 8) = 0)
  30   SEQ_P8MF2NoInit_B : bool ;       = ((OSASI_MFCnt_I - S2S_Prod(OSASI_MFCnt_I , 8) * 8) = 2)
  31   SEQ_P8MF3NoInit_B : bool ;       = ((OSASI_MFCnt_I - S2S_Prod(OSASI_MFCnt_I , 8) * 8) = 3)
  32   SEQ_P8MF4NoInit_B : bool ;       = ((OSASI_MFCnt_I - S2S_Prod(OSASI_MFCnt_I , 8) * 8) = 4)
  33   SEQ_P16MF1NoInit_B : bool ;      = ((OSASI_MFCnt_I - (S2S_Prod(OSASI_MFCnt_I , 16) * 16)) = 1)
  34   SEQ_P16MF2NoInit_B : bool ;      = ((OSASI_MFCnt_I - (S2S_Prod(OSASI_MFCnt_I , 16) * 16)) = 2)
  35   SEQ_P16MF3NoInit_B : bool ;      = ((OSASI_MFCnt_I - (S2S_Prod(OSASI_MFCnt_I , 16) * 16)) = 3)
  36   SEQ_P16MF4NoInit_B : bool ;      = ((OSASI_MFCnt_I - (S2S_Prod(OSASI_MFCnt_I , 16) * 16)) = 4)
  37   SEQ_P16MF9NoInit_B : bool ;      = ((OSASI_MFCnt_I - (S2S_Prod(OSASI_MFCnt_I , 16) * 16)) = 9)
  38   SEQ_SelCcr16_4_B : bool ;        = (((OSASI_MFCnt_I - (S2S_Prod(OSASI_MFCnt_I , 16) * 16)) = 3) and not (InitCmpl_B))
                                          or (((OSASI_MFCnt_I - (S2S_Prod(OSASI_MFCnt_I , 16) * 16)) = 9) and InitCmpl_B)
  39   SEQ_P16MF8_B : bool ;            = InitCmpl_B and ((OSASI_MFCnt_I - (S2S_Prod(OSASI_MFCnt_I , 16) * 16)) = 8)
  40   SEQ_P16MF11_B : bool ;           = InitCmpl_B and ((OSASI_MFCnt_I - (S2S_Prod(OSASI_MFCnt_I , 16) * 16)) = 11)

  41   SEQ_EIUInitInProg_B : bool        = SEQ_EIUInitInProgress(InitWd_PwrUpRst_B, LongInitFlg_B)
*)
let correspondance_clock_safran = Array.make 42 None

let base_clock = mk_clock_safran 1 0 false   (* Clock associated to the first argument of the sequenceur *)

let fill_correspondance_clock_array () =
  Array.set correspondance_clock_safran 0 None;         (* None = never used as a clock *)
  Array.set correspondance_clock_safran 1 (Some (mk_clock_safran 1 0 true));
  Array.set correspondance_clock_safran 2 (Some (mk_clock_safran 2 0 true));
  Array.set correspondance_clock_safran 3 (Some (mk_clock_safran 2 1 true));
  Array.set correspondance_clock_safran 4 (Some (mk_clock_safran 4 1 true));
  Array.set correspondance_clock_safran 5 (Some (mk_clock_safran 4 2 true));
  Array.set correspondance_clock_safran 6 (Some (mk_clock_safran 4 3 true));
  Array.set correspondance_clock_safran 7 (Some (mk_clock_safran 8 0 true));
  Array.set correspondance_clock_safran 8 (Some (mk_clock_safran 8 1 true));
  Array.set correspondance_clock_safran 9 (Some (mk_clock_safran 8 2 true));
  Array.set correspondance_clock_safran 10 (Some (mk_clock_safran 8 3 true));
  Array.set correspondance_clock_safran 11 (Some (mk_clock_safran 8 5 true));
  Array.set correspondance_clock_safran 12 (Some (mk_clock_safran 8 6 true));
  Array.set correspondance_clock_safran 13 (Some (mk_clock_safran 8 7 true));
  Array.set correspondance_clock_safran 14 (Some (mk_clock_safran 16 0 true));
  Array.set correspondance_clock_safran 15 (Some (mk_clock_safran 16 1 true));
  Array.set correspondance_clock_safran 16 (Some (mk_clock_safran 16 7 true));
  Array.set correspondance_clock_safran 17 (Some (mk_clock_safran 16 9 true));

  Array.set correspondance_clock_safran 18 (Some (mk_clock_safran 1 0 false));
  Array.set correspondance_clock_safran 19 (Some (mk_clock_safran 1 0 false));
  Array.set correspondance_clock_safran 20 (Some (mk_clock_safran 1 0 false));
  Array.set correspondance_clock_safran 21 (Some (mk_clock_safran 1 0 false));
  Array.set correspondance_clock_safran 22 (Some (mk_clock_safran_special_case 1));

  Array.set correspondance_clock_safran 23 (Some (mk_clock_safran 1 0 false));
  Array.set correspondance_clock_safran 24 (Some (mk_clock_safran 2 0 false));
  Array.set correspondance_clock_safran 25 (Some (mk_clock_safran 2 1 false));
  Array.set correspondance_clock_safran 26 (Some (mk_clock_safran 4 1 false));
  Array.set correspondance_clock_safran 27 (Some (mk_clock_safran 4 2 false));
  Array.set correspondance_clock_safran 28 (Some (mk_clock_safran 4 3 false));
  Array.set correspondance_clock_safran 29 (Some (mk_clock_safran 8 0 false));
  Array.set correspondance_clock_safran 30 (Some (mk_clock_safran 8 2 false));
  Array.set correspondance_clock_safran 31 (Some (mk_clock_safran 8 3 false));
  Array.set correspondance_clock_safran 32 (Some (mk_clock_safran 8 4 false));
  Array.set correspondance_clock_safran 33 (Some (mk_clock_safran 16 1 false));
  Array.set correspondance_clock_safran 34 (Some (mk_clock_safran 16 2 false));
  Array.set correspondance_clock_safran 35 (Some (mk_clock_safran 16 3 false));
  Array.set correspondance_clock_safran 36 (Some (mk_clock_safran 16 4 false));
  Array.set correspondance_clock_safran 37 (Some (mk_clock_safran 16 9 false));
  Array.set correspondance_clock_safran 38 (Some (mk_clock_safran_special_case 2));
  Array.set correspondance_clock_safran 39 (Some (mk_clock_safran 16 8 true));
  Array.set correspondance_clock_safran 40 (Some (mk_clock_safran 16 11 true));
  Array.set correspondance_clock_safran 41 None         (* None = never used as a clock *)



(* Name of the sequenceur for the Safran usecase (AS) *)
let name_seq_call = "wfz02_00_seq"

(* Auxilliary function which extract the list of variable id from a pattern *)
let rec get_list_vid plhs = match plhs with
  | Etuplepat pl -> List.fold_left (fun acc p1 -> acc@(get_list_vid p1)) [] pl
  | Evarpat vid -> vid::[]

let find_seq_call_eq bl =
  (* Fill the correspondance array now (because it's the initialization) *)
  fill_correspondance_clock_array ();

  (* Search for the equation corresponding to the sequenceur *)
  let plhsargsOpt = List.fold_left (fun acc eq -> match eq.eq_desc with
      | Eeq (plhs, rhs) ->
        begin
        match rhs.e_desc with
        | Eapp (a, el, _) -> begin
            match a.a_op with
              | Efun (f,_) | Enode (f,_) ->
                if (f.name = name_seq_call) then Some (plhs,el) else acc
              | _ -> acc
            end
          | _ -> acc
        end
      | _ -> raise Equation_not_in_Eeq_form
  ) None bl.b_equs in
  let (plhs, args) = match plhsargsOpt with
    | None -> raise Sequenceur_call_not_found
    | Some plhsargs -> plhsargs
  in
  
  (* We match the name of the variable to the corresponding clock *)
  let htblClocks = Hashtbl.create 43 in

  (* Matching the first argument of the sequenceur call *)
  let baseclockvarexp = List.hd args in
  let baseclockvarid = match baseclockvarexp.e_desc with
    | Evar vid -> vid
    | _ -> failwith "Unexpected form of the first argument of the sequencer call"
  in
  Hashtbl.add htblClocks baseclockvarid base_clock;

  (* Matching the outputs of the sequenceur call*)
  let lvidOut = get_list_vid plhs in
  List.iteri (fun k vid ->
    match correspondance_clock_safran.(k) with
     | None -> ()
     | Some ck -> Hashtbl.add htblClocks vid ck
    ) lvidOut;
  htblClocks



(* Name of the sequenceur for the ecas usecase *)
let name_ecas_seq = ""


(* TODO *)





(* ================================================================================ *)

(* [[a0, a1, ...], [b0, b1, ...], ...] => [[a0, b0, ...], [a1, b1, ...], ...] *)
let transpose_list_list lle =
  let rec create_n_empty_list n = match n with
    | 0 -> []
    | _ -> []::(create_n_empty_list (n-1))
  in
  let rec transpose_list_list_aux lle nRow = match lle with
  | [] -> create_n_empty_list nRow
  | hl::tl ->
    let llres = transpose_list_list_aux tl nRow in
    List.map2 (fun helem lres -> helem::lres) hl llres
  in
  if (lle=[]) then [] else
  transpose_list_list_aux lle (List.length (List.hd lle))

(* Find vid in the 3 HashTbls *)
let search_var_ident varTables vid =
  let (varTblIn, varTblOut, varTblLoc) = varTables in
  try Hashtbl.find varTblIn vid
  with Not_found ->
    (try Hashtbl.find varTblOut vid
    with Not_found ->
      (try Hashtbl.find varTblLoc vid
       with Not_found ->
          Format.fprintf (Format.formatter_of_out_channel stdout)
            "Variable not found : %s\n@?" (Idents.name vid);
          raise VariableNotFoundInHashTbl
      )
    )

(* Separate the last element of a list with the rest *)
let rec split_end_list l = match l with
  | [] -> raise Empty_list
  | a::[] -> ([],a)
  | a::r ->
    let (hl,e) = split_end_list r in
    (a::hl,e)

(* Copy n times an element
   Note: not valid if there is mutable inside x *)
let rec copy_n_times n x = match n with
  | 0 -> []
  | _ -> x::(copy_n_times (n-1) x)

let rec list_map3 f l1 l2 l3 = match (l1, l2, l3) with
  | ([],[],[]) -> []
  | (h1::t1, h2::t2, h3::t3) ->
    let h4 = f h1 h2 h3 in
    h4::(list_map3 f t1 t2 t3)
  | _ -> failwith "list_map3 : uneven list size"

(* Produce a static expression "0" (for the left size of a fby) of type "ty" *)
(*let tyAliasInfoRef = ref []
let rec find_aliasInfo tyAliasInfo strTyid = match tyAliasInfo with
  | [] -> None
  | (nty, ty)::r ->
    if (strTyid = nty.name) then Some ty
    else find_aliasInfo r strTyid *)

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

      (* TODO: do it in a cleaner way (using the type declarations) *)


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


let rec extract_ty_elem t = match t with
  | Tprod lty -> lty
  | _ -> failwith "extract_ty_elem : type is not a Tprod"


(* DEBUG *)
let verbose_duplEq = false

(* Note: result is a list of size "num_period", corresponding to all version
   of the current equation part *)
let rec edesc_duplEq varTables lvardec htblClocks lplhs edesc = match edesc with
  | Efby (e1, e2) ->
    (* Special case - produce [e1_0 fby e2_(num_period-1); e2_0; e2_(num_period-2)] *)
    let le1 = exp_duplEq varTables lvardec htblClocks lplhs (e1:Heptagon.exp) in
    let le2 = exp_duplEq varTables lvardec htblClocks lplhs e2 in
    let e1_0 = List.hd le1 in
    let (le2_begin, e2_end) = split_end_list le2 in
    let fby_exp_0 = Efby (e1_0, e2_end) in
    let ledesc2_begin = List.map (fun e -> e.e_desc) le2_begin in
    fby_exp_0::ledesc2_begin

  | Epre (None, _) ->
      Format.eprintf "PreShouldNotAppearHere : edesc = %a\n@?" Hept_printer.print_exp_desc edesc;
      raise PreShouldNotAppearHere (* Everybody in on the base clock => should not appear *)
  | Epre (Some se1, e2) -> (* Same than Efby( Econst se1, e2) *)
    let le2 = exp_duplEq varTables lvardec htblClocks lplhs e2 in
    let (le2_begin, e2_end) = split_end_list le2 in
    let pre_exp_0 = Epre (Some se1, e2_end) in
    let ledesc2_begin = List.map (fun e -> e.e_desc) le2_begin in
    pre_exp_0::ledesc2_begin

  | Evar v ->
    let lvardec = search_var_ident varTables v in
    let ledesc = List.map (fun vd -> Evar vd.v_ident) lvardec in
    ledesc
  
  (* The rest of the cases are just propagation *)
  | Econst sexp ->
    let lsexp = copy_n_times num_period sexp in
    let ledesc = List.map (fun stexp -> Econst stexp) lsexp in
    ledesc
  | Elast v ->
    let lvardec = search_var_ident varTables v in
    let ledesc = List.map (fun vd -> Elast vd.v_ident) lvardec in
    ledesc
  | Estruct lfname_exp ->
    let llexp = List.map
      (fun (_, e) -> exp_duplEq varTables lvardec htblClocks lplhs e) lfname_exp in
    let llexp_Transp = transpose_list_list llexp in
    let ledesc = List.map (fun lexp_Transp ->
          let nlfname_exp = List.map2 
            (fun (fname, _) exp -> (fname, exp))
            lfname_exp lexp_Transp in
          Estruct nlfname_exp
       ) llexp_Transp in
    ledesc
  | Ewhen (e, cname, vid) ->
    let le = exp_duplEq varTables lvardec htblClocks lplhs e in
    let lvid = search_var_ident varTables vid in
    let ledesc = List.map2 (fun ne nvid ->
      Ewhen (ne, cname, nvid.v_ident)
    ) le lvid in
    ledesc
  | Emerge (vid, lcname_e) ->
    let lvid = search_var_ident varTables vid in
    let llexp = List.map
      (fun (_, e) -> exp_duplEq varTables lvardec htblClocks lplhs e)
      lcname_e in
    let llexp_Trans = transpose_list_list llexp in
    let lledesc_right = List.map (fun lexp_Transp ->
        let nlcname_e = List.map2
          (fun (cname, _) exp -> (cname, exp))
          lcname_e lexp_Transp
        in
        nlcname_e
      ) llexp_Trans in
    let ledesc = List.map2
      (fun vid ledesc_right-> Emerge (vid.v_ident, ledesc_right))
      lvid lledesc_right
    in
    ledesc
  | Ecurrent (cname, vid, e) ->
    let lvid = search_var_ident varTables vid in
    let le = exp_duplEq varTables lvardec htblClocks lplhs e in
    let ledesc = List.map2 (fun ne nvid ->
      Ecurrent (cname, nvid.v_ident, ne)
    ) le lvid in
    ledesc
  | Esplit (e1, e2) ->
    let le1 = exp_duplEq varTables lvardec htblClocks lplhs e1 in
    let le2 = exp_duplEq varTables lvardec htblClocks lplhs e2 in
    let ledesc = List.map2 (fun ne1 ne2 ->
      Esplit (ne1, ne2)
    ) le1 le2 in
    ledesc
  | Eapp (a, le, eopt) ->
    begin
    let ledesc_elem_func_callopt = elementary_func_call_duplEq varTables lvardec htblClocks lplhs a le eopt in
    match ledesc_elem_func_callopt with
      | Some ledesc_elem_func_call -> ledesc_elem_func_call
      | None ->
        begin
        (* Default case *)
        let leopt = match eopt with
          | None -> copy_n_times num_period None
          | Some e ->
            let leSome = exp_duplEq varTables lvardec htblClocks lplhs e in
            List.map (fun eSome -> Some eSome) leSome
        in
        let lle = List.map (fun e -> exp_duplEq varTables lvardec htblClocks lplhs e) le in
        let lle_transp = transpose_list_list lle in
        let ledesc = List.map2 (fun le_transp eopt ->
          Eapp (a, le_transp, eopt)
        ) lle_transp leopt in
        ledesc
      end
    end
  | Eiterator (itype, a, lst, le1, le2, eopt) ->
    let leopt = match eopt with
      | None -> copy_n_times num_period None
      | Some e ->
        let leSome = exp_duplEq varTables lvardec htblClocks lplhs e in
        List.map (fun eSome -> Some eSome) leSome
    in
    let lle1 = List.map (fun e1 -> exp_duplEq varTables lvardec htblClocks lplhs e1) le1 in
    let lle2 = List.map (fun e2 -> exp_duplEq varTables lvardec htblClocks lplhs e2) le2 in
    let lle1_transp = transpose_list_list lle1 in
    let lle2_transp = transpose_list_list lle2 in
    let lle_tr_ziped = List.map2
      (fun le1_transp le2_transp -> (le1_transp, le2_transp))
      lle1_transp lle2_transp
    in
    let ledesc = List.map2 (fun (le1_transp, le2_transp) eopt ->
        Eiterator (itype, a, lst, le1_transp, le2_transp, eopt)
      ) lle_tr_ziped leopt in
    ledesc

(* Special function to recognize an elementary function call & to duplicate it accordingly *)
and elementary_func_call_duplEq varTables (lvardec:var_dec list) htblClocks lplhs a le eopt = match a.a_op with
  | Efun (fname,_) | Enode (fname,_) ->
    begin
    if ((fname.qual=Pervasives) || (fname.qual=LocalModule)) then None else (* External call *)

    (* Checking if the first argument is a clock *)
    let first_arg = List.hd le in
    let baseclockvarid = match first_arg.e_desc with
      | Evar vid -> vid
      | _ -> failwith "Unexpected form of the first argument - program should be in normal form"
    in
    if (not (Hashtbl.mem htblClocks baseclockvarid)) then None else begin (* First argument is not a registered clock *)
    (* Automatically, the first argument is a boolean *)

    (* At that point, we are now sure that we have an elementary function here *)
    (* We now create the list of ldesc *)
    assert(eopt=None);
    let ck = Hashtbl.find htblClocks baseclockvarid in
    let period = ck.period in
    let shift = ck.shift in
    let special_case = ck.special_case in
    let activation_vector = Array.make 16 false in
    (match special_case with
      | 1 -> (* SEQ_Idp_B : (not (InitCmpl_B)) and (OSASI_MFCnt_I = 3)) *)
        Array.set activation_vector 3 true
      | 2 -> (* SEQ_SelCcr16_4_B : (((OSASI_MFCnt_I - (S2S_Prod(OSASI_MFCnt_I , 16) * 16)) = 3) and not (InitCmpl_B))
                                        or (((OSASI_MFCnt_I - (S2S_Prod(OSASI_MFCnt_I , 16) * 16)) = 9) and InitCmpl_B) *)
        Array.set activation_vector 3 true;
        Array.set activation_vector 9 true
      | 0 -> begin (* General case *)
        Array.iteri (fun k _ ->
          if (k mod period = shift) then
            Array.set activation_vector k true
          else ()
        ) activation_vector
        end
      | _ -> failwith "Unknown special case value"
    );
    let lle1 = List.map (fun e1 -> exp_duplEq varTables lvardec htblClocks lplhs e1) le in
    let lle1_transp = transpose_list_list lle1 in
    let llvarid_out = List.map get_list_vid lplhs in
    let lvarid_out_0 = List.hd llvarid_out in
    let lty_var_out = List.map (fun vid ->
        let str_no_dupl = remove_suffix_hypexp vid in
        let vdec = search_in_lvardec str_no_dupl lvardec in
        vdec.v_type
      ) lvarid_out_0 in
    
    (* Aux function to create an expression which is the Evar/tuple of a list of variable *)
    let mk_edesc_var_or_tuple lvaridpre ltyvaridpre =
      if ((List.length lvaridpre)=1) then
        Evar (List.hd lvaridpre)
      else
        let app_tuple = { a_op = Etuple; a_params = []; a_unsafe = false; a_inlined = false } in
         let levarpre = List.map2 (fun vid tyvaridpre -> Hept_utils.mk_exp (Evar vid) tyvaridpre
            ~linearity:Linearity.Ltop) lvaridpre ltyvaridpre in 
         Eapp (app_tuple, levarpre, None)
    in

    let (ledesc,_) = Array.fold_right (fun act (acc,i) -> 
        let edesc = if (act) then
            (* Activated function *)
            Eapp (a, (List.nth lle1_transp i), None)
          else begin
            (* The function is not activated => we place a "pre" of the output variables *)
            (* NOTE! In both side of this "if" statement, the resulting expression is not normalized
               => we need to split the tuples in different equations at the eqdesc level *)
            if (i==0) then
              let lvaridpre = List.nth llvarid_out (num_period-1) in
              let subedescPre = mk_edesc_var_or_tuple lvaridpre lty_var_out in
              let tyexpPre = Types.Tprod lty_var_out in
              let expPre = Hept_utils.mk_exp subedescPre tyexpPre ~linearity:Linearity.Ltop in
              Epre(Some (init_stexp_fby tyexpPre), expPre)
            else
              let lvaridpre = List.nth llvarid_out (i-1) in
              let subedesc = mk_edesc_var_or_tuple lvaridpre lty_var_out in
              subedesc
          end in
        (edesc::acc,i-1)
      ) activation_vector ([], num_period-1) in
    Some ledesc
    end
    end
  | _ -> None

and exp_duplEq varTables lvardec htblClocks lplhs (e:Heptagon.exp) =
  if (verbose_duplEq) then
    Format.fprintf (Format.formatter_of_out_channel stdout) "*** e = %a\n@?"
      Hept_printer.print_exp e
  else ();

  let ledesc = edesc_duplEq varTables lvardec htblClocks lplhs e.e_desc in
  let lne = List.map (fun edesc ->
     let ne = Hept_utils.mk_exp edesc ~level_ck:e.e_level_ck
          ~ct_annot:None e.e_ty
          ~linearity:e.e_linearity in
     ne
  ) ledesc in
  lne


and pat_duplEq varTables htblClocks p = match p with
  | Etuplepat pl ->
    let llpl = List.map (fun p1 -> pat_duplEq varTables htblClocks p1) pl in
    let llplTransp = transpose_list_list llpl in
    let nlp = if (pl=[]) then
      copy_n_times num_period (Etuplepat [])
    else List.map (fun pl -> Etuplepat pl) llplTransp in
    nlp
  | Evarpat vid ->
    let lvardec = search_var_ident varTables vid in
    let nlp = List.map (fun vdec -> Evarpat vdec.v_ident) lvardec in
    nlp


and eqdesc_duplEq varTables lvardec htblClocks eqdesc = match eqdesc with
  | Eeq (plhs, rhs) -> 
    let (lplhs: Heptagon.pat list) = pat_duplEq varTables htblClocks plhs in
    let (lrhs: Heptagon.exp list) = exp_duplEq varTables lvardec htblClocks lplhs rhs in

    (* Detection of tuples (as output of elementary function management)
        => check the lrhs: if Epre of tuple / tuple then need to do smthing *)
    let nllEqDecs = List.map2 (fun pl er ->
      (* Check the nature of the rhs (er) *)
      let (exp_ignorePre, is_a_pre) = match er.e_desc with
        | Epre(x,epre) -> ((*assert(x=None);*) (epre, true))
        | _ -> (er, false)
      in
      let (is_not_tuple, tuple_args) = match exp_ignorePre.e_desc with
        | Eapp(a, le, _) -> begin match a.a_op with
          | Etuple -> (false, le)
          | _ -> (true, [])
        end
        | _ -> (true, [])
      in

      (* Default case -> not a tuple -> no need of normalization *)
      if (is_not_tuple) then [Eeq (pl, er)] else

      let tyTuple = er.e_ty in (* Type of the tuple *)
      let ltyTuple = extract_ty_elem tyTuple in

      (* Normalization needed: we split the tuple into several equations *)
      let l_lhsvarid = get_list_vid pl in
      assert((List.length l_lhsvarid) = (List.length tuple_args));
      let leq = list_map3 (fun lhs erhs tyElem ->
        if (is_a_pre) then
          let edescRhsPre = Epre(Some (init_stexp_fby tyElem), erhs) in
          let erhspre = Hept_utils.mk_exp edescRhsPre tyElem ~ct_annot:(Some (Clocks.Ck Clocks.Cbase))
                ~linearity:Linearity.Ltop in
          Eeq((Evarpat lhs), erhspre)
        else
          Eeq((Evarpat lhs), erhs)
      ) l_lhsvarid tuple_args ltyTuple in
      leq
    ) lplhs lrhs in
    let nlEqDecs = List.concat nllEqDecs in
    nlEqDecs
  | _ -> raise Equation_not_in_Eeq_form


and eq_duplEq varTables lvardec htblClocks eq =
  let leqdesc = eqdesc_duplEq varTables lvardec htblClocks eq.eq_desc in
  let leq = List.map
    (fun eqdesc -> Hept_utils.mk_equation eqdesc)
    leqdesc
  in
  leq



(* ================================================================================ *)
let get_all_var_decl htbl = Hashtbl.fold (fun _ v acc -> v@acc) htbl []


(* ================================================================================ *)

(* Main functions *)
let node nd =
  (* Step 0: get the equation using Wfz02_00_seq.wfz02_00_seq and put it in relation to correspondance_clock_safran *)
  let htblClocks = find_seq_call_eq nd.n_block in

  (* Step 1: creates all instances of variables *)
  let varTblIn = Hashtbl.create (List.length nd.n_input) in
  let varTblOut = Hashtbl.create (List.length nd.n_output) in
  let varTblLoc = Hashtbl.create (List.length nd.n_block.b_local) in
  
  List.iter (fun var ->
  	let lInstances = create_all_var_instances var num_period in
  	Hashtbl.add varTblIn var.v_ident lInstances
    ) nd.n_input;
  List.iter (fun var ->
  	let lInstances = create_all_var_instances var num_period in
  	Hashtbl.add varTblOut var.v_ident lInstances
    ) nd.n_output;
  List.iter (fun var ->
  	let lInstances = create_all_var_instances var num_period in
  	Hashtbl.add varTblLoc var.v_ident lInstances
    ) nd.n_block.b_local;
  let varTables = (varTblIn, varTblOut, varTblLoc) in

  (* Step 2: duplicate equations *)
  let lvardec = nd.n_input @ nd.n_output @ nd.n_block.b_local in
  let lneqs = List.fold_left (fun acc eq ->
      let nleq = eq_duplEq varTables lvardec htblClocks eq in
      nleq @ acc
    ) [] nd.n_block.b_equs in

  (* TODO: iterate over contracts also? => nContract *)
  assert(nd.n_contract=None);
  let nContract = None in

  (* Step 3: build the new system and return it *)
  let lnInputs = get_all_var_decl varTblIn in
  let lnOutputs = get_all_var_decl varTblOut in
  let lnLocals = get_all_var_decl varTblLoc in

  let nBl = {
    b_local = lnLocals;
    b_equs = lneqs;
    b_defnames = nd.n_block.b_defnames;
    b_stateful = nd.n_block.b_stateful;
    b_loc = nd.n_block.b_loc;
  } in
  let n_nd = {
    n_name = nd.n_name;
    n_stateful = nd.n_stateful;  (* if fby in nd, then true / else false *)
    n_unsafe = nd.n_unsafe;
    n_typeparamdecs = nd.n_typeparamdecs;
    n_input = lnInputs;
    n_output = lnOutputs;
    n_contract = nContract;
    n_block = nBl;
    n_loc = nd.n_loc;
    n_params = nd.n_params;
    n_param_constraints = nd.n_param_constraints;
  } in

  (* Visitor to set all level_ck to Clocks.Cbase *)
  (* let exp_clockbase funs acc exp =
    let exp, _ = Hept_mapfold.exp funs acc exp in
    let ct_annot = match exp.e_ty with
      | Tprod lty -> Clocks.Cprod (List.map (fun _ -> Clocks.Ck Clocks.Cbase) lty)
  (*  | Tarray (_,se) -> begin match se.se_desc with 
          | Sint i ->
            let lcbasei = copy_n_times i (Clocks.Ck Clocks.Cbase) in
            Clocks.Cprod lcbasei
          | _ -> failwith "Array size not an integer"
        end *)
      | _ -> Clocks.Ck Clocks.Cbase
    in
     {exp with e_level_ck = Clocks.Cbase;
               e_ct_annot = Some ct_annot
     }, acc
  in
  let var_dec_clockbase _ acc vd = {vd with v_clock = Clocks.Cbase}, acc in
  let funs_clockbase = { Hept_mapfold.defaults with
          Hept_mapfold.exp = exp_clockbase; Hept_mapfold.var_dec = var_dec_clockbase} in
  let n_nd, _ = funs_clockbase.Hept_mapfold.node_dec funs_clockbase [] n_nd in *)
  n_nd

let program p =
  (* Dirty fix to correct the type of constants *)
  (*tyAliasInfoRef := ArrayDestruct.getTyAliasInfo p; *)

  let nlpdesc = List.fold_left
  (fun acc pdesc -> match pdesc with
    | Pnode nd -> (Pnode (node nd))::acc
    | _ -> pdesc::acc
  ) [] p.p_desc in
  {p with p_desc = nlpdesc}
