(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(* removing switch statements and translation into Minils *)

open Location
open Misc
open Names
open Name_utils
open Idents
open Static
open Signature
open Clocks
open Format

open Minils
open Mls_utils
open Signature

module Error =
struct
  type error =
    | Ereset_not_var
    | Eunsupported_language_construct
    | Enormalization

  let message loc kind =
    begin match kind with
      | Ereset_not_var ->
          eprintf "%aOnly variables can be used for resets.@."
            print_location loc
      | Eunsupported_language_construct ->
          eprintf "%aThis construct is not supported by MiniLS.@."
            print_location loc
      | Enormalization ->
          eprintf "%aThis construct should have been normalized.@."
            print_location loc
    end;
    raise Errors.Error
end

let fresh v =
  let s = match v with
    | Heptagon.Enode f -> (shortname f)
    | _ -> "n"
  in
  Idents.gen_var "hept2mls" ~reset:false s

(* This function set every variable with v_is_memory=false,
   this is corrected at the end of the pass *)
let translate_var { Heptagon.v_ident = n; Heptagon.v_type = ty; Heptagon.v_linearity = linearity;
                    Heptagon.v_loc = loc; Heptagon.v_clock = ck } =
  mk_var_dec ~loc:loc n ty ~is_memory:false linearity ck

let translate_reset = function
  | Some { Heptagon.e_desc = Heptagon.Evar n } -> Some n
  | Some re -> Error.message re.Heptagon.e_loc Error.Ereset_not_var
  | None -> None

let translate_iterator_type = function
  | Heptagon.Imap -> Imap
  | Heptagon.Imapi -> Imapi
  | Heptagon.Ifold -> Ifold
  | Heptagon.Ifoldi -> Ifoldi
  | Heptagon.Imapfold -> Imapfold

let rec translate_op = function
  | Heptagon.Eifthenelse -> Eifthenelse
  | Heptagon.Efun f -> Efun f
  | Heptagon.Enode f -> Enode f
  | Heptagon.Efield -> assert false
  | Heptagon.Efield_update -> Efield_update
  | Heptagon.Earray_fill -> Earray_fill
  | Heptagon.Eselect -> Eselect
  | Heptagon.Eselect_dyn -> Eselect_dyn
  | Heptagon.Eupdate -> Eupdate
  | Heptagon.Eselect_slice -> Eselect_slice
  | Heptagon.Eselect_trunc -> Eselect_trunc
  | Heptagon.Econcat -> Econcat
  | Heptagon.Earray -> Earray
  | Heptagon.Etuple -> Misc.internal_error "hept2mls Etuple"
  | Heptagon.Earrow -> assert false
  | Heptagon.Ereinit -> assert false
  | Heptagon.Ebang -> Ebang

let translate_app app =
  mk_app ~params:app.Heptagon.a_params ~async:app.Heptagon.a_async
    ~unsafe:app.Heptagon.a_unsafe
    ~id:(Some (fresh app.Heptagon.a_op))
    (translate_op app.Heptagon.a_op)

let mk_extvalue e w =
  let clock = match e.Heptagon.e_ct_annot with
    | None -> fresh_clock ()
    | Some ct -> assert_1 (Clocks.unprod ct)
  in
  mk_extvalue ~loc:e.Heptagon.e_loc ~linearity:e.Heptagon.e_linearity
    ~ty:e.Heptagon.e_ty ~clock:clock w


let rec translate_extvalue e =
  match e.Heptagon.e_desc with
    | Heptagon.Econst c -> mk_extvalue e (Wconst c)
    | Heptagon.Evar x -> mk_extvalue e (Wvar x)
    | Heptagon.Ewhen (e, c, x) ->
        mk_extvalue e (Wwhen (translate_extvalue e, c, x))
    | Heptagon.Eapp({ Heptagon.a_op = Heptagon.Efield;
                      Heptagon.a_params = params }, e_list, _) ->
        let e' = assert_1 e_list in
        let f = assert_1 params in
        let fn = match f.se_desc with Sfield fn -> fn | _ -> assert false in
          mk_extvalue e (Wfield (translate_extvalue e', fn))
    | Heptagon.Eapp({ Heptagon.a_op = Heptagon.Ereinit }, e_list, _) ->
        let e1, e2 = assert_2 e_list in
          mk_extvalue e (Wreinit (translate_extvalue e1, translate_extvalue e2))
    | _ -> Error.message e.Heptagon.e_loc Error.Enormalization

let rec translate ({ Heptagon.e_desc = desc; Heptagon.e_ty = ty;
                 Heptagon.e_level_ck = b_ck; Heptagon.e_linearity = linearity;
                 Heptagon.e_ct_annot = a_ct; Heptagon.e_loc = loc;  } as e) =
  let desc = match desc with
    | Heptagon.Econst _
    | Heptagon.Evar _
    | Heptagon.Eapp({ Heptagon.a_op = Heptagon.Efield | Heptagon.Ereinit }, _, _) ->
        let w = translate_extvalue e in
        Eextvalue w
    | Heptagon.Ewhen (e,c,x) -> Ewhen (translate e, c, x)
    | Heptagon.Epre(None, e) ->
        Efby(None, translate_extvalue e)
    | Heptagon.Epre(Some c, e) ->
        Efby(Some c, translate_extvalue e)
    | Heptagon.Efby ({ Heptagon.e_desc = Heptagon.Econst c }, e) ->
        Efby(Some c, translate_extvalue e)
    | Heptagon.Estruct f_e_list ->
        let f_e_list = List.map
          (fun (f, e) -> (f, translate_extvalue e)) f_e_list in
        Estruct f_e_list
    | Heptagon.Eapp({ Heptagon.a_op = Heptagon.Earrow }, _, _) ->
        Misc.internal_error "Hept2mls : Earrow still present"
    | Heptagon.Eapp(app, e_list, reset) ->
        Eapp (translate_app app, List.map translate_extvalue e_list, translate_reset reset)
    | Heptagon.Eiterator(it, app, n, pe_list, e_list, reset) ->
        Eiterator (translate_iterator_type it,
                   translate_app app, n,
                   List.map translate_extvalue pe_list,
                   List.map translate_extvalue e_list,
                   translate_reset reset)
    | Heptagon.Efby _ -> Misc.internal_error "Hept2mls : Efby still present"
    | Heptagon.Elast _ -> Misc.internal_error "Hept2mls : Elast still present"
    | Heptagon.Esplit _ -> Misc.internal_error "Hept2mls : Esplit still present"
    | Heptagon.Emerge (x, c_e_list) ->
        Emerge (x, List.map (fun (c,e)-> c, translate_extvalue e) c_e_list)
  in
  match a_ct with
    | None -> mk_exp b_ck ty ~loc:loc ~linearity:linearity desc
    | Some ct -> mk_exp b_ck ty ~ct:ct ~loc:loc ~linearity:linearity desc



let rec translate_pat = function
  | Heptagon.Evarpat(n) -> Evarpat n
  | Heptagon.Etuplepat(l) -> Etuplepat (List.map translate_pat l)

let rec translate_eq { Heptagon.eq_desc = desc; Heptagon.eq_loc = loc } =
  match desc with
    | Heptagon.Eeq(p, e) ->
        begin match e.Heptagon.e_desc with
          | Heptagon.Eapp({ Heptagon.a_unsafe = unsafe },_,_)
          | Heptagon.Eiterator(_,{ Heptagon.a_unsafe = unsafe},_,_,_,_) ->
              mk_equation ~loc:loc unsafe (translate_pat p) (translate e)
          | _ -> mk_equation ~loc:loc false (translate_pat p) (translate e)
        end
    | Heptagon.Eblock _ | Heptagon.Eswitch _
    | Heptagon.Epresent _ | Heptagon.Eautomaton _ | Heptagon.Ereset _ ->
        Error.message loc Error.Eunsupported_language_construct

let translate_contract contract =
  match contract with
    | None -> None
    | Some { Heptagon.c_block = { Heptagon.b_local = v;
                                  Heptagon.b_equs = eq_list };
             Heptagon.c_assume = e_a;
             Heptagon.c_enforce = e_g;
             Heptagon.c_controllables = l_c } ->
        Some { c_local = List.map translate_var v;
               c_eq = List.map translate_eq eq_list;
               c_assume = translate_extvalue e_a;
               c_enforce = translate_extvalue e_g;
               c_controllables = List.map translate_var l_c }

let node n =
  Idents.push_node n.Heptagon.n_name;
  let n = Is_memory.update_node
    { n_name = n.Heptagon.n_name;
      n_stateful = n.Heptagon.n_stateful;
      n_unsafe = n.Heptagon.n_unsafe;
      n_input = List.map translate_var n.Heptagon.n_input;
      n_output = List.map translate_var n.Heptagon.n_output;
      n_contract = translate_contract n.Heptagon.n_contract;
      n_controller_call = ([],[]);
      n_local = List.map translate_var n.Heptagon.n_block.Heptagon.b_local;
      n_equs = List.map translate_eq n.Heptagon.n_block.Heptagon.b_equs;
      n_loc = n.Heptagon.n_loc ;
      n_params = n.Heptagon.n_params;
      n_param_constraints = n.Heptagon.n_param_constraints;
      n_mem_alloc = [];
      n_base_ck = Clocks.Cbase;
      n_base_id = None }
  in
  let _ = Idents.pop_node () in
  n


let typedec
    {Heptagon.t_name = n; Heptagon.t_desc = tdesc; Heptagon.t_loc = loc} =
  let onetype = function
    | Heptagon.Type_abs -> Type_abs
    | Heptagon.Type_alias ln -> Type_alias ln
    | Heptagon.Type_enum tag_list -> Type_enum tag_list
    | Heptagon.Type_struct field_ty_list -> Type_struct field_ty_list
  in
  { t_name = n; t_desc = onetype tdesc; t_loc = loc }

let const_dec cd =
  { Minils.c_name = cd.Heptagon.c_name;
    Minils.c_value = cd.Heptagon.c_value;
    Minils.c_type = cd.Heptagon.c_type;
    Minils.c_loc = cd.Heptagon.c_loc; }

let program_desc pd = match pd with
  | Heptagon.Ptype td -> Ptype (typedec td)
  | Heptagon.Pnode nd -> Pnode (node nd)
  | Heptagon.Pconst cd -> Pconst (const_dec cd)

let program
    { Heptagon.p_modname = modname;
      Heptagon.p_opened = modules;
      Heptagon.p_desc = desc_list } =
  { p_modname = modname;
    p_format_version = minils_format_version;
    p_opened = modules;
    p_desc = List.map program_desc desc_list }

let signature s =
  { sig_name = s.Heptagon.sig_name;
    sig_sig = s.Heptagon.sig_sig}

let interface i =
  let interface_decl id = match id with
    | Heptagon.Itypedef td -> Itypedef (typedec td)
    | Heptagon.Iconstdef cd -> Iconstdef (const_dec cd)
    | Heptagon.Isignature s -> Isignature (signature s)
  in
  { i_modname = i.Heptagon.i_modname;
    i_opened = i.Heptagon.i_opened;
    i_desc = List.map interface_decl i.Heptagon.i_desc }
