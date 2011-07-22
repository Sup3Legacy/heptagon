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
open Idents
open Static
open Types
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


let translate_var { Heptagon.v_ident = n; Heptagon.v_type = ty;
                    Heptagon.v_loc = loc; Heptagon.v_clock = ck;
                    Heptagon.v_mem = mem } =
  mk_var_dec ~loc:loc ~mem:mem n ty ck

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
  | Heptagon.Ipmap -> Ipmap
  | Heptagon.Ipmapi -> Ipmapi

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

let translate_app app =
  mk_app ~params:app.Heptagon.a_params
    ~unsafe:app.Heptagon.a_unsafe (translate_op app.Heptagon.a_op)

let rec translate_extvalue e =
  let mk_extvalue = mk_extvalue ~loc:e.Heptagon.e_loc ~ty:e.Heptagon.e_ty in
  match e.Heptagon.e_desc with
    | Heptagon.Econst c -> mk_extvalue (Wconst c)
    | Heptagon.Evar x -> mk_extvalue (Wvar x)
    | Heptagon.Ewhen (e, c, x) ->
        mk_extvalue (Wwhen (translate_extvalue e, c, x))
    | Heptagon.Eapp({ Heptagon.a_op = Heptagon.Efield;
                      Heptagon.a_params = params }, e_list, _) ->
        let e = assert_1 e_list in
        let f = assert_1 params in
        let fn = match f.se_desc with Sfield fn -> fn | _ -> assert false in
          mk_extvalue (Wfield (translate_extvalue e, fn))
    | _ -> Error.message e.Heptagon.e_loc Error.Enormalization

let rec translate ({ Heptagon.e_desc = desc; Heptagon.e_ty = ty; Heptagon.e_level_ck = b_ck;
                 Heptagon.e_ct_annot = a_ct; Heptagon.e_loc = loc } as e) =
  let desc = match desc with
    | Heptagon.Econst _
    | Heptagon.Evar _
    | Heptagon.Eapp({ Heptagon.a_op = Heptagon.Efield }, _, _) ->
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
         Error.message loc Error.Eunsupported_language_construct
    | Heptagon.Eapp(app, e_list, reset) ->
        Eapp (translate_app app, List.map translate_extvalue e_list, translate_reset reset)
    | Heptagon.Eiterator(it, app, n, pe_list, e_list, reset) ->
        Eiterator (translate_iterator_type it,
                    translate_app app, n,
                    List.map translate_extvalue pe_list,
                    List.map translate_extvalue e_list,
                    translate_reset reset)
    | Heptagon.Efby _
    | Heptagon.Elast _ ->
        Error.message loc Error.Eunsupported_language_construct
    | Heptagon.Emerge (x, c_e_list) ->
        Emerge (x, List.map (fun (c,e)-> c, translate_extvalue e) c_e_list)
  in
  match a_ct with
    | None -> mk_exp b_ck ty ~loc:loc desc
    | Some ct -> mk_exp b_ck ty ~ct:ct ~loc:loc desc



let rec translate_pat = function
  | Heptagon.Evarpat(n) -> Evarpat n
  | Heptagon.Etuplepat(l) -> Etuplepat (List.map translate_pat l)

let rec translate_eq
    { Heptagon.eq_desc = desc; Heptagon.eq_loc = loc } =
  match desc with
    | Heptagon.Eeq(p, e) ->
        mk_equation ~loc:loc (translate_pat p) (translate e)
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
  { n_name = n.Heptagon.n_name;
    n_stateful = n.Heptagon.n_stateful;
    n_input = List.map translate_var n.Heptagon.n_input;
    n_output = List.map translate_var n.Heptagon.n_output;
    n_contract = translate_contract n.Heptagon.n_contract;
    n_local = List.map translate_var n.Heptagon.n_block.Heptagon.b_local;
    n_equs = List.map translate_eq n.Heptagon.n_block.Heptagon.b_equs;
    n_loc = n.Heptagon.n_loc ;
    n_params = n.Heptagon.n_params;
    n_param_constraints = n.Heptagon.n_param_constraints;
    n_gpu = n.Heptagon.n_gpu }

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
