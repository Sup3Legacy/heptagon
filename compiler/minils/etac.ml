let _aux_fresh index prefix hint =
  index := !index + 1;
  Printf.sprintf "%s%s__%d" prefix hint !index

let fresh_var =
  let index = ref 0 in
  _aux_fresh index "TMP"

let fresh_clk =
  let index = ref 0 in
  _aux_fresh index "TMP"

module ClockDisjonction =
  struct
    type t = string * Idents.var_ident
    let compare = Pervasives.compare
  end;;

module VarIdent =
  struct
    type t = Idents.var_ident
    let compare = Pervasives.compare
  end;;

module IdentVardecMap = Map.Make(VarIdent)
module ClockDisjonctionSet = Set.Make(ClockDisjonction)
type state_t = {
  channel: out_channel;
  written_clocks: ClockDisjonctionSet.t;
  var_dec: Minils.var_dec Idents.Env.t
}

let types_tbl = Hashtbl.create 256
let constructors_tbl = Hashtbl.create 1024

let get_type_of_constructor (constructor: Names.constructor_name) =
  Hashtbl.find constructors_tbl constructor

let add_constructor_type (c: Names.constructor_name) (t: Names.qualname) =
  Hashtbl.add constructors_tbl c t

let pervasives_bool = {Names.qual=Names.Pervasives; Names.name="bool"}
let pervasives_true = {Names.qual=Names.Pervasives; Names.name="true"}
let pervasives_false = {Names.qual=Names.Pervasives; Names.name="false"}

let _ =
  add_constructor_type pervasives_true pervasives_bool
let _ =
  add_constructor_type pervasives_false pervasives_bool
let _ =
  Hashtbl.add types_tbl pervasives_bool (Minils.Type_enum [pervasives_true; pervasives_false])


let int_of_constructor (name: Names.constructor_name) =
  let t = get_type_of_constructor name in
  match (Hashtbl.find types_tbl t) with
  | Minils.Type_enum l ->
      let rec find (i: int) = function
        | [] -> failwith "invalid constructor"
        | name2 :: _ when name = name2 -> i
        | _ :: tl -> find (i+1) tl
      in find 0 l
  | _ -> failwith "Constructor of non-enum."


(* List.map and List.fold_left in a single pass. *)
let mapfold (pred: 'a -> 'b -> ('a * 'c)) (start: 'a) (l: 'b list) =
  let aux (acc: ('a * 'c list)) (item: 'b) = (
    let (folded, mapped) = acc in
    let (new_folded, new_mapped) = (pred folded item) in
    (new_folded, new_mapped :: mapped)
  ) in
  let (folded, mapped) = (List.fold_left aux (start, []) l) in
  (folded, List.rev mapped)

let string_of_modul (modul: Names.modul) =
  let rec aux stack = function
    | Names.Pervasives -> (
        match (List.hd stack) with
        | "+" -> "add" :: (List.tl stack)
        | "~-" -> "sub 0" :: (List.tl stack)
        | "-" -> "sub" :: (List.tl stack)
        | "*" -> "mul" :: (List.tl stack)
        | "/" -> "div" :: (List.tl stack)
        | ">" -> "cmp gt" :: (List.tl stack)
        | ">=" -> "cmp ge" :: (List.tl stack)
        | "<" -> "cmp lt" :: (List.tl stack)
        | "<=" -> "cmp le" :: (List.tl stack)
        | "=" -> "cmp eq" :: (List.tl stack)
        | "<>" -> "cmp ne" :: (List.tl stack)
        | "not" -> "not" :: (List.tl stack)
        (* TODO: boolean operators *)
        | _ -> "PERVASIVES" :: stack
      )
    | Names.LocalModule -> stack
    | Names.Module name -> name :: stack
    | Names.QualModule name -> aux (name.Names.name :: stack) name.Names.qual
  in String.concat "__" (aux [] modul)

let string_of_qualname (qualname: Names.qualname) =
  string_of_modul (Names.QualModule qualname)

let string_of_varident (varident: Idents.var_ident) =
  Printf.sprintf "%s" (Idents.name varident)

let string_of_vardec (with_type: bool) (vardec: Minils.var_dec) =
  (* TODO: handle types *)
  if with_type then
    String.concat "" ["i64 %"; string_of_varident vardec.Minils.v_ident]
  else
    string_of_varident vardec.Minils.v_ident

let ck_name_from_constructor state (base_ck: string) (constructor: Names.qualname) (var: Minils.var_dec) =
  let formatter cstr var =
    Printf.sprintf "%s___%s_%s" base_ck (string_of_qualname cstr) (string_of_varident var)
  in
  let new_state = (
    if ClockDisjonctionSet.mem (base_ck, var.Minils.v_ident) state.written_clocks then
      state
    else (
      let tname = Hashtbl.find constructors_tbl constructor in
      let t = Hashtbl.find types_tbl tname in (
      match t with
      | Minils.Type_enum constructors ->
          let pred i cstr = (
            let name = (formatter cstr var.Minils.v_ident) in
            let tmpimm = fresh_var "imm" in
            Printf.fprintf state.channel "  i64 %%%s = li %d when ?%s\n" tmpimm i base_ck;
            Printf.fprintf state.channel "  i1 %%%s = cmp eq %%%s, %%%s when ?%s\n" name (string_of_vardec false var) tmpimm base_ck;
            Printf.fprintf state.channel "  ?%s is %%%s\n" name name;
            (i+1, name)
          ) in
          let (_, clocks) = mapfold pred 0 constructors in
          Printf.fprintf state.channel "  ?%s <=> ?%s\n" base_ck (String.concat " | ?" clocks);
          { state with written_clocks=ClockDisjonctionSet.add (base_ck, var.Minils.v_ident) state.written_clocks }
      | _ -> failwith "Unsupported type"
      )
    )
  ) in
  (new_state, formatter constructor (var.Minils.v_ident))

let rec push_static_exp state ck (sexp: Types.static_exp) =
  push_static_exp_desc state ck sexp.Types.se_desc

and push_static_exp_desc state ck = function
  | Types.Svar name -> (state, name)
  | Types.Sint i ->
      let tmpvar = (fresh_var "imm") in
      Printf.fprintf state.channel "  i64 %%%s = li %d when ?%s\n" tmpvar i ck;
      (state, {Names.qual=Names.LocalModule; Names.name=tmpvar})
  | Types.Sop (f_name, args) ->
      let (state, args) = mapfold (fun state arg -> push_static_exp state ck arg) state args in
      let args = (String.concat ", %%" (List.map string_of_qualname args)) in
      let tmpvar = (fresh_var "sexp") in
      Printf.fprintf state.channel "  i64 %%%s = %s %%%s when ?%s\n" tmpvar (string_of_qualname f_name) args ck;
      (state, {Names.qual=Names.LocalModule; Names.name=tmpvar})
  | _ -> failwith "static_exp_desc constructor not handled" (* TODO *)

let rec string_of_pat = function
  (* FIXME: not tail-recursive *)
  | Minils.Evarpat var_ident ->
      String.concat "" ["i64 %"; string_of_varident var_ident]
  | Minils.Etuplepat pats ->
      Printf.sprintf "%%%s" (String.concat ", %" (List.map string_of_pat pats))

and push_eq (state: state_t) base_clk (eq: Minils.eq) =
  push_exp state base_clk (string_of_pat eq.Minils.eq_lhs) eq.Minils.eq_rhs

and push_exp (state: state_t) base_clk (lhs: string) (exp: Minils.exp) =
  match exp.Minils.e_desc with
  | Minils.Eextvalue ev ->
      let (state, res) = push_extvalue state base_clk ev in
      Printf.fprintf state.channel "  i64 %%%s = sample %%%s when ?%s\n" lhs (string_of_varident res) base_clk;
      state
  | Minils.Eapp (app, evs, None) ->
      let (state, params) = (mapfold (fun state arg -> push_extvalue state base_clk arg) state evs) in
      push_app state lhs params app
  | Minils.Ewhen (exp, constructor, varident) ->
      let exp_res = fresh_var "res" in
      let state = push_exp state base_clk exp_res exp in
      let var = Idents.Env.find varident state.var_dec in
      let (state, clk) = (ck_name_from_constructor state base_clk constructor var) in
      Printf.fprintf state.channel "  %s = sample %%%s when ?%s\n" lhs exp_res clk;
      state
  | Minils.Emerge (var, l) ->
      let pred state (cstr, exp) = (
        let (state, clk) = ck_name_from_constructor state base_clk cstr (Idents.Env.find var state.var_dec) in
        push_extvalue state clk exp
      ) in
      let (state, variables) = mapfold pred state l in
      Printf.fprintf state.channel "  %s = phi %%%s when ?%s\n" lhs (String.concat ", %" (List.map string_of_varident variables)) base_clk;
      state
  | _ -> failwith "edesc constructor not handled" (* TODO *)

and push_app (state: state_t) (lhs: string) (params: Idents.ident list) (app: Minils.app) =
  match app.Minils.a_op with
  | Minils.Efun f ->
      Printf.fprintf state.channel "%s = %s %%%s" lhs (string_of_qualname f) (String.concat ", %" (List.map string_of_varident params));
      state
  | Minils.Eifthenelse -> (
      match params with [cond; iftrue; iffalse] -> (
        let tmptrue = fresh_var "iftrue" in
        let tmpfalse = fresh_var "iffalse" in
        let conddec = Idents.Env.find cond state.var_dec in
        let (state, trueclk) = ck_name_from_constructor state "?top" pervasives_true conddec in
        let (state, falseclk) = ck_name_from_constructor state "?top" pervasives_false conddec in
        Printf.fprintf state.channel "  i64 %%%s = sample %%%s when ?%s\n"
            tmptrue (string_of_varident iftrue) trueclk;
        Printf.fprintf state.channel "  i64 %%%s = sample %%%s when ?%s\n"
            tmpfalse (string_of_varident iffalse) falseclk;
        Printf.fprintf state.channel "  i64 %%%s = phi %%%s, %%%s\n" lhs tmptrue tmpfalse;
        state
      )
      | _ -> failwith "bad list of params"
  )
  | _ -> failwith "op constructor not handled>" (* TODO *)

and push_extvalue state ck (ev: Minils.extvalue) =
  push_extvaluedesc state ck ev.Minils.w_desc

and push_extvaluedesc state ck = function
  | Minils.Wvar varident -> (state, varident)
  | Minils.Wconst sexp ->
      let (state, name) = push_static_exp state ck sexp in
      (state, Idents.ident_of_name (string_of_qualname name))
  | _ -> failwith "extvaluedesc constructor not handled" (* TODO *)

let rec push_ck state = function
  (* FIXME: not tail-recursive *)
  | Clocks.Cbase -> (state, "top")
  | Clocks.Cvar link -> push_link state !link
  | Clocks.Con (base_ck, constructor, varident) ->
      let (state, base_ck) = push_ck state base_ck in
      let var = Idents.Env.find varident state.var_dec in
      ck_name_from_constructor state base_ck constructor var

and push_link state = function
  | Clocks.Cindex i -> (state, Printf.sprintf "%d" i)
  | Clocks.Clink ck -> push_ck state ck (* XXX: Is it right? *)

let push_eq state (eq: Minils.eq) =
  (* TODO: handle types *)
  let (state, ck) = (push_ck state eq.Minils.eq_base_ck) in
  let state = push_eq state ck eq in
  state

let push_var_init state (var: Minils.var_dec) =
  let state = { state with var_dec = Idents.Env.add var.Minils.v_ident var state.var_dec } in
  match var.Minils.v_type with
  | Types.Tid {Names.qual=Names.Pervasives; Names.name="float"}
  | Types.Tid {Names.qual=Names.Pervasives; Names.name="bool"}
  | Types.Tid {Names.qual=Names.Pervasives; Names.name="int"} -> state
  | Types.Tid t when Hashtbl.mem types_tbl t -> state (* Will be initialized when needed *)
  | Types.Tid t  -> failwith (Printf.sprintf "Undefined type %s." (string_of_qualname t))
  | _ -> failwith "Unsupported type."

let node_pred file (node: Minils.node_dec) =
  (* Print node name *)
  Printf.fprintf file "node @%s__%s {\n"
      (string_of_modul node.Minils.n_name.Names.qual)
      node.Minils.n_name.Names.name;

  let state = {channel=file; written_clocks=ClockDisjonctionSet.empty; var_dec=Idents.Env.empty} in

  let all_var_dec = node.Minils.n_output @ node.Minils.n_input @ node.Minils.n_local in
  let state = List.fold_left push_var_init state all_var_dec in

  (* Print inputs *)
  (match List.map (string_of_vardec true) node.Minils.n_input with
  | [] -> Printf.fprintf file "  init\n"
  | inputs -> Printf.fprintf file "  %s = init\n" (String.concat ", " inputs)
  );

  (* Print equations *)
  ignore (List.fold_left (push_eq) state node.Minils.n_equs);

  (* Print outputs *)
  let outputs = List.map (string_of_vardec false) node.Minils.n_output in
  Printf.fprintf file "  exit %%%s\n" (String.concat ", %" outputs);

  (* Print end of node *)
  Printf.fprintf file "}\n"

let program_pred file (p: Minils.program_desc) = match p with
  | Minils.Pnode node -> node_pred file node
  | Minils.Pconst _ -> Printf.printf "const not supported\n"
  | Minils.Ptype t -> (
      match t.Minils.t_desc with
      | Minils.Type_enum l -> ignore (
          List.map (fun c -> add_constructor_type c t.Minils.t_name) l)
      | _ -> failwith "Unsupported type"
      );
      Hashtbl.add types_tbl t.Minils.t_name t.Minils.t_desc

let program (p: Minils.program) =
  let filename = (String.uncapitalize (Names.modul_to_string p.Minils.p_modname)) ^".etac" in
  let file = open_out_bin filename in
  ignore (List.map (program_pred file) p.Minils.p_desc);
  close_out file;
