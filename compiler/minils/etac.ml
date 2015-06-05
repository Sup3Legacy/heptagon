let string_of_modul (modul: Names.modul) =
  let rec aux stack = function
    | Names.Pervasives -> (
        match (List.hd stack) with
        | "+" -> "add" :: (List.tl stack)
        | "-" -> "sub" :: (List.tl stack)
        | "*" -> "mul" :: (List.tl stack)
        | "/" -> "div" :: (List.tl stack)
        (* TODO: binary operators *)
        | _ -> "PERVASIVES" :: stack
      )
    | Names.LocalModule -> "LOCALMODULE" :: stack
    | Names.Module name -> name :: stack
    | Names.QualModule name -> aux (name.Names.name :: stack) name.Names.qual
  in String.concat "__" (aux [] modul)

let string_of_qualname (qualname: Names.qualname) =
  string_of_modul (Names.QualModule qualname)

let string_of_varident (varident: Idents.var_ident) =
  Printf.sprintf "%%%s" (Idents.name varident)

let string_of_vardec (with_type: bool) (vardec: Minils.var_dec) =
  (* TODO: handle types *)
  if with_type then
    String.concat " " ["i64"; string_of_varident vardec.Minils.v_ident]
  else
    string_of_varident vardec.Minils.v_ident

let rec string_of_static_exp (sexp: Types.static_exp) =
  string_of_static_exp_desc sexp.Types.se_desc

and string_of_static_exp_desc = function
  | Types.Svar name -> string_of_qualname name
  | Types.Sint i -> string_of_int i
  | _ -> "<static_exp_desc constructor not handled>" (* TODO *)

let rec string_of_pat = function
  (* FIXME: not tail-recursive *)
  | Minils.Evarpat var_ident ->
      String.concat " " ["i64"; string_of_varident var_ident]
  | Minils.Etuplepat pats ->
      Printf.sprintf "%s" (String.concat ", " (List.map string_of_pat pats))

let rec string_of_exp (exp: Minils.exp)  =
  string_of_edesc exp.Minils.e_desc

and string_of_edesc = function
  | Minils.Eextvalue ev -> string_of_extvalue ev
  | Minils.Eapp (app, evs, None) ->
      Printf.sprintf "%s %s"
          (string_of_app app)
          (String.concat ", " (List.map string_of_extvalue evs))
  | Minils.Eapp (app, evs, Some varident) ->
      Printf.sprintf "%s %s(%s)"
          (string_of_app app)
          (String.concat ", " (List.map string_of_extvalue evs))
          (string_of_varident varident)
  | _ -> "<edesc constructor not handled>" (* TODO *)

and string_of_app (app: Minils.app) =
  match app.Minils.a_op with
  | Minils.Efun f -> string_of_qualname f
  | _ -> "<op constructor not handled>" (* TODO *)

and string_of_extvalue (ev: Minils.extvalue) =
  string_of_extvaluedesc ev.Minils.w_desc

and string_of_extvaluedesc = function
  | Minils.Wvar varident -> string_of_varident varident
  | Minils.Wconst sexp -> string_of_static_exp sexp
  | _ -> "<extvaluedesc constructor not handled>" (* TODO *)

let rec string_of_ck = function
  | Clocks.Cbase -> "?top"
  | Clocks.Cvar link -> string_of_link !link
  | Clocks.Con _ -> "<Clocks.Con not handled>" (* TODO *)

and string_of_link = function
  | Clocks.Cindex i -> Printf.sprintf "?%d" i
  | Clocks.Clink ck -> string_of_ck ck (* XXX: Is it right? *)

let string_of_eq (eq: Minils.eq) =
  (* TODO: handle types *)
  Printf.sprintf "%s = %s when %s"
      (string_of_pat eq.Minils.eq_lhs)
      (string_of_exp eq.Minils.eq_rhs)
      (string_of_ck eq.Minils.eq_base_ck)

let node_pred file (node: Minils.node_dec) =
  (* Print node name *)
  Printf.fprintf file "node @%s__%s {\n"
      (string_of_modul node.Minils.n_name.Names.qual)
      node.Minils.n_name.Names.name;

  (* Print inputs *)
  let inputs = List.map (string_of_vardec true) node.Minils.n_input in
  Printf.fprintf file "  %s = init\n" (String.concat ", " inputs);

  (* Print equations *)
  let equations = List.map (string_of_eq) node.Minils.n_equs in
  Printf.fprintf file "  %s\n" (String.concat "\n  " equations);

  (* Print outputs *)
  let outputs = List.map (string_of_vardec false) node.Minils.n_output in
  Printf.fprintf file "  exit %s\n" (String.concat ", " outputs);

  (* Print end of node *)
  Printf.fprintf file "}\n"

let program_pred file (p: Minils.program_desc) = match p with
  | Minils.Pnode node -> node_pred file node
  | Minils.Pconst _ -> Printf.printf "const not supported\n"
  | Minils.Ptype _ -> Printf.printf "type not supported\n"

let program (p: Minils.program) =
  let filename = (String.uncapitalize (Names.modul_to_string p.Minils.p_modname)) ^".etac" in
  let file = open_out_bin filename in
  ignore (List.map (program_pred file) p.Minils.p_desc);
  close_out file;
