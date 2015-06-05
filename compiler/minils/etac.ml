let string_of_modul (modul: Names.modul) =
  let rec aux stack = function
    | Names.Pervasives -> "PERVASIVES" :: stack
    | Names.LocalModule -> "LOCALMODULE" :: stack
    | Names.Module name -> name :: stack
    | Names.QualModule name -> aux (name.Names.name :: stack) name.Names.qual
  in String.concat "__" (List.rev (aux [] modul))

let string_of_varident (varident: Idents.var_ident) =
  Printf.sprintf "%%%s" (Idents.name varident)

let string_of_vardec (with_type: bool) (vardec: Minils.var_dec) =
  (* TODO: handle types *)
  if with_type then
    String.concat " " ["i64"; string_of_varident vardec.Minils.v_ident]
  else
    string_of_varident vardec.Minils.v_ident

let rec string_of_pat = function
  (* FIXME: not tail-recursive *)
  | Minils.Evarpat var_ident ->
      String.concat " " ["i64"; string_of_varident var_ident]
  | Minils.Etuplepat pats ->
      Printf.sprintf "%s" (String.concat ", " (List.map string_of_pat pats))

let rec string_of_exp (exp: Minils.exp)  =
  "foo"


let rec string_of_ck (ck: Clocks.ck) =
  "bar"

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
  Printf.fprintf file "  %s = init;\n" (String.concat ", " inputs);

  (* Print equations *)
  let equations = List.map (string_of_eq) node.Minils.n_equs in
  Printf.fprintf file "  %s;\n" (String.concat ";\n  " equations);

  (* Print outputs *)
  let outputs = List.map (string_of_vardec false) node.Minils.n_output in
  Printf.fprintf file "  exit %s;\n" (String.concat ", " outputs);

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
