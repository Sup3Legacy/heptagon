let string_of_modul (modul: Names.modul) =
  let rec aux stack = function
    | Names.Pervasives -> "PERVASIVES" :: stack
    | Names.LocalModule -> "LOCALMODULE" :: stack
    | Names.Module name -> name :: stack
    | Names.QualModule name -> aux (name.Names.name :: stack) name.Names.qual
  in String.concat "__" (List.rev (aux [] modul))

let string_of_vardec (vardec: Minils.var_dec) =
  (* TODO: handle types *)
  String.concat " " ["i64"; Idents.name vardec.Minils.v_ident]

let node_pred file (node: Minils.node_dec) =
  (* Print node name *)
  Printf.fprintf file "node @%s__%s {\n"
      (string_of_modul node.Minils.n_name.Names.qual)
      node.Minils.n_name.Names.name;
  (* Print inputs *)
  let inputs = List.map string_of_vardec node.Minils.n_input in
  Printf.fprintf file "  %s = init;\n" (String.concat ", " inputs);

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
