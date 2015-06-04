let string_of_modul modul = 
  let rec aux stack = function
    | Names.Pervasives -> "PERVASIVES" :: stack
    | Names.LocalModule -> "LOCALMODULE" :: stack
    | Names.Module name -> name :: stack
    | Names.QualModule name -> aux (name.Names.name :: stack) name.Names.qual
  in String.concat "__" (List.rev (aux [] modul))

let node_pred file node =
  Printf.fprintf file "node @%s__%s { }\n"
      (string_of_modul node.Minils.n_name.Names.qual)
      node.Minils.n_name.Names.name

let program_pred file = function
  | Minils.Pnode node -> node_pred file node
  | Minils.Pconst _ -> Printf.printf "const not supported\n"
  | Minils.Ptype _ -> Printf.printf "type not supported\n"

let program p =
  let filename = (String.uncapitalize (Names.modul_to_string p.Minils.p_modname)) ^".etac" in
  let file = open_out_bin filename in
  ignore (List.map (program_pred file) p.Minils.p_desc);
  close_out file;
