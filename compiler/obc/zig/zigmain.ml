let interface i =
  let filename =
    filename_of_name (zigname_of_name (modul_to_string i.i_modname)) in
  let dirname = build_path (filename ^ "_zig") in
  let dir = clean_dir dirname in
  let c_ast = interface_header (Filename.basename filename) i in
    Zig.output dir c_ast