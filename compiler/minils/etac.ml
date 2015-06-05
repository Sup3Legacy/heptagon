let fresh_name =
  let index = ref 0 in
  let aux () = (
    index := !index + 1;
    Printf.sprintf "%%TMP__%d" !index
  ) in
  aux

(* List.map and List.fold_left in a single pass. *)
let mapfold (pred: 'a -> 'b -> ('a * 'c)) (start: 'a) (l: 'b list) =
  let aux (acc: ('a * 'c list)) (item: 'b) = (
    let (folded, mapped) = acc in
    let (new_folded, new_mapped) = (pred folded item) in
    (new_folded, new_mapped :: mapped)
  ) in List.fold_left aux (start, []) l

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

let rec push_static_exp acc (sexp: Types.static_exp) =
  push_static_exp_desc acc sexp.Types.se_desc

and push_static_exp_desc acc = function
  | Types.Svar name -> (acc, string_of_qualname name)
  | Types.Sint i ->
      let tmpvar = (fresh_name ()) in
      let loader = (Printf.sprintf "i64 %s = li %d" tmpvar i) in
      (loader :: acc, tmpvar)
  | _ -> (acc, "<static_exp_desc constructor not handled>") (* TODO *)

let rec string_of_pat = function
  (* FIXME: not tail-recursive *)
  | Minils.Evarpat var_ident ->
      String.concat " " ["i64"; string_of_varident var_ident]
  | Minils.Etuplepat pats ->
      Printf.sprintf "%s" (String.concat ", " (List.map string_of_pat pats))

let rec push_exp acc(exp: Minils.exp)  =
  push_edesc acc exp.Minils.e_desc

and push_edesc acc = function
  | Minils.Eextvalue ev -> push_extvalue acc ev
  | Minils.Eapp (app, evs, None) ->
      let (acc, params) = (mapfold push_extvalue acc evs) in
      (acc, Printf.sprintf "%s %s"
          (string_of_app app)
          (String.concat ", " params))
  | Minils.Eapp (app, evs, Some varident) ->
      let (acc, params) = (mapfold push_extvalue acc evs) in
      (acc,
      Printf.sprintf "%s %s(%s)"
          (string_of_app app)
          (String.concat ", " params)
          (string_of_varident varident))
  | _ -> (acc, "<edesc constructor not handled>") (* TODO *)

and string_of_app (app: Minils.app) =
  match app.Minils.a_op with
  | Minils.Efun f -> string_of_qualname f
  | _ -> "<op constructor not handled>" (* TODO *)

and push_extvalue acc (ev: Minils.extvalue) =
  push_extvaluedesc acc ev.Minils.w_desc

and push_extvaluedesc acc = function
  | Minils.Wvar varident -> (acc, string_of_varident varident)
  | Minils.Wconst sexp -> push_static_exp acc sexp
  | _ -> (acc, "<extvaluedesc constructor not handled>") (* TODO *)

let rec string_of_ck = function
  | Clocks.Cbase -> "?top"
  | Clocks.Cvar link -> string_of_link !link
  | Clocks.Con _ -> "<Clocks.Con not handled>" (* TODO *)

and string_of_link = function
  | Clocks.Cindex i -> Printf.sprintf "?%d" i
  | Clocks.Clink ck -> string_of_ck ck (* XXX: Is it right? *)

let push_eq acc (eq: Minils.eq) =
  (* TODO: handle types *)
  let (acc, s) = push_exp acc eq.Minils.eq_rhs in
  let inst = Printf.sprintf "%s = %s when %s"
      (string_of_pat eq.Minils.eq_lhs)
      s
      (string_of_ck eq.Minils.eq_base_ck)
  in inst :: acc

let node_pred file (node: Minils.node_dec) =
  (* Print node name *)
  Printf.fprintf file "node @%s__%s {\n"
      (string_of_modul node.Minils.n_name.Names.qual)
      node.Minils.n_name.Names.name;

  (* Print inputs *)
  let inputs = List.map (string_of_vardec true) node.Minils.n_input in
  Printf.fprintf file "  %s = init\n" (String.concat ", " inputs);

  (* Print equations *)
  let equations = List.fold_left (push_eq) [] node.Minils.n_equs in
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
