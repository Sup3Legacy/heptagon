let _aux_fresh index prefix hint =
  index := !index + 1;
  Printf.sprintf "%s%s__%d" prefix hint !index

let fresh_var =
  let index = ref 0 in
  _aux_fresh index "%TMP"

let fresh_clk =
  let index = ref 0 in
  _aux_fresh index "?TMP"


let int_of_constructor =
  let tbl = Hashtbl.create 1024 in
  let index = ref 0 in
  let aux (name: Names.constructor_name) =
    if Hashtbl.mem tbl name then
      Hashtbl.find tbl name
    else (
      index := !index + 1;
      Hashtbl.add tbl name !index;
      !index
    )
  in aux


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
      let tmpvar = (fresh_var "imm") in
      let loader = (Printf.sprintf "i64 %s = li %d" tmpvar i) in
      (loader :: acc, tmpvar)
  | Types.Sop (f_name, args) ->
      let (acc, args) = mapfold push_static_exp acc args in
      let args = (String.concat ", " args) in
      let tmpvar = (fresh_var "sexp") in
      let loader = (Printf.sprintf "i64 %s = %s %s" tmpvar (string_of_qualname f_name) args) in
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
      push_app acc params app
  | _ -> (acc, "<edesc constructor not handled>") (* TODO *)

and push_app acc (params: string list) (app: Minils.app) =
  match app.Minils.a_op with
  | Minils.Efun f -> (acc,
      String.concat " " [string_of_qualname f; (String.concat ", " params)])
  | Minils.Eifthenelse -> (
      match params with [cond; iftrue; iffalse] -> (
        let notcond = fresh_var "not" in
        let tmptrue = fresh_var "iftrue" in
        let tmpfalse = fresh_var "iffalse" in
        let clktrue = fresh_clk "true" in
        let clkfalse = fresh_clk "false" in
        let eqnclktrue = Printf.sprintf "%s is %s" clktrue cond in
        let eqnclkfalse = Printf.sprintf "%s is %s" clkfalse notcond in
        let eqnclkrel = Printf.sprintf "?top <=> %s | %s" clkfalse clktrue in (* Redundant relatio *)
        let instrnot = Printf.sprintf "i1 %s = not %s"
            notcond cond in
        let instrsampletrue = Printf.sprintf "i64 %s = sample %s when %s"
            tmptrue iftrue clkfalse in
        let instrsamplefalse = Printf.sprintf "i64 %s = sample %s when %s"
            tmpfalse iffalse clkfalse in
        (instrnot :: instrsampletrue :: instrsamplefalse ::
          eqnclktrue :: eqnclkfalse :: eqnclkrel :: acc,
        Printf.sprintf "phi %s, %s" tmptrue tmpfalse)
      )
      | _ -> failwith "bad list of params"
  )
  | _ -> (acc, "<op constructor not handled>") (* TODO *)

and push_extvalue acc (ev: Minils.extvalue) =
  push_extvaluedesc acc ev.Minils.w_desc

and push_extvaluedesc acc = function
  | Minils.Wvar varident -> (acc, string_of_varident varident)
  | Minils.Wconst sexp -> push_static_exp acc sexp
  | _ -> (acc, "<extvaluedesc constructor not handled>") (* TODO *)

let rec push_ck acc = function
  (* FIXME: not tail-recursive *)
  | Clocks.Cbase -> (acc, "?top")
  | Clocks.Cvar link -> push_link acc !link
  | Clocks.Con (ck, constructor, var) ->
      let (acc, ck) = push_ck acc ck in
      let tmpvar = (fresh_var (Printf.sprintf "%s_%s" (string_of_qualname constructor) (string_of_varident var))) in
      let tmpclk = (fresh_clk (Printf.sprintf "%s_%s" (string_of_qualname constructor) (string_of_varident var))) in
      let vareqn = Printf.sprintf "i1 %s = cmp eq %s %d" tmpvar (string_of_varident var) (int_of_constructor constructor) in
      let clkeqn = Printf.sprintf "%s is %s" tmpclk tmpvar in
      (vareqn :: clkeqn :: acc, Printf.sprintf "%s, %s" ck tmpclk)

and push_link acc = function
  | Clocks.Cindex i -> (acc, Printf.sprintf "?%d" i)
  | Clocks.Clink ck -> push_ck acc ck (* XXX: Is it right? *)

let push_eq acc (eq: Minils.eq) =
  (* TODO: handle types *)
  let (acc, s) = push_exp acc eq.Minils.eq_rhs in
  let (acc, ck) = (push_ck acc eq.Minils.eq_base_ck) in
  let inst = Printf.sprintf "%s = %s when %s"
      (string_of_pat eq.Minils.eq_lhs) s ck
  in inst :: acc

let node_pred file (node: Minils.node_dec) =
  (* Print node name *)
  Printf.fprintf file "node @%s__%s {\n"
      (string_of_modul node.Minils.n_name.Names.qual)
      node.Minils.n_name.Names.name;

  (* Print inputs *)
  (match List.map (string_of_vardec true) node.Minils.n_input with
  | [] -> Printf.fprintf file "  init\n"
  | inputs -> Printf.fprintf file "  %s = init\n" (String.concat ", " inputs)
  );

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
