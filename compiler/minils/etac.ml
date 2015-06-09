let _aux_fresh index prefix hint =
  index := !index + 1;
  Printf.sprintf "%s%s__%d" prefix hint !index

let fresh_var =
  let index = ref 0 in
  _aux_fresh index "TMP"

let fresh_clk =
  let index = ref 0 in
  _aux_fresh index "TMP"


let types_tbl = Hashtbl.create 256
let constructors_tbl = Hashtbl.create 1024

let get_type_of_constructor (constructor: Names.constructor_name) =
  Hashtbl.find constructors_tbl constructor

let add_constructor_type (c: Names.constructor_name) (t: Names.qualname) =
  Hashtbl.add constructors_tbl c t

let bool_type = {Names.qual= Names.Pervasives; Names.name= "bool"}

let _ =
  add_constructor_type
    {Names.qual= Names.Pervasives; Names.name= "true"}
    bool_type
let _ =
  add_constructor_type
    {Names.qual= Names.Pervasives; Names.name= "false"}
    bool_type
let _ =
  Hashtbl.add types_tbl bool_type (Minils.Type_enum [
    {Names.qual= Names.Pervasives; Names.name= "true"};
    {Names.qual= Names.Pervasives; Names.name= "false"}])


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
    | Names.LocalModule -> "LOCALMODULE" :: stack
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

let rec push_static_exp acc (sexp: Types.static_exp) =
  push_static_exp_desc acc sexp.Types.se_desc

and push_static_exp_desc acc = function
  | Types.Svar name -> (acc, string_of_qualname name)
  | Types.Sint i ->
      let tmpvar = (fresh_var "imm") in
      let loader = (Printf.sprintf "i64 %%%s = li %d" tmpvar i) in
      (loader :: acc, tmpvar)
  | Types.Sop (f_name, args) ->
      let (acc, args) = mapfold push_static_exp acc args in
      let args = (String.concat ", %%" args) in
      let tmpvar = (fresh_var "sexp") in
      let loader = (Printf.sprintf "i64 %%%s = %s %%%s" tmpvar (string_of_qualname f_name) args) in
      (loader :: acc, tmpvar)
  | _ -> (acc, "<static_exp_desc constructor not handled>") (* TODO *)

let rec string_of_pat = function
  (* FIXME: not tail-recursive *)
  | Minils.Evarpat var_ident ->
      String.concat "" ["i64 %"; string_of_varident var_ident]
  | Minils.Etuplepat pats ->
      Printf.sprintf "%%%s" (String.concat ", %" (List.map string_of_pat pats))

and push_exp acc clk (exp: Minils.exp)  =
  push_edesc acc clk exp.Minils.e_desc

and push_edesc acc _ = function
  | Minils.Eextvalue ev -> push_extvalue acc ev
  | Minils.Eapp (app, evs, None) ->
      let (acc, params) = (mapfold push_extvalue acc evs) in
      push_app acc params app
  | Minils.Ewhen _ ->
      (acc, "<Ewhen not handled>")
  | Minils.Emerge _ ->
      (acc, "<Emerge not handled>")
  | _ -> (acc, "<edesc constructor not handled>") (* TODO *)

and push_app acc (params: string list) (app: Minils.app) =
  match app.Minils.a_op with
  | Minils.Efun f -> (acc,
      String.concat " %" [string_of_qualname f; (String.concat ", %" params)])
  | Minils.Eifthenelse -> (
      match params with [cond; iftrue; iffalse] -> (
        let tmptrue = fresh_var "iftrue" in
        let tmpfalse = fresh_var "iffalse" in
        let instrsampletrue = Printf.sprintf "i64 %%%s = sample %%%s when ?%s_true_clk"
            tmptrue iftrue cond in
        let instrsamplefalse = Printf.sprintf "i64 %%%s = sample %%%s when ?%s_false_clk"
            tmpfalse iffalse cond in
        (instrsampletrue :: instrsamplefalse :: acc,
        Printf.sprintf "phi %%%s, %%%s" tmptrue tmpfalse)
      )
      | _ -> failwith "bad list of params"
  )
  | _ -> (acc, "<op constructor not handled>") (* TODO *)

and push_extvalue acc (ev: Minils.extvalue) =
  push_extvaluedesc acc ev.Minils.w_desc

and push_extvaluedesc acc = function
  | Minils.Wvar varident -> (acc, Printf.sprintf "%s" (string_of_varident varident))
  | Minils.Wconst sexp -> push_static_exp acc sexp
  | _ -> (acc, "<extvaluedesc constructor not handled>") (* TODO *)

let rec push_ck acc = function
  (* FIXME: not tail-recursive *)
  | Clocks.Cbase -> (acc, "top")
  | Clocks.Cvar link -> push_link acc !link
  | Clocks.Con _ ->
      failwith "Clocks.Con not handled."

and push_link acc = function
  | Clocks.Cindex i -> (acc, Printf.sprintf "%d" i)
  | Clocks.Clink ck -> push_ck acc ck (* XXX: Is it right? *)

let push_eq acc (eq: Minils.eq) =
  (* TODO: handle types *)
  let (acc, ck) = (push_ck acc eq.Minils.eq_base_ck) in
  let (acc, s) = push_exp acc ck eq.Minils.eq_rhs in
  let inst = Printf.sprintf "%s = %s"
      (string_of_pat eq.Minils.eq_lhs) s
  in inst :: acc

let push_var_init acc (var: Minils.var_dec) =
  let varname =  (string_of_varident var.Minils.v_ident) in
  let (acc, base_clk) = (push_ck acc var.Minils.v_clock) in
  match var.Minils.v_type with
  | Types.Tid {Names.qual=Names.Pervasives; Names.name="bool"} ->
      let trueclk = Printf.sprintf "%s_true_clk" varname in
      let falsevarname = Printf.sprintf "%s_false" varname in
      let falseclk = Printf.sprintf "%s_false_clk" varname in
      let noteqn = Printf.sprintf "i1 %%%s = not %%%s when ?%s" falsevarname varname base_clk in
      let trueeqn = Printf.sprintf "?%s is %%%s" trueclk varname in
      let falseeqn = Printf.sprintf "?%s is %%%s" falseclk falsevarname in
      let unioneqn = Printf.sprintf "?%s <=> ?%s | ?%s" base_clk trueclk falseclk in
      noteqn :: trueeqn :: falseeqn :: unioneqn :: acc
  | Types.Tid {Names.qual=Names.Pervasives; Names.name="float"} -> acc
  | Types.Tid {Names.qual=Names.Pervasives; Names.name="int"} -> acc
  | _ -> failwith "Unsupported type."

let node_pred file (node: Minils.node_dec) =
  (* Print node name *)
  Printf.fprintf file "node @%s__%s {\n"
      (string_of_modul node.Minils.n_name.Names.qual)
      node.Minils.n_name.Names.name;

  Printf.fprintf file "  %s\n" (String.concat "\n  " (List.fold_left push_var_init [] (node.Minils.n_output @ node.Minils.n_input @ node.Minils.n_local)));

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
