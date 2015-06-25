

(* List.map and List.fold_left in a single pass. *)
let mapfold (pred: 'a -> 'b -> ('a * 'c)) (start: 'a) (l: 'b list) =
  let aux (acc: ('a * 'c list)) (item: 'b) = (
    let (folded, mapped) = acc in
    let (new_folded, new_mapped) = (pred folded item) in
    (new_folded, new_mapped :: mapped)
  ) in
  let (folded, mapped) = (List.fold_left aux (start, []) l) in
  (folded, List.rev mapped)



(*** Fresh variables generators ***)

let _aux_fresh index prefix hint =
  index := !index + 1;
  Printf.sprintf "%s%s__%d" prefix hint !index

let fresh_var =
  let index = ref 0 in
  _aux_fresh index "TMP"

let fresh_clk =
  let index = ref 0 in
  _aux_fresh index "TMP"



(*** Type declarations ***)

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

module ExtValue =
  struct
    type t = Minils.extvalue
    let compare = Pervasives.compare
  end;;
module ExtvalueMap = Map.Make(ExtValue)
module ClockDisjonctionSet = Set.Make(ClockDisjonction)
type state_t = {
  channel: out_channel;
  written_clocks: ClockDisjonctionSet.t; (* Clocks whose definition (ie. “is” and “<=>”) was already written *)
  var_dec: Minils.var_dec Idents.Env.t; (* variable_name -> variable_declaration *)
  saved_values: (int * string) ExtvalueMap.t; (* value -> index_in_struct * type map *)
}



(*** Types and constructors storage ***)

let types_tbl = Hashtbl.create 256
let constructors_tbl = Hashtbl.create 1024

let get_type_of_constructor (constructor: Names.constructor_name) =
  Hashtbl.find constructors_tbl constructor

let add_constructor_type (c: Names.constructor_name) (t: Names.qualname) =
  Hashtbl.add constructors_tbl c t

(* Returns the integer that will be used to represent a constructor in output code. *)
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



(*** Initialization of bool type ***)

let pervasives_bool = {Names.qual=Names.Pervasives; Names.name="bool"}
let pervasives_true = {Names.qual=Names.Pervasives; Names.name="true"}
let pervasives_false = {Names.qual=Names.Pervasives; Names.name="false"}

let _ =
  add_constructor_type pervasives_true pervasives_bool
let _ =
  add_constructor_type pervasives_false pervasives_bool
let _ =
  Hashtbl.add types_tbl pervasives_bool (Minils.Type_enum [pervasives_false; pervasives_true])


(*** Name to string convertion ***)

let string_of_modul (modul: Names.modul) =
  let rec aux stack = function
    | Names.Pervasives -> (
        match (List.hd stack) with
        | "+" -> "add" :: (List.tl stack)
        | "~-" -> "sub %ZERO32," :: (List.tl stack)
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
    String.concat "" ["i32 %"; string_of_varident vardec.Minils.v_ident]
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
            (* Write the condition of a clock created from the given constructor on the variable *)
            let name = (formatter cstr var.Minils.v_ident) in
            let tmpimm = fresh_var "imm" in
            Printf.fprintf state.channel "  i32 %%%s = li %d when ?%s\n" tmpimm i base_ck;
            Printf.fprintf state.channel "  i1 %%%s = cmp eq %%%s, %%%s when ?%s\n" name (string_of_vardec false var) tmpimm base_ck;
            Printf.fprintf state.channel "  ?%s is %%%s\n" name name;
            (i+1, name)
          ) in
          (* Write all clocks constructed from the variable *)
          let (_, clocks) = mapfold pred 0 constructors in
          (* Write disjoint union equation *)
          Printf.fprintf state.channel "  ?%s <=> ?%s\n" base_ck (String.concat " | ?" clocks);
          { state with written_clocks=ClockDisjonctionSet.add (base_ck, var.Minils.v_ident) state.written_clocks }
      | _ -> failwith "Unsupported type" (* TODO *)
      )
    )
  ) in
  (new_state, formatter constructor (var.Minils.v_ident))

let strings_of_pat = function
  (* FIXME: not tail-recursive *)
  | Minils.Evarpat var_ident ->
      ("i32", string_of_varident var_ident)
  | Minils.Etuplepat _ ->
      failwith "Etuplepat not handled"



(*** Expressions output ***)

(* Static expressions *)
let rec push_static_exp state ck (sexp: Types.static_exp) =
  push_static_exp_desc state ck sexp.Types.se_desc

(* Static expression descriptions *)
and push_static_exp_desc state ck = function
  | Types.Svar name -> (* Variables *)
      (state, name)
  | Types.Sint i -> (* Integers *)
      let tmpvar = (fresh_var "imm") in
      Printf.fprintf state.channel "  i32 %%%s = li %d when ?%s\n" tmpvar i ck;
      (state, {Names.qual=Names.LocalModule; Names.name=tmpvar})
  | Types.Sop (f_name, args) -> (* Static operators *)
      let (state, args) = mapfold (fun state arg -> push_static_exp state ck arg) state args in
      let args = (String.concat ", %" (List.map string_of_qualname args)) in
      let tmpvar = (fresh_var "sexp") in
      Printf.fprintf state.channel "  i32 %%%s = %s %%%s when ?%s\n" tmpvar (string_of_qualname f_name) args ck;
      (state, {Names.qual=Names.LocalModule; Names.name=tmpvar})
  | _ -> failwith "static_exp_desc constructor not handled" (* TODO *)

(* Dynamic expression *)
and push_exp (state: state_t) base_clk (lhs_type: string) (lhs_var: string) (exp: Minils.exp) =
  match exp.Minils.e_desc with
  | Minils.Eextvalue ev -> (* constant/variable/field/when/reinit *)
      let (state, res) = push_extvalue state base_clk ev in
      Printf.fprintf state.channel "  %s %%%s = sample %%%s when ?%s\n" lhs_type lhs_var (string_of_varident res) base_clk;
      state
  | Minils.Efby (first, follow) -> (* followed by *)
      (* Generate fresh variables *)
      let tmpfirst = fresh_var "first" in
      let tmpfollow = fresh_var "follow" in
      let memory_ptr = fresh_var "memptr" in
      let selector_ptr = fresh_var "selptr" in
      let selector = fresh_var "sel" in

      (* Write clock definitions *)
      let clk_first = Printf.sprintf "%s__%s_first" base_clk lhs_var in
      let clk_follow = Printf.sprintf "%s__%s_follow" base_clk lhs_var in
      Printf.fprintf state.channel "  ?%s is %%%s_not\n" clk_first selector;
      Printf.fprintf state.channel "  ?%s is %%%s\n" clk_follow selector;
      Printf.fprintf state.channel "  ?%s <=> ?%s | ?%s\n" base_clk clk_first clk_follow;
      Printf.fprintf state.channel "  %s %%%s = phi %%%s, %%%s when ?%s\n" lhs_type lhs_var tmpfirst tmpfollow base_clk;

      (* Initial value (left operand of fby) *)
      let (state, res_first) = (match first with
        | None ->
            Printf.fprintf state.channel "  %s %%%s = li 0 when ?%s ; UNDEF\n" lhs_type lhs_var clk_first;
            (state, lhs_var)
        | Some first ->
            let (state, res) = push_static_exp state clk_first first in (* TODO: Do this is done in the reset function, as for C *)
            Printf.fprintf state.channel "  %s %%%s = sample %%%s when ?%s\n" lhs_type tmpfirst (string_of_qualname res) clk_first;
            (state, tmpfirst)
      ) in
      let index = ExtvalueMap.fold (fun _ _ n  -> n+1) state.saved_values 0 in
      let (state, res_follow) = push_extvalue state clk_follow follow in

      (* Load pointer to first/follow selector *)
      Printf.fprintf state.channel "  i1* %%%s = getptr %%__PAST, %d when ?%s\n" selector_ptr (index*2) base_clk;
      Printf.fprintf state.channel "  i1 %%%s = load %%%s when ?%s\n" selector selector_ptr base_clk;
      Printf.fprintf state.channel "  i1 %%%s_not = not %%%s when ?%s\n" selector selector base_clk;

      (* Load pointer to memory *)
      Printf.fprintf state.channel "  %s* %%%s = getptr %%__PAST, %d when ?%s\n" lhs_type memory_ptr (index*2+1) base_clk;

      (* Load present value from the past *)
      Printf.fprintf state.channel "  %s %%%s = load %%%s when ?%s\n" lhs_type tmpfollow memory_ptr clk_follow;

      (* Load future value from the present *)
      Printf.fprintf state.channel "  store %%%s, %%ZERO1 when ?%s after %%%s\n" selector_ptr clk_first selector;
      Printf.fprintf state.channel "  store %%%s, %%%s when ?%s after %%%s\n" memory_ptr (string_of_varident res_follow) clk_follow tmpfollow;
      Printf.fprintf state.channel "  store %%%s, %%%s when ?%s after %%%s\n" memory_ptr res_first clk_first tmpfirst;

      let state = { state with saved_values=(ExtvalueMap.add follow (index, "i32") state.saved_values) } in
      state
  | Minils.Eapp (app, evs, None) -> (* Application *)
      let (state, params) = (mapfold (fun state arg -> push_extvalue state base_clk arg) state evs) in
      push_app state base_clk lhs_type lhs_var params app
  | Minils.Ewhen (exp, _, _) -> (* Clock sampling *)
      let exp_res = fresh_var "res" in
      let state = push_exp state base_clk "i32" exp_res exp in
      let clk = base_clk in (* Heptagon already uses the sub-clock as base clock *)
      Printf.fprintf state.channel "  %s %%%s = sample %%%s when ?%s\n" lhs_type lhs_var exp_res clk;
      state
  | Minils.Emerge (var, l) -> (* Clock merging *)
      let pred state (cstr, exp) = (
        let (state, clk) = ck_name_from_constructor state base_clk cstr (Idents.Env.find var state.var_dec) in
        push_extvalue state clk exp
      ) in
      let (state, variables) = mapfold pred state l in
      Printf.fprintf state.channel "  %s %%%s = phi %%%s when ?%s\n" lhs_type lhs_var (String.concat ", %" (List.map string_of_varident variables)) base_clk;
      state
  | _ -> failwith "edesc constructor not handled" (* TODO *)

(* Application *)
and push_app (state: state_t) base_clk (lhs_type: string) (lhs_var: string) (params: Idents.ident list) (app: Minils.app) =
  match app.Minils.a_op with
  | Minils.Efun f -> (* Function and operator calls *)
      Printf.fprintf state.channel "  %s %%%s = %s %%%s when ?%s\n" lhs_type lhs_var (string_of_qualname f) (String.concat ", %" (List.map string_of_varident params)) base_clk;
      state
  | Minils.Eifthenelse -> (
      match params with [cond; iftrue; iffalse] -> (
        (* Generate fresh variables *)
        let tmptrue = fresh_var "iftrue" in
        let tmpfalse = fresh_var "iffalse" in

        (* Declaration of the condition variable *)
        let conddec = Idents.Env.find cond state.var_dec in

        (* Get/generate clocks of the true and false states of the conditio *)
        let (state, trueclk) = ck_name_from_constructor state base_clk pervasives_true conddec in
        let (state, falseclk) = ck_name_from_constructor state base_clk pervasives_false conddec in

        (* Write output *)
        Printf.fprintf state.channel "  %s %%%s = sample %%%s when ?%s\n"
            lhs_type tmptrue (string_of_varident iftrue) trueclk;
        Printf.fprintf state.channel "  %s %%%s = sample %%%s when ?%s\n"
            lhs_type tmpfalse (string_of_varident iffalse) falseclk;
        Printf.fprintf state.channel "  %s %%%s = phi %%%s, %%%s\n" lhs_type lhs_var tmptrue tmpfalse;
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

(* Get the name of a clock, and create it if does not exist yet *)
let rec push_ck state = function
  | Clocks.Cbase -> (state, "top")
  | Clocks.Cvar link -> push_link state !link
  | Clocks.Con (base_ck, constructor, varident) ->
      let (state, base_ck) = push_ck state base_ck in
      let var = Idents.Env.find varident state.var_dec in
      ck_name_from_constructor state base_ck constructor var

and push_link state = function
  | Clocks.Cindex i -> (state, Printf.sprintf "%d" i)
  | Clocks.Clink ck -> push_ck state ck (* XXX: Is it right? *)

(* Equations *)
let push_eq state (eq: Minils.eq) =
  (* TODO: handle types *)
  let (state, ck) = (push_ck state eq.Minils.eq_base_ck) in
  let (lhs_type, lhs_var) = strings_of_pat eq.Minils.eq_lhs in
  push_exp state ck lhs_type lhs_var eq.Minils.eq_rhs

(* Variable initialization *)
let push_var_init state (var: Minils.var_dec) =
  let state = { state with var_dec = Idents.Env.add var.Minils.v_ident var state.var_dec } in
  match var.Minils.v_type with
  | Types.Tid {Names.qual=Names.Pervasives; Names.name="float"}
  | Types.Tid {Names.qual=Names.Pervasives; Names.name="bool"}
  | Types.Tid {Names.qual=Names.Pervasives; Names.name="int"} -> state
  | Types.Tid t when Hashtbl.mem types_tbl t -> state (* Will be initialized if/when needed *)
  | Types.Tid t  -> failwith (Printf.sprintf "Undefined type %s." (string_of_qualname t))
  | _ -> failwith "Unsupported type."

let node_pred file (node: Minils.node_dec) =
  let node_name = Printf.sprintf "%s__%s"
      (string_of_modul node.Minils.n_name.Names.qual)
      node.Minils.n_name.Names.name in

  (* Print node name *)
  Printf.fprintf file "node @%s_step {\n" node_name;

  let memory_type = Printf.sprintf "PAST__%s" node_name in

  let state = {channel=file; written_clocks=ClockDisjonctionSet.empty; var_dec=Idents.Env.empty; saved_values=ExtvalueMap.empty} in

  (* Print variable initializations *)
  let all_var_dec = node.Minils.n_output @ node.Minils.n_input @ node.Minils.n_local in
  let state = List.fold_left push_var_init state all_var_dec in

  Printf.fprintf file "  i32 %%ZERO32 = li 0;\n";
  Printf.fprintf file "  i1 %%ZERO1 = cmp ne %%ZERO32, %%ZERO32;\n";

  (* Print equations *)
  let state = (List.fold_left push_eq state node.Minils.n_equs) in

  let arguments = (List.map (string_of_vardec true) node.Minils.n_input) in

  let arguments =
    (* Prepend memory to the list of arguments iff needed. *)
    if (ExtvalueMap.is_empty state.saved_values) then
      arguments
    else
      (Printf.sprintf "!%s* %%__PAST" memory_type) :: arguments
  in

  (* Print inputs *)
  (match arguments with
  | [] -> Printf.fprintf file "  init\n"
  | inputs -> Printf.fprintf file "  %s = init\n" (String.concat ", " inputs)
  );

  (* Print outputs *)
  let outputs = List.map (string_of_vardec false) node.Minils.n_output in
  Printf.fprintf file "  exit %%%s\n" (String.concat ", %" outputs);

  (* Print end of node *)
  Printf.fprintf file "}\n\n";

  (* Print remembrance struct type and its reinitialization node *)
  if (not (ExtvalueMap.is_empty state.saved_values)) then (
    let fields = ExtvalueMap.fold (fun _ (_, type_) acc -> type_ :: "i1" :: acc) state.saved_values [] in
    Printf.fprintf file "type !%s = { %s }\n\n" memory_type (String.concat ", " (List.rev fields));
    Printf.fprintf file "node @%s_reset {\n" node_name;
    Printf.fprintf file "  !%s* %%__PAST = init\n" memory_type;
    Printf.fprintf file "  i32 %%ZERO32 = li 0\n";
    Printf.fprintf file "  i1 %%ZERO1 = cmp ne %%ZERO32, %%ZERO32\n";
    ignore (ExtvalueMap.fold (fun _ _ (is_bool, i) ->
      if is_bool then (
        Printf.fprintf file "  i1* %%ptr%d = getptr %%__PAST, %d\n" i i;
        Printf.fprintf file "  store %%ptr%d, %%ZERO1\n" i
      )
      else
        ();
      (not is_bool, i+1)) state.saved_values (true, 0));
    Printf.fprintf file "  exit\n}\n"
  )
  else
    ()

let program_pred file (p: Minils.program_desc) = match p with
  | Minils.Pnode node -> node_pred file node
  | Minils.Pconst _ -> Printf.printf "const not supported\n"
  | Minils.Ptype t -> (
      (* Add the type to the compiler's hashtable *)
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
