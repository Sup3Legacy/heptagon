
(* Transformation which changes systematically all variable names of a program *)
(* Originaly built because of issue of some people with variables starting with "_" or uppercases *)

open Idents
open Global_mapfold
open Heptagon
open Hept_mapfold


(* Modif: Name => "x_" ^ name *)

(* Keep in memory the changes done *)
let var_ident_rename _ htblRenaming vid =
  let name = Idents.name vid in
  try
    let nvid = Hashtbl.find htblRenaming name in
    nvid, htblRenaming
  with
  | Not_found -> begin
    (* New name! *)
    let nname = ("x" ^ name) in
    let nvid = gen_var "var_rename" nname in
    Hashtbl.add htblRenaming name nvid;
    nvid, htblRenaming
  end

  


let node nd =
  (* We need to keep in memory the id we create, to avoid creating new ones with diff names *)
  let htblRenaming = Hashtbl.create 1000 in

  (* Call! *)
  let glfuns_var_rename = { Global_mapfold.defaults with
      var_ident = var_ident_rename
    } in
  let funs_var_rename = { Hept_mapfold.defaults with global_funs = glfuns_var_rename } in
  let n_nd, _ = funs_var_rename.node_dec funs_var_rename htblRenaming nd in
  n_nd


let program p =
  let nlpdesc = List.map
    (fun pdesc -> match pdesc with
      | Pnode n -> Pnode (node n)
      | _ -> pdesc
    ) p.p_desc in
  { p with p_desc = nlpdesc }

