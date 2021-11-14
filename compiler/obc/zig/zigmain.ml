open List
open Names
open Idents
open Obc
open Obc_utils
open Types
open Signature
open Zig
open Ziggen
open Compiler_utils

let fresh n = Idents.name (Idents.gen_var "zigmain" n)

let mk_int i = Zigconst (Zigint i)
let mk_float f = Zigconst (Zigfloat f)

let step_counter = fresh "step_zig"
and max_step = fresh"step_max"

let assert_node_res cd =
  let stepm = find_step_method cd in
  if List.length stepm.m_inputs > 0 then
    (Format.eprintf "Cannot generate run-time check for node %s with inputs.@."
       (zigname_of_qn cd.cd_name);
     exit 1);
  if (match stepm.m_outputs with
        | [{ v_type = Tid nbool; }] when nbool = Initial.pbool -> false
        | _ -> true) then
    (Format.eprintf
       "Cannot generate run-time check for node %s with non-boolean output.@."
       (zigname_of_qn cd.cd_name);
     exit 1);
  let name = zigname_of_qn cd.cd_name in
  let out =
    (fresh ("out_for_" ^ name),
      Zigty_id (qn_append cd.cd_name "_out")) in
  let mem, reset_i =
    if not cd.cd_stateful
    then ([], [])
    else
      let mem =
        (fresh ("mem_for_" ^ name), Zigty_id (qn_append cd.cd_name "_mem")) in
      ([mem],
       [Zigsexpr (Zigfun_call (name ^ "_reset", [CZigddrof (Zigvar (fst mem))]))]) in
  let step_i =
    let outn = Idents.name ((List.hd stepm.m_outputs).v_ident) in
    Csblock
      { var_decls = [];
        block_body =
          [
            Zigsexpr (Zigfun_call (name ^ "_step",
                               Zigaddrof (Zigvar (fst out))
                               :: (if cd.cd_stateful
                                   then [Zigaddrof (Zigvar (fst (List.hd mem)))]
                                   else [])));
            Zigif (Ziguop ("!", Zigfield (Zigvar (fst out), local_qn outn)),
                 [Zigsexpr (Zigfun_call ("fprintf",
                                     [Zigvar "stderr";
                                      Zigconst (Zigstrlit ("Node \""
                                                       ^ (Names.fullname cd.cd_name)
                                                            ^ "\" failed at step" ^
                                                              " %d.\n"));
                                      Zigvar step_counter]));
                  Zigreturn (mk_int 1)],
                 []);
          ];
      } in
  (out :: mem, reset_i, step_i);;

let interface i =
  let filename =
    filename_of_name (zigname_of_name (modul_to_string i.i_modname)) in
  let dirname = build_path (filename ^ "_zig") in
  let dir = clean_dir dirname in
  let zig_ast = interface_header (Filename.basename filename) i in
    Zig.output dir zig_ast