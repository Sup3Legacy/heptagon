open Misc
open Names
open Modules
open Signature
open Java
open Java_printer

(** returns the vd and the pat of a fresh ident from [name] *)
let mk_var ty name =
  let id = Idents.gen_var "java_main" name in
  mk_var_dec id ty, Pvar id, Evar id

let program p =
  (*Scalarize*)
  let p = Compiler_utils.pass "Scalarize" true Scalarize.program p Obc_compiler.pp in
  let p_java = if !Compiler_options.java_queue_size = 0
    then Obc2java.program p
    else Obc2java_asyncnode.program p
  in
  let dir = Compiler_utils.build_path "java" in
  Compiler_utils.ensure_dir dir;

  (* Compile and output the nodes *)
  output_program dir p_java;

  (* Create a runnable main simulation *)
  if !Compiler_options.simulation
  then (
    let class_name = Obc2java.fresh_classe (!Compiler_options.simulation_node ^ "_sim") in
    Idents.enter_node class_name;
    let field_step_dnb, id_step_dnb =
      let id = Idents.gen_var "java_main" "default_step_nb" in
      mk_field ~static:true ~final:true ~value:(Some (Sint 100)) Tint id, id
    in
    let main_methode =
      let vd_step, pat_step, exp_step = mk_var Tint "step" in
      let vd_args, _, exp_args =
        mk_var (Tarray (Tclass (Names.pervasives_qn "String"), (Sint 0))) "args" in
      let body =
        let vd_main, e_main, q_main, ty_main =
          let q_main = !Compiler_options.simulation_node |> qualify_value in (*qual*)
          let ty_main =
            (find_value q_main).node_outputs |> types_of_arg_list |> Types.prod in
          let q_main = Obc2java.qualname_to_package_classe q_main in (*java qual*)
          let id = Idents.gen_var "java_main" "main" in
          mk_var_dec id (Tclass q_main), Evar id, q_main, ty_main
        in
        let acts =
          let integer = Eclass(Names.pervasives_qn "Integer") in
          let args1 = Earray_elem(exp_args, Sint 1) in
          let out = Eclass(Names.qualname_of_string "java.lang.System.out") in
          let jarrays = Eclass(Names.qualname_of_string "java.util.Arrays") in
          let jint = Eclass(Names.qualname_of_string "Integer") in
          let jfloat = Eclass(Names.qualname_of_string "Float") in
          let jbool = Eclass(Names.qualname_of_string "Boolean") in
          let jsys = Eval(Pclass(Names.qualname_of_string "java.lang.System")) in
          let jminus = pervasives_qn "-" in
          let ret = Emethod_call(e_main, "step", []) in
          let print_ret, separate = match ty_main with
            | Types.Tarray (Types.Tarray _, _) ->
                Emethod_call(jarrays, "deepToString", [ret]), false
            | Types.Tarray _ -> Emethod_call(jarrays, "toString", [ret]), false
            | t when t = Initial.tint -> Emethod_call(jint, "toString", [ret]), false
            | t when t = Initial.tfloat -> Emethod_call(jfloat, "toString", [ret]), false
            | t when t = Initial.tbool -> Emethod_call(jbool, "toString", [ret]), false
            | Types.Tprod [] -> Java.Sstring "_", true
            | _ -> Emethod_call(ret, "toString", []), false
          in
          let vd_t1, e_t1 =
            let id = Idents.gen_var "java_main" "t" in
            mk_var_dec id Tlong, Eval (Pvar id)
          in
          let main_for_loop i =
            if separate
            then [ Aexp(Emethod_call(e_main, "step", []));
                   Aexp(Emethod_call(out, "printf", [ Sstring "%d => _\\n"; Eval (Pvar i)])) ]
            else [ Aexp(Emethod_call(out, "printf", [ Sstring "%d => %s\\n"; Eval (Pvar i);
                                                      print_ret])) ]
          in
          [ Anewvar(vd_main, Enew (Tclass q_main, []));
            Aifelse( Efun(Names.pervasives_qn ">", [Efield (exp_args, "length"); Sint 1])
                   , mk_block [Aassgn(pat_step, Emethod_call(integer, "parseInt", [args1]))]
                   , mk_block [Aassgn(pat_step, Evar id_step_dnb)]);
            Anewvar(vd_t1, Emethod_call(jsys, "currentTimeMillis", []));
            Obc2java.fresh_for pat_step main_for_loop;
            Aexp (Emethod_call(out, "printf",
              [ Sstring "time : %d\\n";
                Efun(jminus, [Emethod_call(jsys, "currentTimeMillis", []); e_t1])]))
          ]
        in
        mk_block ~locals:[vd_step] acts
      in
      mk_methode ~static:true ~args:[vd_args] ~throws:throws_async body "main"
    in
    let c = mk_classe ~imports:import_async ~fields:[field_step_dnb]
                                            ~methodes:[main_methode] class_name
    in
    output_program dir [c]
  )
