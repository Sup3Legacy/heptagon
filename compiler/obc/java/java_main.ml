open Misc
open Names
open Modules
open Signature
open Java
open Java_printer

let load_conf () =
  Compiler_options.normalize_register_outputs := false;
  Compiler_options.do_scalarize := true;
  ()

(** returns the vd and the pat of a fresh ident from [name] *)
let mk_var ty name =
  let id = Idents.gen_var "java_main" name in
  mk_var_dec id ty, Pvar id, Evar id


let program p =
  let p_java = Obc2java.program p in
  let dir = Compiler_utils.build_path "java" in
  Compiler_utils.ensure_dir dir;

  (* Compile and output the nodes *)
  output_program dir p_java;

  (* Create a runnable main simulation *)
  if !Compiler_options.simulation
  then (
    let q_main =
      try !Compiler_options.simulation_node |> qualify_value
      with Not_found ->
        Format.eprintf "Unable to find main node: %s@." !Compiler_options.simulation_node;
        raise Errors.Error
    in
    let sig_main = find_value q_main in
    let ty_main = sig_main.node_outputs |> types_of_arg_list |> Types.prod in
    let ty_main_args = sig_main.node_params |> types_of_param_list in
    let class_name = Obc2java.fresh_classe (!Compiler_options.simulation_node ^ "_sim") in
    Idents.enter_node class_name;
    let field_step_dnb, id_step_dnb =
      let id = Idents.gen_var "java_main" "default_step_nb" in
      mk_field ~static:true ~final:true ~value:(Some (Sint 100)) Tint id, id
    in
    let main_methode =

      (* step is the current iteration step *)
      let vd_step, pat_step, exp_step = mk_var Tint "step" in

      let vd_args, _, exp_args =
        mk_var (Tarray (Tclass (Names.pervasives_qn "String"), [Sint 0])) "args" in

      let get_arg i = Earray_elem(exp_args, [Sint i]) in

      let body =
        let vd_main, e_main, q_main, ty_main =
          let q_main = Obc2java.qualname_to_package_classe q_main in (*java qual*)
          let id = Idents.gen_var "java_main" "main" in
          mk_var_dec id (Tclass q_main), Evar id, q_main, ty_main
        in
        let acts =
          let out = Eclass(Names.qualname_of_string "java.lang.System.out") in
          let jarrays = Eclass(Names.qualname_of_string "java.util.Arrays") in
          let jint = Eclass(Names.qualname_of_string "Integer") in
          let jfloat = Eclass(Names.qualname_of_string "Float") in
          let jbool = Eclass(Names.qualname_of_string "Boolean") in
          let jsys = Eclass(Names.qualname_of_string "java.lang.System") in
          let jminus = pervasives_qn "-" in

          (* parse arguments to give to the main *)
          let rec parse_args t_l i = match t_l with
            | [] -> []
            | t::t_l when t = Initial.tint ->
                (Emethod_call(jint, "parseInt", [get_arg i]))
                :: parse_args t_l (i+1)
            | t::t_l when t = Initial.tfloat ->
                (Emethod_call(jfloat, "parseFloat", [get_arg i]))
                :: parse_args t_l (i+1)
            | t::t_l when t = Initial.tint ->
                (Emethod_call(jbool, "parseBool", [get_arg i]))
                :: parse_args t_l (i+1)
            | _ -> Misc.unsupported "java main does not support parsing complexe static args"
          in
          let main_args = parse_args ty_main_args 0 in

          let parse_max_iteration =
            let t_size = List.length ty_main_args in
            (* no more arg to give to main, the last one if it exists is the iteration nb *)
            Aifelse(Efun(Names.pervasives_qn ">", [ Efield (exp_args, "length"); Sint t_size ]),
                    (* given max number of iterations *)
                    mk_block [Aassgn(pat_step,
                              Emethod_call(jint, "parseInt", [get_arg t_size]))],
                    (* default max number of iterations *)
                    mk_block [Aassgn(pat_step, Evar id_step_dnb)]);
          in
          let ty_ret = Obc2java.ty NamesEnv.empty ty_main in
          let vd_ret, pat_ret, exp_ret = mk_var ty_ret "ret" in
          let call_main = match ty_ret with
            | Tunit -> Aexp(Emethod_call(e_main, "step", []))
            | _ -> Anewvar (vd_ret, Emethod_call(e_main, "step", []))
          in
          let print_ret = match ty_ret with
            | Tunit -> Sstring ""
            | Tarray (Tarray _, _) -> Emethod_call(jarrays, "deepToString", [exp_ret])
            | Tarray _ -> Emethod_call(jarrays, "toString", [exp_ret])
            | Tint -> Emethod_call(jint, "toString", [exp_ret])
            | Tfloat -> Emethod_call(jfloat, "toString", [exp_ret])
            | Tbool -> Emethod_call(jbool, "toString", [exp_ret])
            | _ -> Emethod_call(exp_ret, "toString", [])
          in
          let main_for_loop i =
            [call_main; Aexp (Emethod_call(out, "printf",
                                [Sstring "%d => %s\\n"; Evar i; print_ret]))]
          in
          let vd_t1, e_t1 =
            let id = Idents.gen_var "java_main" "t" in
            mk_var_dec id Tlong, Evar id
          in
          [ Anewvar(vd_main, Enew (Tclass q_main, main_args));
            parse_max_iteration;
            Anewvar(vd_t1, Emethod_call(jsys, "currentTimeMillis", []));
            Obc2java.fresh_for exp_step main_for_loop;
            Aexp (Emethod_call(out, "printf",
              [ Sstring "time : %d\\n";
                Efun(jminus, [Emethod_call(jsys, "currentTimeMillis", []); e_t1])]));
            Aexp(Emethod_call(jsys, "exit", [Sint 0]))
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
