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
       [Zigsexpr (Zigfun_call (name ^ "_reset", [Zigaddrof (Zigvar (fst mem))]))]) in
  let step_i =
    let outn = Idents.name ((List.hd stepm.m_outputs).v_ident) in
    Zigsblock
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

let main_def_of_class_def cd =
  let format_for_type ty = match ty with
    | Tarray _ | Tprod _ | Tinvalid -> assert false
    | Types.Tid id when id = Initial.pfloat -> "{f}"
    | Types.Tid id when id = Initial.pint -> "{d}"
    | Types.Tid id when id = Initial.pbool -> "{b}"
    | Tid _ -> "{s}"
  in

  (* Does reading type [ty] need a buffer? When it is the case,
     [need_buf_for_ty] also returns the type's name. *)
  let need_buf_for_ty ty = match ty with
    | Tarray _ | Tprod _ | Tinvalid -> assert false
    | Types.Tid id when id = Initial.pfloat -> None
    | Types.Tid id when id = Initial.pint -> None
    | Types.Tid id when id = Initial.pbool -> None
    | Tid tn -> Some (zigname_of_qn tn)
  in
  let cprint_string s = Zigsexpr (Zigfun_call ("printf", [Zigconst (Zigstrlit s)])) in

  (* Generates scanf statements. *)
  let rec read_lhs_of_ty lhs ty =
    match ty with
    | Tarray (ty, n) ->
        let iter_var = fresh "i" in
        let lhs = Zigarray (lhs, Zigvar iter_var) in
        let (reads, bufs) = read_lhs_of_ty lhs ty in
        ([Zigfor (iter_var, mk_int 0, zigexpr_of_static_exp n, reads)], bufs)
    | (Tid tn) as ty ->
        begin match Modules.find_type tn with
        | Talias ty -> read_lhs_of_ty lhs ty
        | Tstruct field_list ->
            List.fold_left
              (fun (reads,bufs)
                 { Signature.f_name = f_name; Signature.f_type = f_ty} ->
                 let f_lhs = Zigfield(lhs,f_name) in
                 let (f_reads,f_bufs) = read_lhs_of_ty f_lhs f_ty in
                 (reads@f_reads),(bufs@f_bufs))
              ([],[])
              field_list
        | _ ->
            let rec mk_prompt lhs = match lhs with
              | Zigvar vn -> (vn, [])
              | Zigarray (lhs, cvn) ->
                  let (vn, args) = mk_prompt lhs in
                  (vn ^ "[%d]", cvn :: args)
              | Zigfield (lhs, fn) ->
                  let (vn, args) = mk_prompt lhs in
                  (vn ^ "." ^ (shortname fn), args)
              | _ -> assert false in
            let (prompt, args_format_s) = mk_prompt lhs in
            let scan_exp e =
              let printf_s = Format.sprintf "%s ? " prompt in
              let format_s = format_for_type ty in
              let exp_scanf = Zigfun_call ("scanf", [Zigconst (Zigstrlit format_s); e]) in
              let body =
                if !Compiler_options.hepts_simulation
                then (* hepts: systematically test and quit when EOF *)
                  [Zigif(Zigbop("==",exp_scanf,Zigvar("EOF")),
                       [Zigreturn(mk_int 0)],[])]
                else
                  [Zigsexpr (exp_scanf);] in
              let body =
                if !Compiler_options.hepts_simulation then
                  body
                else
                  Zigsexpr (Zigfun_call ("printf",
                                     Zigconst (Zigstrlit printf_s)
                                     :: args_format_s))
                  :: body in
              Zigsblock { var_decls = [];
                        block_body = body; } in
            match need_buf_for_ty ty with
            | None -> ([scan_exp (Zigaddrof lhs)], [])
            | Some tyn ->
                let varn = fresh "buf" in
                let lhs = ziglhs_of_zigexpr lhs in
                ([scan_exp (Zigvar varn);
                  Zigaffect (lhs,
                           (Zigfun_call (tyn ^ "_of_string",
                                     [Zigvar varn])))],
                 [(varn, Zigty_arr (20, Zigty_char))])
        end
    | Tprod _ | Tinvalid -> failwith("read_lhs_of_ty: untranslatable type")
  in

  (* Generates printf statements and buffer declarations needed for printing
     resulting values of enum types. *)
  let rec write_lhs_of_ty lhs ty =
    match ty with
    | Tarray (ty, n) ->
        let iter_var = fresh "i" in
        let lhs = Zigarray (lhs, Zigvar iter_var) in
        let (writes, bufs) = write_lhs_of_ty lhs ty in
        let writes_loop =
          Zigfor (iter_var, mk_int 0, zigexpr_of_static_exp n, writes) in
        if !Compiler_options.hepts_simulation then
          ([writes_loop], bufs)
        else
          ([cprint_string "[ ";
            writes_loop;
            cprint_string "]"], bufs)
    | (Tid tn) as ty ->
        begin match Modules.find_type tn with
        | Talias ty -> write_lhs_of_ty lhs ty
        | Tstruct field_list ->
            List.fold_left
              (fun (writes,bufs)
                 { Signature.f_name = f_name; Signature.f_type = f_ty} ->
                 let f_lhs = Zigfield(lhs,f_name) in
                 let (f_writes,f_bufs) = write_lhs_of_ty f_lhs f_ty in
                 (writes@f_writes),(bufs@f_bufs))
              ([],[])
              field_list
        | _ ->
            let varn = fresh "buf" in
            let format_s = format_for_type ty in
            let format_s =
              if !Compiler_options.hepts_simulation
              then format_s ^ "\n"
              else format_s ^ " " in
            let nbuf_opt = need_buf_for_ty ty in
            let ep = match nbuf_opt with
              | None -> [lhs]
              | Some sid -> [Zigfun_call ("string_of_" ^ sid,
                                        [lhs;
                                         Zigvar varn])] in
            ([Zigsexpr (Zigfun_call ("printf",
                                 Zigconst (Zigstrlit (format_s))
                                 :: ep))],
             match nbuf_opt with
             | None -> []
             | Some _ -> [(varn, Zigty_arr (20, Zigty_char))])
        end
    | Tprod _ | Tinvalid -> failwith("write_lhs_of_ty: untranslatable type")
  in

  let stepm = find_step_method cd in
  let (scanf_calls, scanf_decls) =
    let read_lhs_of_ty_for_vd vd =
      read_lhs_of_ty (Zigvar (Idents.name vd.v_ident)) vd.v_type in
    split (map read_lhs_of_ty_for_vd stepm.m_inputs) in

  let (printf_calls, printf_decls) =
    let write_lhs_of_ty_for_vd vd =
      let (stm, vars) =
        write_lhs_of_ty (Zigfield (Zigvar "_res",
                                 local_qn (name vd.v_ident))) vd.v_type in
      if !Compiler_options.hepts_simulation then
  (stm, vars)
      else
  (cprint_string "=> " :: stm, vars)
    in
    split (map write_lhs_of_ty_for_vd stepm.m_outputs) in
  let printf_calls = List.concat printf_calls in

  let cinp = inputlist_of_ovarlist stepm.m_inputs in
  let cout = ["_res", (Zigty_id (qn_append cd.cd_name "_out"))] in

  let mem_decl =
    if cd.cd_stateful
    then Some (Zigvardef ("mem", Zigty_id (qn_append cd.cd_name "_mem")))
    else None
  in

  let varlist =
    cinp
    @ cout
    @ concat scanf_decls
    @ concat printf_decls in

  (* The main function loops (while (1) { ... }) reading arguments for our node
     and prints the results. *)
  let step_l =
    let funcall =
      let args =
        map (fun vd -> Zigvar (name vd.v_ident)) stepm.m_inputs
        @ (Zigaddrof (Zigvar "_res")
           :: if cd.cd_stateful then [Zigaddrof (Zigvar "mem")] else []) in
      Zigfun_call ((zigname_of_qn cd.cd_name) ^ "_step", args) in
    concat scanf_calls
    @ [Zigsexpr funcall]
    @ printf_calls
    @
      (if !Compiler_options.hepts_simulation
       then []
       else [Zigsexpr (Zigfun_call ("puts", [Zigconst (Zigstrlit "")]))])
    @ [Zigsexpr (Zigfun_call ("fflush", [Zigvar "stdout"]))] in

  (* Do not forget to initialize memory via reset if needed. *)
  let rst_i =
    if cd.cd_stateful
    then [Zigsexpr (Zigfun_call ((zigname_of_qn cd.cd_name) ^ "_reset",
                             [Zigaddrof (Zigvar "mem")]))]
    else [] in

  (mem_decl, varlist, rst_i, step_l)

let main_skel var_list prologue body =
  Zigfundef {
    Zig.f_name = "main";
    f_retty = Zigty_int;
    f_args = [("argc", Zigty_int); ("argv", Zigty_ptr (Zigty_ptr Zigty_char))];
    f_body = {
      var_decls =
        (step_counter, Zigty_int) :: (max_step, Zigty_int) :: var_list;
      block_body =
        [
          (*
            step_count = 0;
            max_step = 0;
            if (argc == 2)
              max_step = atoi(argv[1]);
          *)
          Zigaffect (ZigLvar step_counter, mk_int 0);
          Zigaffect (ZigLvar max_step, mk_int 0);
          Zigif (Zigbop ("==", Zigvar "argc", mk_int 2),
               [Zigaffect (ZigLvar max_step,
                         Zigfun_call ("atoi",
                                    [Zigarray (Zigvar "argv",
                                             mk_int 1)]))], []);
        ]
        @ prologue
          (* while (!max_step || step_c < max_step) *)
        @ [
          Zigwhile (Zigbop ("||",
                        Ziguop ("!", Zigvar max_step),
                        Zigbop ("<",
                              Zigvar step_counter,
                              Zigvar max_step)),
                  (* step_counter = step_counter + 1; *)
                  Zigaffect (ZigLvar step_counter,
                           Zigbop ("+",
                                 Zigvar step_counter,
                                 mk_int 1))
                  :: body);
          Zigreturn (mk_int 0);
        ];
    }
  }

let mk_main name p : Zig.zigfile =
  if !Compiler_options.simulation then (
      let classes = program_classes p in
      let n_names = !Compiler_options.assert_nodes in
      let find_class n =
        List.find (fun cd -> cd.cd_name.name = n) classes
      in

      let a_classes =
        List.fold_left
          (fun acc n ->
             try
               find_class n :: acc
             with Not_found -> acc)
          []
          n_names in

      let (var_l, res_l, step_l) =
        let add cd (var_l, res_l, step_l) =
          let (var, res, step) = assert_node_res cd in
          (var @ var_l, res @ res_l, step :: step_l) in
        List.fold_right add a_classes ([], [], []) in

      let n = !Compiler_options.simulation_node in
      let (defs, var_l, res_l, step_l) =
        try
          let (mem, nvar_l, res, nstep_l) = main_def_of_class_def (find_class n) in
          let defs = match mem with None -> [] | Some m -> [m] in
          (defs, nvar_l @ var_l, res @ res_l, nstep_l @ step_l)
        with Not_found -> ([],var_l,res_l,step_l) in

      ("_main.zig", ([name], (defs @ [main_skel var_l res_l step_l])));
  ) else
    ("_lolz.zig", ([], []))



(******************************)

let translate name prog =
  let modname = (Filename.basename name) in
  global_name := String.capitalize_ascii modname;
  (global_file_header modname prog) @ ([mk_main name prog])

let program p =
  let filename =
    filename_of_name (zigname_of_name (modul_to_string p.p_modname)) in
  let dirname = build_path (filename ^ "_zig") in
  let dir = clean_dir dirname in
  let zig_ast = translate filename p in
  let zig_ast = if !Compiler_options.unroll_loops then Zigunroll.zigfile zig_ast else zig_ast in
  Zig.output dir [zig_ast]

let interface i = ()
  (*let filename =
    filename_of_name (zigname_of_name (modul_to_string i.i_modname)) in
  let dirname = build_path (filename ^ "_zig") in
  let dir = clean_dir dirname in
  let zig_ast = interface_header (Filename.basename filename) i in
  Zig.output dir zig_ast*)