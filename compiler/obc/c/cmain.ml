(***********************************************************************)
(*                                                                     *)
(*                             Heptagon                                *)
(*                                                                     *)
(* Gwenael Delaval, LIG/INRIA, UJF                                     *)
(* Leonard Gerard, Parkas, ENS                                         *)
(* Adrien Guatto, Parkas, ENS                                          *)
(* Cedric Pasteur, Parkas, ENS                                         *)
(* Marc Pouzet, Parkas, ENS                                            *)
(*                                                                     *)
(* Copyright 2012 ENS, INRIA, UJF                                      *)
(*                                                                     *)
(* This file is part of the Heptagon compiler.                         *)
(*                                                                     *)
(* Heptagon is free software: you can redistribute it and/or modify it *)
(* under the terms of the GNU General Public License as published by   *)
(* the Free Software Foundation, either version 3 of the License, or   *)
(* (at your option) any later version.                                 *)
(*                                                                     *)
(* Heptagon is distributed in the hope that it will be useful,         *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of      *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the       *)
(* GNU General Public License for more details.                        *)
(*                                                                     *)
(* You should have received a copy of the GNU General Public License   *)
(* along with Heptagon.  If not, see <http://www.gnu.org/licenses/>    *)
(*                                                                     *)
(***********************************************************************)

open List
open Containers
open Names
open Idents
open Obc
open Obc_utils
open Types
open Signature
open C
open Cgen
open Compiler_utils

(** {1 Main C function generation} *)

let _ = Idents.enter_node (Modules.fresh_value "cmain" "main")

let fresh n = Idents.name (Idents.gen_var "cmain" n)

(* Order*)
let order_list lposelem =
  let lsorted = List.sort (fun (a, _) (b,_) -> a - b) lposelem in
  List.map (fun (_,e) -> e) lsorted


let mk_int i = Cconst (Ccint i)
let mk_float f = Cconst (Ccfloat f)

(* Unique names for C variables handling step counts. *)
let step_counter = fresh "step_c"
and max_step = fresh "step_max"

let assert_node_res cd =
  let stepm = find_step_method cd in
  if List.length stepm.m_inputs > 0 then
    (Format.eprintf "Cannot generate run-time check for node %s with inputs.@."
       (cname_of_qn cd.cd_name);
     exit 1);
  if (match stepm.m_outputs with
        | [{ v_type = Tid nbool; }] when nbool = Initial.pbool -> false
        | _ -> true) then
    (Format.eprintf
       "Cannot generate run-time check for node %s with non-boolean output.@."
       (cname_of_qn cd.cd_name);
     exit 1);
  let name = cname_of_qn cd.cd_name in
  let out =
    (fresh ("out_for_" ^ name),
      Cty_id (qn_append cd.cd_name "_out")) in
  let mem, reset_i =
    if not cd.cd_stateful
    then ([], [])
    else
      let mem =
        (fresh ("mem_for_" ^ name), Cty_id (qn_append cd.cd_name "_mem")) in
      ([mem],
       [Csexpr (Cfun_call (name ^ "_reset", [Caddrof (Cvar (fst mem))]))]) in
  let step_i =
    (*
      step(&out, &mem);
      if (!out.proper_name) {
        printf("Node $node failed at step %d.\n", step_count);
        return 1;
      }
    *)
    let outn = Idents.name ((List.hd stepm.m_outputs).v_ident) in
    Csblock
      { var_decls = [];
        block_body =
          [
            Csexpr (Cfun_call (name ^ "_step",
                               Caddrof (Cvar (fst out))
                               :: (if cd.cd_stateful
                                   then [Caddrof (Cvar (fst (List.hd mem)))]
                                   else [])));
            Cif (Cuop ("!", Cfield (Cvar (fst out), local_qn outn)),
                 [Csexpr (Cfun_call ("fprintf",
                                     [Cvar "stderr";
                                      Cconst (Cstrlit ("Node \""
                                                       ^ (Names.fullname cd.cd_name)
                                                            ^ "\" failed at step" ^
                                                              " %d.\n"));
                                      Cvar step_counter]));
                  Creturn (mk_int 1)],
                 []);
          ];
      } in
  (out :: mem, reset_i, step_i);;

(** [main_def_of_class_def_simul cd] returns a [(var_list, rst_i, step_i)] where
    [var_list] (resp. [rst_i] and [step_i]) is a list of variables (resp. of
    statements) needed for a main() function calling [cd]. *)
let main_def_of_class_def cd =
  let format_for_type ty = match ty with
    | Tarray _ | Tprod _ | Tclasstype _ | Tinvalid -> assert false
    | Types.Tid id when id = Initial.pfloat -> "%f"
    | Types.Tid id when id = Initial.pint -> "%d"
    | Types.Tid id when id = Initial.pbool -> "%d"
    | Tid _ -> "%s"
  in

  (* Does reading type [ty] need a buffer? When it is the case,
     [need_buf_for_ty] also returns the type's name. *)
  let need_buf_for_ty ty = match ty with
    | Tarray _ | Tprod _ | Tclasstype _ | Tinvalid -> assert false
    | Types.Tid id when id = Initial.pfloat -> None
    | Types.Tid id when id = Initial.pint -> None
    | Types.Tid id when id = Initial.pbool -> None
    | Tid tn -> Some (cname_of_qn tn)
  in
  let cprint_string s = Csexpr (Cfun_call ("printf", [Cconst (Cstrlit s)])) in

  (* Generates scanf statements. *)
  let rec read_lhs_of_ty lhs ty =
    match ty with
    | Tarray (ty, n) ->
        let iter_var = fresh "i" in
        let lhs = Carray (lhs, Cvar iter_var) in
        let (reads, bufs) = read_lhs_of_ty lhs ty in
        ([Cfor (iter_var, mk_int 0, cexpr_of_static_exp n, reads)], bufs)
    | (Tid tn) as ty ->
        begin match Modules.find_type tn with
        | Talias ty -> read_lhs_of_ty lhs ty
        | Tstruct field_list ->
            List.fold_left
              (fun (reads,bufs)
                 { Signature.f_name = f_name; Signature.f_type = f_ty} ->
                 let f_lhs = Cfield(lhs,f_name) in
                 let (f_reads,f_bufs) = read_lhs_of_ty f_lhs f_ty in
                 (reads@f_reads),(bufs@f_bufs))
              ([],[])
              field_list
        | _ ->
            let rec mk_prompt lhs = match lhs with
              | Cvar vn -> (vn, [])
              | Carray (lhs, cvn) ->
                  let (vn, args) = mk_prompt lhs in
                  (vn ^ "[%d]", cvn :: args)
              | Cfield (lhs, fn) ->
                  let (vn, args) = mk_prompt lhs in
                  (vn ^ "." ^ (shortname fn), args)
              | _ -> assert false in
            let (prompt, args_format_s) = mk_prompt lhs in
            let scan_exp e =
              let printf_s = Format.sprintf "%s ? " prompt in
              let format_s = format_for_type ty in
              let exp_scanf = Cfun_call ("scanf", [Cconst (Cstrlit format_s); e]) in
              let body =
                if !Compiler_options.hepts_simulation
                then (* hepts: systematically test and quit when EOF *)
                  [Cif(Cbop("==",exp_scanf,Cvar("EOF")),
                       [Creturn(mk_int 0)],[])]
                else
                  [Csexpr (exp_scanf);] in
              let body =
                if !Compiler_options.hepts_simulation then
                  body
                else
                  Csexpr (Cfun_call ("printf",
                                     Cconst (Cstrlit printf_s)
                                     :: args_format_s))
                  :: body in
              Csblock { var_decls = [];
                        block_body = body; } in
            match need_buf_for_ty ty with
            | None -> ([scan_exp (Caddrof lhs)], [])
            | Some tyn ->
                let varn = fresh "buf" in
                let lhs = clhs_of_cexpr lhs in
                ([scan_exp (Cvar varn);
                  Caffect (lhs,
                           (Cfun_call (tyn ^ "_of_string",
                                     [Cvar varn])))],
                 [(varn, Cty_arr (20, Cty_char))])
        end
    | Tprod _ | Tclasstype _ | Tinvalid -> failwith("read_lhs_of_ty: untranslatable type")
  in

  (* Generates printf statements and buffer declarations needed for printing
     resulting values of enum types. *)
  let rec write_lhs_of_ty lhs ty =
    match ty with
    | Tarray (ty, n) ->
        let iter_var = fresh "i" in
        let lhs = Carray (lhs, Cvar iter_var) in
        let (writes, bufs) = write_lhs_of_ty lhs ty in
        let writes_loop =
          Cfor (iter_var, mk_int 0, cexpr_of_static_exp n, writes) in
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
                 let f_lhs = Cfield(lhs,f_name) in
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
              | Some sid -> [Cfun_call ("string_of_" ^ sid,
                                        [lhs;
                                         Cvar varn])] in
            ([Csexpr (Cfun_call ("printf",
                                 Cconst (Cstrlit (format_s))
                                 :: ep))],
             match nbuf_opt with
             | None -> []
             | Some _ -> [(varn, Cty_arr (20, Cty_char))])
        end
    | Tprod _ | Tclasstype _ | Tinvalid -> failwith("write_lhs_of_ty: untranslatable type")
  in

  let stepm = find_step_method cd in
  let (scanf_calls, scanf_decls) =
    let read_lhs_of_ty_for_vd vd =
      read_lhs_of_ty (Cvar (Idents.name vd.v_ident)) vd.v_type in
    split (map read_lhs_of_ty_for_vd stepm.m_inputs) in

  let (printf_calls, printf_decls) =
    let write_lhs_of_ty_for_vd vd =
      let (stm, vars) =
        write_lhs_of_ty (Cfield (Cvar "_res",
                                 local_qn (name vd.v_ident))) vd.v_type in
      if !Compiler_options.hepts_simulation then
        (stm, vars)
      else
        (cprint_string "=> " :: stm, vars)
    in
    split (map write_lhs_of_ty_for_vd stepm.m_outputs) in
  let printf_calls = List.concat printf_calls in

  let cinp = inputlist_of_ovarlist stepm.m_inputs in
  let cout = ["_res", (Cty_id (qn_append cd.cd_name "_out"))] in

  let mem_decl =
    if cd.cd_stateful
    then Some (Cvardef ("mem", Cty_id (qn_append cd.cd_name "_mem")))
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
        map (fun vd -> Cvar (name vd.v_ident)) stepm.m_inputs
        @ (Caddrof (Cvar "_res")
           :: if cd.cd_stateful then [Caddrof (Cvar "mem")] else []) in
      Cfun_call ((cname_of_qn cd.cd_name) ^ "_step", args) in
    concat scanf_calls
    @ [Csexpr funcall]
    @ printf_calls
    @
      (if !Compiler_options.hepts_simulation
       then []
       else [Csexpr (Cfun_call ("puts", [Cconst (Cstrlit "")]))])
    @ [Csexpr (Cfun_call ("fflush", [Cvar "stdout"]))] in

  (* Do not forget to initialize memory via reset if needed. *)
  let rst_i =
    if cd.cd_stateful
    then [Csexpr (Cfun_call ((cname_of_qn cd.cd_name) ^ "_reset",
                             [Caddrof (Cvar "mem")]))]
    else [] in

  (mem_decl, varlist, rst_i, step_l)

(** [main_skel_simul var_list prologue body] generates a C main() function using the
    variable list [var_list], prologue [prologue] and loop body [body]. *)
let main_skel_simul var_list prologue body =
  Cfundef {
    C.f_name = "main";
    f_retty = Cty_int;
    f_args = [("argc", Cty_int); ("argv", Cty_ptr (Cty_ptr Cty_char))];
    f_body = {
      var_decls =
        (step_counter, Cty_int) :: (max_step, Cty_int) :: var_list;
      block_body =
        [
          (*
            step_count = 0;
            max_step = 0;
            if (argc == 2)
              max_step = atoi(argv[1]);
          *)
          Caffect (CLvar step_counter, mk_int 0);
          Caffect (CLvar max_step, mk_int 0);
          Cif (Cbop ("==", Cvar "argc", mk_int 2),
               [Caffect (CLvar max_step,
                         Cfun_call ("atoi",
                                    [Carray (Cvar "argv",
                                             mk_int 1)]))], []);
        ]
        @ prologue
          (* while (!max_step || step_c < max_step) *)
        @ [
          Cwhile (Cbop ("||",
                        Cuop ("!", Cvar max_step),
                        Cbop ("<",
                              Cvar step_counter,
                              Cvar max_step)),
                  (* step_counter = step_counter + 1; *)
                  Caffect (CLvar step_counter,
                           Cbop ("+",
                                 Cvar step_counter,
                                 mk_int 1))
                  :: body);
          Creturn (mk_int 0);
        ];
    }
  } 

(* ----- *)
(* Posix parallel code generation *)
let main_def_of_class_def_parallel_CG cd =
  (* Hypothesis: there are no input/output to be managed here (due to the parallel scheduler used) *)
  (* If you wish to simulate some node, use a function "read_XXX" to implement the scanf
    and a function "write_XXX" to implement the printf *)

  (* === Form of the generated code ===
    int result_code;

    init_sync_counter(mem);

    // Lanch the CPU threads other than CPU_0
    result_code = pthread_create(&threads[1], NULL, (void * (*)(void *)) &work_CPU_1, mem);
    assert(result_code!=0);
    result_code = pthread_create(&threads[2], NULL, (void * (*)(void *)) &work_CPU_2, mem);
    assert(result_code!=0);

    // Launch CPU_0
    ( *work_CPU_0 )(mem);

    // Synchro with all other threads
    result_code = pthread_join(threads[1], NULL);
    assert(result_code!=0);
    result_code = pthread_join(threads[2], NULL);
    assert(result_code!=0);
    }
  *)
  let result_code_varname = "_result_code" in
  let var_result_code = (result_code_varname, Cty_int) in

  let arg_init_counter_fun = Cvar Posixprep.name_var_memory_main in (* Alternative? Cconst Ctag *)
  let init_counter_fun = Csexpr (Cfun_call (Posixprep.name_init_sync_counter_func, [arg_init_counter_fun])) in

  let rec create_join_thread_instr (lcreate, ljoin) n =
    assert(n>0);

    let larg_cr_instr = [
      Caddrof (Carray (Cvar "threads", Cconst (Ccint n)));
      Cconst (Ctag "NULL");
      Caddrof(Cvar (Posixprep.get_name_thread n));  (* TODO: (void * (*)(void *)) ??? => warning if do not put it *)
      Cvar Posixprep.name_var_memory_main
    ] in
    let cr_instr = Caffect (CLvar result_code_varname,
      Cfun_call (Posixprep.name_pthread_create, larg_cr_instr)
    ) in

    let larg_join_instr = [
      Carray (Cvar "threads", Cconst (Ccint n));
      Cconst (Ctag "NULL")
    ] in
    let join_instr = Caffect (CLvar result_code_varname,
      Cfun_call (Posixprep.name_pthread_join, larg_join_instr)
    ) in

    (* Finishing *)
    if (n=1) then (cr_instr::lcreate, join_instr::ljoin) else
    create_join_thread_instr (lcreate, ljoin) (n-1)
  in

  let (lcreate_thread, ljoin_thread) = create_join_thread_instr ([],[]) !Posixprep.rnum_thread in

  let launch_thread_0 = Csexpr (
    Cderef ( Cfun_call ( (Posixprep.get_name_thread 0), [Cvar Posixprep.name_var_memory_main] ) )
  ) in

  let body_while = [init_counter_fun] @ lcreate_thread
    @ [launch_thread_0] @ ljoin_thread in

  (* Reset function correspond to performing some malloc *)
  let reset_funcall =  if cd.cd_stateful then
      let arg_reset_funcall = Cvar Posixprep.name_var_memory_main in
      [Csexpr (Cfun_call ((cname_of_qn cd.cd_name) ^ "_reset", [arg_reset_funcall]))]
    else
      []
  in

  ([var_result_code], reset_funcall, body_while)


(* ----- *)
(* OpenCL code generation *)

let program_var_name kernel_name instnum = "program_" ^ kernel_name ^ "_" ^ (string_of_int instnum)
let kernel_var_name kernel_name instnum = "kernel_" ^ kernel_name ^ "_" ^ (string_of_int instnum)
let buffer_var_name kernel_name buffid = "buffer_" ^ kernel_name ^ "_" ^ (string_of_int buffid)


(* Remark: global declaration and OpenCL header file include are
 in a common file "hept_opencl.h" which does not change from a CG to another
    Also, all the info needed are already built in Openclprep *)
let get_opencl_prologue _ =
  (* Step 1 - architecture configuration *)
  let lvarloc_step1 =
    ("platform_id", Cty_id { qual = Pervasives; name = "cl_platform_id"})::
    ("num_platforms", Cty_id { qual = Pervasives; name = "cl_uint"})::
    ("device_id", Cty_id { qual = Pervasives; name = "cl_device_id"})::
    ("num_devices", Cty_id { qual = Pervasives; name = "cl_uint"})::
    ("context", Cty_id { qual = Pervasives; name = "cl_context"})::
    ("queue", Cty_id { qual = Pervasives; name = "cl_command_queue"})::[] in

  (* queues[i] = clCreateCommandQueue(context, device_id, 0, NULL); *)
  let (lstm_create_queues, _) = StringMap.fold (fun _ _ (lacc, i) ->
      let nstm = (Caffect ( CLarray ( (CLvar "queues"), Cconst (Ccint i)), (Cfun_call ("clCreateCommandQueue",
      [ Cvar "context";
        Cvar "device_id";
        Cconst (Ccint 0);
        Cconst (Ctag "NULL")
      ]
      )))) in
      (nstm::lacc, (i+1))
    ) !Openclprep.mQueueCL ([],0)
  in
  let lstm_step1 =
    (* platform_id = NULL; *)
    (Caffect ((CLvar "platform_id"), (Cconst (Ctag "NULL")))) ::
    (* clGetPlatformIDs(1, &platform_id, &num_platforms); *)
    (Csexpr (Cfun_call ("clGetPlatformIDs",
      [ Cconst (Ccint 1);
        Caddrof (Cvar "platform_id");
        Caddrof (Cvar "num_platforms")
      ]
    )))::
    (* device_id = NULL; *)
    (Caffect ((CLvar "device_id"), (Cconst (Ctag "NULL"))))::
    (* clGetDeviceIDs(platform_id, CL_DEVICE_TYPE_CUSTOM, 1, &device_id, &num_devices); *)
    (Csexpr (Cfun_call ("clGetDeviceIDs",
      [ Cvar "platform_id";
        Cconst (Ctag "CL_DEVICE_TYPE_CUSTOM");
        Cconst (Ccint 1);
        Caddrof (Cvar "device_id");
        Caddrof (Cvar "num_devices")
      ]
    )))::
    (* context = clCreateContext(NULL, num_devices, &device_id, NULL, NULL, NULL); *)
    (Caffect ((CLvar "context"), (Cfun_call ("clCreateContext",
      [ Cconst (Ctag "NULL");
        Cvar "num_devices";
        Caddrof (Cvar "device_id");
        Cconst (Ctag "NULL");
        Cconst (Ctag "NULL");
        Cconst (Ctag "NULL")
      ]
    ))))::
    lstm_create_queues
  in

  (* Step 2 & 3 - Kernel management *)
  (* Preparation *)
  let lKernelVar = IntMap.fold (fun cloid (qname, sign, _) acc ->
    let nprogname = program_var_name qname.name cloid in
    let nkername = kernel_var_name qname.name cloid in
    (qname, sign, nprogname, cloid, nkername)::acc
  ) !Openclprep.mKernelCL [] in

  let lvarloc_step2 =
    ("fp", Cty_ptr (Cty_id { qual = Pervasives; name = "FILE"}))::
    ("code", Cty_ptr (Cty_id { qual = Pervasives; name = "char"}))::
    ("code_size", Cty_id { qual = Pervasives; name = "size_t"})::[] in
  let lvarloc_step2 = List.fold_left (fun acc (_, _, nprogname, _, nkername) ->
    (nprogname, Cty_id { qual = Pervasives; name = "cl_program"})::
    (nkername, Cty_id { qual = Pervasives; name = "cl_kernel"})::acc
  ) lvarloc_step2 lKernelVar in

  (* For all kernels... *)
  let lstm_step2 = List.fold_left (fun acc (qname, kernsig, nprogname, _, nkername) ->
    (* fp = fopen("[program source location]", "r"); *)
    let nstmts_load = (Caffect ((CLvar "fp"), (Cfun_call ("fopen",
      [ Cconst (Cstrlit kernsig.Signature.k_srcbin);
        Cconst (Cstrlit "r")
      ]
    ))))::
    (* code = (char* ) malloc(MAX_SOURCE_SIZE); *)
    (Caffect ((CLvar "code"), (Cfun_call ("malloc", 
      [ Cconst (Ctag "MAX_SOURCE_SIZE") ]
    ))))::
    (* code_size = fread(code, 1, MAX_SOURCE_SIZE, fp); *)
    (Caffect ((CLvar "code_size"), (Cfun_call ("fread",
      [ Cvar "code";
        Cconst (Ccint 1);
        Cconst (Ctag "MAX_SOURCE_SIZE");
        Cvar "fp"
      ]
    ))))::
    (* fclose(fp); *)
    (Csexpr (Cfun_call ("fclose", [Cvar "fp"])))::[] in

    (* Switch if source or binary file *)
    let nstmts_prog = if (kernsig.k_issource) then
      (* Program from source file *)
      (* [nprogname] = clCreateProgramWithSource(context, 1, (const char ** ) &code, &code_size, NULL); *)
      (Caffect ((CLvar nprogname), (Cfun_call ("clCreateProgramWithSource",
        [ Cvar "context";
          Cconst (Ccint 1);
          Caddrof (Cvar "code");
          Caddrof (Cvar "code_size");
          Cconst (Ctag "NULL")
        ]
      ))))::
      (* clBuildProgram([nprogname], 1, &device_id, NULL, NULL, NULL);*)
      (Csexpr (Cfun_call ("clBuildProgram",
        [ Cvar nprogname;
          Cconst (Ccint 1);
          Caddrof (Cvar "device_id");
          Cconst (Ctag "NULL"); Cconst (Ctag "NULL"); Cconst (Ctag "NULL")
        ]
      )))::[]
    else
      (* Program from binary file *)
      (* [nprogname] = clCreateProgramWithBinary(context, 1, &device_id, &code_size, &code, NULL, NULL) *)
      (Caffect ((CLvar nprogname), (Cfun_call ("clCreateProgramWithBinary",
        [ Cvar "context";
          Cconst (Ccint 1);
          Caddrof (Cvar "device_id");
          Caddrof (Cvar "code_size");
          Caddrof (Cvar "code");
          Cconst (Ctag "NULL"); Cconst (Ctag "NULL")
        ]
      ))))::[]
    in

    (* [nkername] = clCreateKernel([nprogname], "[sig_kernel_name]", NULL);*)
    let nstmts_kernel = (Caffect ((CLvar nkername), (Cfun_call ("clCreateKernel",
      [ Cvar nprogname;
        Cconst (Cstrlit qname.name);
        Cconst (Ctag "NULL")
      ]
    ))))::[] in

    nstmts_load @ nstmts_prog @ nstmts_kernel @ acc
  ) [] lKernelVar in

  (* Step 4 & 5 - buffer construction + association *)
  
  (* lBufferVar: list of (qnameKernel, kernelsign, buffid, isInput, pos, buffname) *)
  let lBufferVar = IntMap.fold (fun cloid (qnameKernel, kernelsign, mBuffer) acc ->
    Openclprep.BoolIntMap.fold (fun (isInput, pos) (buffid,_) acc ->
      let buffname = buffer_var_name qnameKernel.name buffid in
      (qnameKernel, kernelsign, cloid, buffid, isInput, pos, buffname)::acc
    ) mBuffer acc
  ) !Openclprep.mBufferCL [] in
  let numInput = List.fold_left (fun acc (_, _, _, _, isInput, _, _) ->
    if isInput then acc+1 else acc
  ) 0 lBufferVar in
  let numInOutput = List.length lBufferVar in

  let rec find_kernelvar lKernelVar cloid = match lKernelVar with
    | [] -> failwith ("find_kernelvar : kernel occurrence " ^ (string_of_int cloid) ^ " was not found.")
    | (_, _, _, cid, kervar)::t ->
      if (cid=cloid) then kervar else find_kernelvar t cloid
  in
  
  let lvarloc_step4 = List.fold_left
    (fun acc (_, _, _, _, _, _, buffname) ->
      (buffname, Cty_id { qual = Pervasives; name = "cl_mem"})::acc
    ) [] lBufferVar
  in
  let lstm_step4 = List.fold_left
    (fun acc (_, kernelsign, cloid, _, isInput, pos, buffname) ->
      

      let flagRW = if isInput then "CL_MEM_READ_ONLY" else "CL_MEM_WRITE_ONLY" in
      let tyBuffer = if isInput then
          (List.nth kernelsign.k_input pos).a_type
        else
          (List.nth kernelsign.k_output pos).a_type
      in

      (* [buffname] = clCreateBuffer(context, CL_MEM_[READ/WRITE]_ONLY, [sizebuffer], NULL, NULL) *)
      let cstm_createbuff = (Caffect ((CLvar buffname), (Cfun_call ("clCreateBuffer",
        [ Cvar "context";
          Cconst (Ctag flagRW);
         (Cgen.type_to_sizeof tyBuffer);
          Cconst (Ctag "NULL"); Cconst (Ctag "NULL")
        ]
      )))) in

      let kernelvar = find_kernelvar lKernelVar cloid in
      (* We assume that all the inputs come before all the outputs *)
      let pos_buff = if isInput then pos else (numInput + pos) in

      (* clSetKernelArg([kernelvar], [pos], size_of(cl_mem), &[buffname])  - for input/output *)
      let cstm_setkernelarg = (Csexpr (Cfun_call ("clSetKernelArg",
        [ Cvar kernelvar;
          Cconst (Ccint pos_buff);
          Cfun_call ("sizeof", (Cconst (Ctag "cl_mem")::[]));
          Caddrof (Cvar buffname)
        ]
      ))) in
      acc @ [cstm_createbuff; cstm_setkernelarg]
    ) [] lBufferVar in

  (* Local memory - buffer namangement *)
  (* clSetKernelArg([kernelvar], [pos], [sizebuffer], NULL)  - for local var *)
  let lstm_step4_local = IntMap.fold (fun cloid (_, mcloid) acc ->
    IntMap.fold (fun pos argloc acc ->
      let kernelvar = find_kernelvar lKernelVar cloid in
      (* Local buffers comes after all input and output buffers *)
      let npos = numInOutput + pos in

      let nacc = (Csexpr (Cfun_call ("clSetKernelArg",
        [Cvar kernelvar;
          Cconst (Ccint npos);
          (Cgen.type_to_sizeof argloc.a_type);
          Cconst (Ctag "NULL")
        ]
      ))) :: acc
      in
      nacc
    ) mcloid acc
  ) !Openclprep.mLocalBuffCL [] in
  let lstm_step4 = lstm_step4 @ lstm_step4_local in

  (* Step 6 - Build global data structure *)
  let numKernel = IntMap.cardinal !Openclprep.mKernelCL in
  let numBuffer = !Openclprep.idbuffer in
  let lvarloc_step6 = 
    ("kernels", Cty_ptr (Cty_id { qual = Pervasives; name = "cl_kernel"}))::
    ("buffers", Cty_ptr (Cty_id { qual = Pervasives; name = "cl_mem"}))::[]
    (* ("kernels", Cty_arr (numKernel, Cty_id { qual = Pervasives; name = "cl_kernel"}))::
    ("buffers", Cty_arr (numBuffer, Cty_id { qual = Pervasives; name = "cl_mem"}))::[] *)
  in
  
  (* OLD (with arrays directly filled)
  let lkernelvarstr = order_list
    (List.map (fun (_, _, _, cloid, nkername) -> (cloid, nkername)) lKernelVar)
  in
  let lbuffervarstr = order_list 
    (List.map (fun (_, _, _, buffid, _, _, buffname) -> (buffid, buffname)) lBufferVar) in

  let lstm_step6 =
  (* kernels = { ..[kernelvarstr].. } *)
  (Caffect (CLvar "kernels", Carraylit (
    List.map (fun kervar -> Cvar kervar) lkernelvarstr
  ))) ::
  (* buffers = { ..[buffervarstr].. } *)
  (Caffect (CLvar "buffers", Carraylit (
    List.map (fun bufvar -> Cvar bufvar) lbuffervarstr
  ))) *)
  let lstm_step6_fill =
  (* kernels = malloc([numKernel] * sizeof(cl_kernel)) *)
  (Caffect ((CLvar "kernels"), Cfun_call ("malloc",
    [ Cbop ("*", (Cconst (Ccint numKernel)),
        Cfun_call ("sizeof", [Cconst (Ctag "cl_kernel")])
      )
    ]
  )))::
 (* buffers = malloc([numBuffer] * sizeof(cl_mem)) *)
  (Caffect ((CLvar "buffers"), Cfun_call ("malloc",
    [ Cbop ("*", (Cconst (Ccint numBuffer)),
        Cfun_call ("sizeof", [Cconst (Ctag "cl_mem")])
      )
    ]
  )))::[] in
  let lstm_step6_fill = lstm_step6_fill @
  (* kernels[...[cloid]... = ...[nkername]... *)
  (List.map (fun (_, _, _, cloid, nkername) ->
    Caffect (CLarray ( (CLvar "kernels"), Cconst (Ccint cloid)) , Cvar nkername)
  ) lKernelVar) @
  (* buffers[...[buffid]... = ...[buffname]... *)
  (List.map (fun (_, _, _, buffid, _, _, buffname) ->
    Caffect (CLarray ( (CLvar "buffers"), Cconst (Ccint buffid)) , Cvar buffname)
  ) lBufferVar) in

  (* [icl_data_struct_string].queues = queues; *)
  let lstm_step6_icl =
  (Caffect ((CLfield (CLvar (Openclprep.icl_data_struct_string), Modules.current_qual "queues"))
    , Cvar "queues"
  )) ::  
  (* [icl_data_struct_string].buffers = buffers; *)
  (Caffect ((CLfield (CLvar (Openclprep.icl_data_struct_string), Modules.current_qual "buffers"))
    , Cvar "buffers"
  )) ::
  (* [icl_data_struct_string].kernels = kernels; *)
  (Caffect ((CLfield (CLvar (Openclprep.icl_data_struct_string), Modules.current_qual "kernels"))
    , Cvar "kernels"
  )) :: [] in
  let lstm_step6 = lstm_step6_fill @ lstm_step6_icl in


  (* Wrapping things up *)
  let stm = lstm_step1 @ lstm_step2 @ lstm_step4 @ lstm_step6 in
  let lvarloc = lvarloc_step1 @ lvarloc_step2 @ lvarloc_step4 @ lvarloc_step6 in
  (stm, lvarloc)

let get_posix_prologue (type_mem_mainnode:string) num_thread =
  (* [type_mainnode]* mem; *)
  let mem_main = 
    (Posixprep.name_var_memory_main, Cty_ptr (Cty_id (Modules.current_qual type_mem_mainnode)))
  in

  (* mem = malloc(sizeof(type_mainnode)); *)
  let arg_malloc_call = Cfun_call ("sizeof", [Cconst (Ctag type_mem_mainnode)]) in
  let call_malloc = Csexpr (Cfun_call ("malloc", [arg_malloc_call])) in

  (* init_mutex(mem); *)
  let larg_call_init_mut = [Cvar Posixprep.name_var_memory_main] in
  let call_init_mutex = Csexpr (Cfun_call (Posixprep.name_init_mutex_func, larg_call_init_mut)) in
  
  (* pthread_t threads[NUM_THREADS]; *)
  let thread_array =
    ("threads", Cty_arr (num_thread, (Cty_id { qual = Pervasives; name = "pthread_t"})))
  in
  let stm = [call_malloc; call_init_mutex] in
  let lvarloc = [mem_main; thread_array] in
  (stm, lvarloc)


(* Main function for OpenCL is a while loop *)
let main_skel_opencl var_list prologue body =
  Cfundef {
    C.f_name = "main";
    f_retty = Cty_int;
    f_args = [("argc", Cty_int); ("argv", Cty_ptr (Cty_ptr Cty_char))];
    f_body = {
      var_decls = var_list;
      block_body =
        prologue (* Includes classical "reset" prologue + OpenCL init *)
        @ [
          (* Infinite while loop *)
          Cwhile (Cconst (Ccint 1), body);
          Creturn (mk_int 0);
        ];
    }
  }

(* ----- *)

let mk_main name p =
  if (!Compiler_options.simulation || !Compiler_options.opencl_cg) then (
      let classes = program_classes p in

      (* Assert nodes management (Boolean nodes) *)
      let n_names = !Compiler_options.assert_nodes in
      let find_class n =
        List.find (fun cd -> cd.cd_name.name = n) classes
      in
      let a_classes = List.fold_left
        (fun acc n -> try find_class n :: acc with Not_found -> acc)
        [] n_names
      in
      let (var_l, res_l, step_l) = List.fold_right (fun cd (var_l, res_l, step_l) ->
          let (var, res, step) = assert_node_res cd in
          (var @ var_l, res @ res_l, step :: step_l)
        ) a_classes ([], [], [])
      in


      (* Get the name of the main node (called by the while loop) *)
      let n =
        if (!Compiler_options.simulation) then
          !Compiler_options.simulation_node
        else
          (Misc.assert_1 !Compiler_options.mainnode).name
      in
      
      let (defs, var_l, res_l, step_l) =
        if (!Posixprep.rnum_thread>=1) then    (* Parallel CG *)
          let (nvar_l, res, nstep_l) = main_def_of_class_def_parallel_CG (find_class n) in
          ([],  nvar_l @ var_l, res, nstep_l @ step_l)
        else try
          let (mem, nvar_l, res, nstep_l) = main_def_of_class_def (find_class n) in
          let defs = match mem with None -> [] | Some m -> [m] in
          (defs, nvar_l @ var_l, res @ res_l, nstep_l @ step_l)
        with Not_found -> ([],var_l,res_l,step_l)
      in
      

      (* Prologues (in reverse order) *)
      (* - Reset *)
      let (prologue, var_l) = (res_l, var_l) in
      (* - Posix *)
      let (prologue, var_l) = if (!Compiler_options.parse_parsched_file) then
          let qname_mainnode = (Misc.assert_1 !Compiler_options.mainnode) in
          let name_type_mem_mainnode = (C.cname_of_qn qname_mainnode) ^ "_mem" in
          let (prol_posix, var_posix) =
            get_posix_prologue name_type_mem_mainnode !Posixprep.rnum_thread in
          (prol_posix @ prologue, var_posix @ var_l)
        else
          (prologue, var_l)
      in
      (* - OpenCL *)
      let (prologue, var_l) = if (!Compiler_options.opencl_cg) then
          let (prol_ocl, var_ocl) = get_opencl_prologue () in
          (prol_ocl @ prologue, var_ocl @ var_l)
        else
          (prologue, var_l)
      in

      (* Select the skeleton *)
      let main_skel = if (!Compiler_options.simulation) then
        main_skel_simul else main_skel_opencl
      in

      (* Final result *)
      [("_main.c", Csource (defs @ [main_skel var_l prologue step_l]));
       ("_main.h", Cheader ([name], []))]
  ) else
    []




(******************************)

let translate name prog =
  let modname = (Filename.basename name) in
  global_name := String.capitalize_ascii modname;
  (global_file_header modname prog) @ (mk_main name prog)

let program p =
  let filename =
    filename_of_name (cname_of_name (modul_to_string p.p_modname)) in
  let dirname = build_path (filename ^ "_c") in
  let dir = clean_dir dirname in
  let c_ast = translate filename p in
  let c_ast = if !Compiler_options.unroll_loops then List.map Cunroll.cfile c_ast else c_ast in
  C.output dir c_ast

let interface i =
  let filename =
    filename_of_name (cname_of_name (modul_to_string i.i_modname)) in
  let dirname = build_path (filename ^ "_c") in
  let dir = clean_dir dirname in
  let c_ast = interface_header (Filename.basename filename) i in
    C.output dir c_ast
