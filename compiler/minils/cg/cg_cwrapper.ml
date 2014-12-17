open Signature
open C

(* Problem : lopth input is computed from mls, but C names and signatures
   are built from Obc models. Thus we can't use CGen methods which use
   obc types which are not available when we generate a lopht model. Here
   we try to "guess" what would be the signature from the mls data we have.
  If there are changes in the compilation from mls to obc, it's likely that
  there will be a missmatch. *)

let build_c_array_power ty ty_elt size  op_name =
  let src = "src" and dest = "dest" in
  let cargs = [(src, Cgen.ctype_of_otype ty_elt) ; (dest, Cgen.ctype_of_otype ty)] in 
    Cfundef {
      f_name = op_name;
      f_retty = Cty_void;
      f_args = cargs;
      f_body =  
        {
          var_decls = [];
          block_body =
            let i = "i" in 
            [Cfor(i, Cconst (Ccint 0), Cconst (Ccint size),
              [Caffect (CLarray (CLvar dest, Cvar i), Cvar src)]
            )];
        };
    }

let build_c_array_constructor ty ty_elt size op_name =
    Cfundef {
      f_name = op_name;
      f_retty = Cty_void;
      f_args = [];
      f_body =  
        {
          var_decls = [];
          block_body = [];
        };
    }

let build_c_struct_constructor ty structure_def op_name =
  let field_to_carg {Signature.f_name ; f_type} = C.cname_of_name f_name.Names.name , Cgen.ctype_of_otype f_type
  and field_to_cparam {Signature.f_name} = C.Cvar (C.cname_of_name f_name.Names.name) in
  let src = "src" and dest = "dest" in
  let csname = 
    match Modules.unalias_type ty with
      | Types.Tid n -> cname_of_qn n
      | _ -> assert false
  in
    Cfundef {
      f_name = op_name;
      f_retty = Cty_void;
      f_args = List.map field_to_carg structure_def ;
      f_body =  
        {
          var_decls = [];
          block_body = [Caffect (CLvar dest, Cstructlit (csname, List.map field_to_cparam structure_def))];
        };
    }

let build_c_wrappers id_wstep id_wreset node_name ({node_stateful} as node) =
  (* let id_wstep = fun_id ^ "_wstep"
  and id_wreset = fun_id ^ "_wreset" *)
  let id_step = (C.cname_of_qn node_name) ^ "_step"
  and id_reset = (C.cname_of_qn node_name) ^ "_reset"
  and cty_mem = Cty_id (Cgen.qn_append node_name "_mem")
  and cty_out = Cty_id (Cgen.qn_append node_name "_out") in

  (* --- Step function --- *)
  let arg_name a = match a.a_name with
    | None -> assert false
    | Some name -> name
  in
  let output_cvar_of_arg a =
    let ty = Cgen.ctype_of_otype a.a_type in
    let ty = Cgen.pointer_type a.a_type ty in
    arg_name a, ty
  and input_cvar_of_arg a =
    let ty = Cgen.ctype_of_otype a.a_type in
    arg_name a, ty
  and copy_out_arg (id,ty) =
    let ty = (Cgen.unalias_ctype ty) in
    let lhs = match ty with
    | Cty_arr _ -> CLvar id   
    | _ -> CLderef (CLvar id)
    and rhs = Cfield (Cvar "_out", Names.local_qn id)  
    in
      Cgen.create_affect_stm lhs rhs ty
  in

  let in_args = List.map input_cvar_of_arg node.node_inputs
  and out_args = List.map output_cvar_of_arg node.node_outputs 
  in
  let source_args =
    in_args
  @ if node_stateful then [("_mem", Cty_ptr cty_mem) ; ("_dummy", Cty_int)] else []
  @ out_args 
  and dest_args =
    List.map (fun (id,_ty) -> Cvar id) in_args
  @ [Caddrof (Cvar "_out")] 
  @ (if node_stateful then [(Cvar "_mem")] else [])
  in
  let f_step_def = Cfundef {
    f_name = id_wstep;
    f_retty = Cty_void;
    f_args = source_args;
    f_body = {
      var_decls = [("_out", cty_out)];
      block_body =
          [Csexpr (Cfun_call (id_step, dest_args))]
        @ (List.flatten (List.map copy_out_arg out_args)) 
    }
  } in

  (* --- Reset function --- *)
  let f_reset_def = Cfundef {
    f_name = id_wreset;
    f_retty = Cty_void;
    f_args = [("_mem", Cty_ptr cty_mem) ; ("_dummy", Cty_ptr Cty_int)];
    f_body = {
      var_decls = [];
      block_body = [
        Csexpr (Cfun_call (id_reset, [(Cvar "_mem")]))]
    }
  } in

  if node_stateful then
    [f_reset_def ; f_step_def]
  else
    [f_step_def]
