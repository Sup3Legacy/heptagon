(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

open Format
open List
open Misc
open Names
open Idents
open Obc
open Obc_utils
open Types
open Gpu

open Modules
open Signature
open Opencl
open Location
open Format

open Compiler_options

(* We will speak of work-items doing exactly the same job as clones and those doing similar
   job on different data due to a pmap as parallel work-items. *)
  
(** Used to know the level of parallelism we can apply on the GPU :
      Parallel is for functions without constraints and in a pmap
      WI is for functions whose type are GPU
      WG are for kernels *)
type parallelisation =
  | Parallel
  | WI
  | WG of int list

(* To contain all the needed informations on the kernels to launch in the Kernel_callers *)
module Kers = Map.Make(struct type t = int let compare = Pervasives.compare end)

(* Binds variables (as strings) to a pair (cty, mem_loc) *)
module Cenv =
struct
  include Map.Make(struct type t = string let compare = Pervasives.compare end)

  (* Returns the location of n in env *)
  let loc n env =
    match find n env with (_, l) -> l

  (* Returns the C type of n in env *)
  let ty n env =
    match find n env with (t, _) -> t
end

module Error =
struct
  type error =
    | Evar of string
    | Enode of string
    | Eno_unnamed_output
    | Ederef_not_pointer
    | Estatic_exp_compute_failed
    | Eunknown_method of string
    | Eillegal_cast

  let message loc kind = (match kind with
    | Evar name ->
        eprintf "%aCode generation : The variable name '%s' is unbound.@."
          print_location loc name
    | Enode name ->
        eprintf "%aCode generation : The node name '%s' is unbound.@."
          print_location loc name
    | Eno_unnamed_output ->
        eprintf "%aCode generation : Unnamed outputs are not supported.@."
          print_location loc
    | Ederef_not_pointer ->
        eprintf "%aCode generation : Trying to deference a non pointer type.@."
          print_location loc
    | Estatic_exp_compute_failed ->
        eprintf "%aCode generation : Computation of the value of the static \
                 expression failed.@."
          print_location loc
    | Eunknown_method s ->
        eprintf "%aCode generation : Methods other than step and \
                    reset are not supported (found '%s').@."
          print_location loc
          s
    | Eillegal_cast ->
        eprintf "%aCode generation : trying to cast a vector to global memory.@."
          print_location loc
     );
    raise Errors.Error
end

let qn_append q suffix =
  { qual = q.qual; name = q.name ^ suffix }

let rec struct_name ty =
  match ty with
  | Cty_id n -> n
  | _ -> assert false

let int_of_static_exp se =
  Static.int_of_static_exp QualEnv.empty se

let ref_of_var var ty = match ty with
	| Cty_arr _ -> var
  |  _ -> Cref var

(* Returns a list of pairs : names - mem_loc from a list of arg (node arguments) *)
let names_mem_of_arg_list argl =
  let remove_option ad = match ad.a_name with
    | Some n -> n, ad.a_mem
    | None -> Error.message no_location Error.Eno_unnamed_output
  in
  List.map remove_option argl

let is_stateful n =
  try
    let sig_info = find_value n in
      sig_info.node_stateful
  with
      Not_found -> Error.message no_location (Error.Enode (fullname n))

let is_kernel gpu = match gpu with
  | Parallel_kernel _ | Kernel -> true
  | _ -> false
let is_cpu gpu = gpu == CPU
let is_gpu gpu = (gpu == GPU) || is_kernel gpu

let is_clone par = not (par = Parallel)

(* Creates a block without declarations *)
let mk_block cstm =
  Csblock { var_decls = []; block_body = cstm }

let mk_int i = Cconst (Ccint i)

(******************************)

(** {2 Translation from Obc to OpenCL using our AST.} *)


(** [ctype_of_type ?ptr oty] translates the Obc type [oty] to a C
    type. We assume that identified types have already been defined
    before use. [ptr] is a boolean in case we should create a pointer.
*)
let rec ctype_of_otype ?(ptr = false) oty =
  match oty with
    | Types.Tid id when id = Initial.pint -> if ptr then Cty_ptr Cty_int else Cty_int
    | Types.Tid id when id = Initial.pfloat -> if ptr then Cty_ptr Cty_int else Cty_float
    | Types.Tid id when id = Initial.pbool -> if ptr then Cty_ptr Cty_int else Cty_int
    | Tid id -> if ptr then Cty_ptr (Cty_id id) else Cty_id id
    | Tarray(ty, n) -> Cty_arr(int_of_static_exp n, ctype_of_otype ty)
    | Tprod _ -> assert false
    | Tinvalid -> assert false

let copname = function
  | "="  -> "==" | "<>" -> "!=" | "&"  -> "&&" | "or" -> "||" | "+" -> "+"
  | "-" -> "-" | "*" -> "*" | "/" -> "/" | "*." -> "*" | "/." -> "/"
  | "+." -> "+" | "-." -> "-" | "<"  -> "<" | ">"  -> ">" | "<=" -> "<="
  | ">=" -> ">="
  | "~-" -> "-" | "not" -> "!" | "%" -> "%"
  | op   -> op

(** Translates an Obc var_dec to a tuple (name, (cty, location)). *)
let cvar_of_vd ?(ptr = false) vd =
    name vd.v_ident, (ctype_of_otype ~ptr:ptr vd.v_type, vd.v_mem)

(** Generates a tuple (name, (cty, location)) for a name used as a GPU memory. *)
let omem_of_vd name =
  name, (Oty_mem, Private)

let rec name_of_ext_value = function
  | { w_desc = Wvar v } -> name v
  | { w_desc = Wconst _ } -> assert false
  | { w_desc = Wmem v } -> name v
  | { w_desc = Wfield (e, _) } -> name_of_ext_value e
  | { w_desc = Warray (e, _) } -> name_of_ext_value e

let rec name_clhs_of_clhs = function
  | CLvar s -> s, CLvar s
  | CLderef clhs -> let s, clhs = name_clhs_of_clhs clhs in s, CLderef clhs
  | CLfield (clhs, f) -> let s, clhs = name_clhs_of_clhs clhs in s, CLfield (clhs, f)
  | CLarray (clhs, _) -> name_clhs_of_clhs clhs
  | OLenv_field _ -> assert false

let rec name_cexpr_of_cexpr cexpr = match cexpr with
  | Cvar x -> x, cexpr
  | Carray (cexpr, _) -> name_cexpr_of_cexpr cexpr
  | Cref cexpr -> let s, cexpr = name_cexpr_of_cexpr cexpr in s, Cderef cexpr
  | Cderef cexpr -> let s, cexpr = name_cexpr_of_cexpr cexpr in s, Cref cexpr
  | Cfield(Cderef (Cvar "self"), { name = x })
  | Cfield(Cderef (Cvar "out"), { name = x }) -> x, cexpr
  | Cfield(cexpr, qn) -> let s, cexpr = name_cexpr_of_cexpr cexpr in s, Cfield(cexpr, qn)
  | _ -> assert false

(** Translates a clhs into a cexpr *)
let rec cexpr_of_lhs = function
  | CLvar s -> Cvar s
  | CLderef lhs -> Cderef (cexpr_of_lhs lhs)
  | CLfield (lhs, qn) -> Cfield (cexpr_of_lhs lhs, qn)
  | CLarray (lhs, cexpr) -> Carray (cexpr_of_lhs lhs, cexpr)
  | OLenv_field f -> Oenv_field f

(** @return the unaliased version of a type. *)
let rec unalias_ctype cty = match cty with
  | Cty_id ty_name ->
    (try match find_type ty_name with
    | Talias ty -> unalias_ctype (ctype_of_otype ty)
    | _ -> Cty_id ty_name
     with Not_found -> Cty_id ty_name)
  | Cty_arr (n, cty) -> Cty_arr (n, unalias_ctype cty)
  | Cty_ptr cty -> Cty_ptr (unalias_ctype cty)
  | cty -> cty

(** @return the type of a constant *)
let cty_of_cconst cconst = match cconst with
  | Ccint _ -> Cty_int
  | Ccfloat _ -> Cty_float
  | Ctag _ -> Cty_int
  | Cstrlit _ -> Cty_ptr Cty_char
  | Cnull -> assert false
  | Oopt _ -> Cty_int

(** Adds a list of cvars to an Cenv. *)
let rec add_env l var_env = match l with
  | [] -> var_env
  | (s, (t, m)) :: l -> add_env l (Cenv.add s (t, m) var_env)

(** Returns the value associated with the cexpr [cexpr] in the Cenv [var_env].
    Expects the Types.gpu [gpu] of the function. *)
let rec assoc_env_cexpr gpu cexpr var_env = match cexpr with
  | Cvar x ->
      let (ty, mem) = Cenv.find x var_env in
      (unalias_ctype ty, mem)
  | Carray (cexpr, _) ->
      let (ty, mem) = assoc_env_cexpr gpu cexpr var_env in
      (array_base_ctype ty [1], mem)
  | Cref cexpr ->
      let (ty, mem) = assoc_env_cexpr gpu cexpr var_env in
      (Cty_ptr ty, mem)
  | Cderef cexpr ->
    (match assoc_env_cexpr gpu cexpr var_env with
    | Cty_ptr ty, mem -> ty, mem
    | _, _ -> Error.message no_location Error.Ederef_not_pointer)
  | Cfield(Cderef (Cvar "self"), { name = x }) ->
      let ty, mem = Cenv.find x var_env in
      if is_kernel gpu then
        ty, Global
      else if is_gpu gpu then
        ty, Local
      else
        ty, mem
  | Cfield(Cderef (Cvar "out"), { name = x }) -> Cenv.find x var_env
  | Cfield(x, f) ->
      let (ty, mem) = assoc_env_cexpr gpu x var_env in
      let n = struct_name ty in
      let fields = find_struct n in
      (ctype_of_otype ~ptr:(is_kernel gpu) (field_assoc f fields), mem)
  | Cconst c -> (cty_of_cconst c, Private)
  | Carrayint_lit (a :: b) ->
      let ty, _ =  assoc_env_cexpr gpu a var_env in
      Cty_arr(1 + List.length b, ty), Private
  | _ -> assert false

(** Returns the type associated with the lhs [lhs] in the Cenv [var_env].
    Expects the Types.gpu [gpu] of the function. *)
let rec assoc_type_lhs gpu lhs var_env = match lhs with
  | CLvar x -> unalias_ctype (Cenv.ty x var_env)
  | CLarray (lhs, _) ->
    let ty = assoc_type_lhs gpu lhs var_env in
    array_base_ctype ty [1]
  | CLderef lhs ->
    (match assoc_type_lhs gpu lhs var_env with
    | Cty_ptr ty -> ty
    | _ -> Error.message no_location Error.Ederef_not_pointer)
  | CLfield(CLderef (CLvar "self"), { name = x }) -> Cenv.ty x var_env
  | CLfield(CLderef (CLvar "out"), { name = x }) -> Cenv.ty x var_env
  | CLfield(x, f) ->
    let ty = assoc_type_lhs gpu x var_env in
    let n = struct_name ty in
    let fields = find_struct n in
    ctype_of_otype ~ptr:(is_kernel gpu) (field_assoc f fields)
  | OLenv_field _ -> assert false

(** Returns the value associated with the lhs [lhs] in the Cenv [var_env].
    Expects the Types.gpu [gpu] of the function. *)
let rec assoc_env_lhs gpu lhs var_env = match lhs with
  | CLvar x ->
      let (ty, mem) = Cenv.find x var_env in
      (unalias_ctype ty, mem)
  | CLarray (lhs, _) ->
    let (ty, mem) = assoc_env_lhs gpu lhs var_env in
    (array_base_ctype ty [1], mem)
  | CLderef lhs ->
    (match assoc_env_lhs gpu lhs var_env with
    | Cty_ptr ty, mem -> ty, mem
    | _, _ -> Error.message no_location Error.Ederef_not_pointer)
  | CLfield(CLderef (CLvar "self"), { name = x }) -> Cenv.find x var_env
  | CLfield(CLderef (CLvar "out"), { name = x }) -> Cenv.find x var_env
  | CLfield(x, f) ->
    let (ty, env) = assoc_env_lhs gpu x var_env in
    let n = struct_name ty in
    let fields = find_struct n in
    (ctype_of_otype ~ptr:(is_kernel gpu) (field_assoc f fields), env)
  | OLenv_field _ -> assert false

(** Returns a C expression computing the size of a type. *)
let rec size_of_ctype ty = match ty with
  | Cty_int -> Cfun_call ("sizeof", [Cvar ("int")])
  | Cty_float -> Cfun_call ("sizeof", [Cvar ("float")])
  | Cty_id qn -> Cfun_call ("sizeof", [Cvar (cname_of_qn qn)])
  | Cty_arr (i, ty) -> Cbop ("*", size_of_ctype ty, Cconst (Ccint i))
  | Cty_ptr ptr -> size_of_ctype ptr
  | _ -> assert false

(** Returns the offset created by the clhs [clhs] to access its variable.
    Expects a Cenv [env]. *)
let offset_of_clhs env clhs =
  let rec aux clhs = match clhs with
	  | CLfield(CLderef (CLvar "self"), { name = s })
	  | CLfield(CLderef (CLvar "out"), { name = s })
	  | CLvar s -> mk_int 0, Cenv.ty s env
	  | CLderef clhs -> aux clhs
	  | CLarray (clhs, cexpr) ->
	      let off, ty = aux clhs in
        (match ty with
          | Cty_arr (_, ty) -> Cbop ("+", off, Cbop("*", size_of_ctype ty, cexpr)), ty
          | _ -> assert false)
	  | CLfield _
	  | OLenv_field _ -> assert false
  in
  let (size, _) = aux clhs in
  size

(** Returns the offset created by the cexpr [cexpr] to access its variable, assuming that the
    cexpr is just an access to a variable. Expects a Cenv [env]. *)
let offset_of_cexpr env cexpr =
  let rec aux cexpr = match cexpr with
	  | Cfield(_, { name = s })
	  | Cvar s -> mk_int 0, Cenv.ty s env
    | Cref cexpr
	  | Cderef cexpr -> aux cexpr
	  | Carray (cexpr, i) ->
	      let off, ty = aux cexpr in
        (match ty with
          | Cty_arr (_, ty) -> Cbop ("+", off, Cbop("*", size_of_ctype ty, i)), ty
          | _ -> assert false)
	  | _ -> assert false
  in
  let (size, _) = aux cexpr in
  size

(** A C expression to call an OpenCL barrier. *)
let create_barrier =
  Csexpr (Cfun_call ("barrier", [Cvar "CLK_LOCAL_MEM_FENCE"]))

(** A C expression to wait for the completion of the command-queue. *)
let mk_wait_finish =
  mk_block [Csexpr (Cfun_call ("clFinish", [Oenv_field Command_queue]))]

(** Creates the expression to create the kernel [f]. *)
let generate_kernel dest f =
  Caffect (dest,
    Cfun_call ("clCreateKernel",
      Oenv_field Program :: Cconst (Cstrlit f) :: Cref (Oenv_field Error) :: []))

(** Creates the expression to set an argument [arg] to the kernel [ker]. *)
let generate_argument_kernel ker nbr arg =
  Caffect (OLenv_field Error,
    Cfun_call ("clSetKernelArg",
      ker :: nbr :: Cfun_call ("sizeof", [Cvar "cl_mem"]) ::
      Ccast ((Cty_ptr Cty_void), arg) :: []))

(** Creates the expression to create a buffer dest of type [ty]. *)
let generate_buffer dest ty =
  Caffect (dest,
	  Cfun_call ("clCreateBuffer",
	    Oenv_field Context :: Cconst (Oopt READ_WRITE) :: size_of_ctype ty ::
      Cconst Cnull :: Cref (Oenv_field Error) :: []))

(** Creates the expression to read [src] from the GPU with an optional offset. *)
let generate_mem_read ?(off=mk_int 0) dest src ty  =
	Caffect ((OLenv_field Error),
	  Cfun_call ("clEnqueueReadBuffer",
	    Oenv_field Command_queue :: src ::
	    Cconst (Oopt TRUE) :: off ::
	    size_of_ctype ty :: ref_of_var dest ty :: mk_int 0 :: Cconst Cnull ::
	    Cref (Oenv_field Event) :: []))

(** Creates the expression to read [src] from the GPU, generating an offset if necessary. *)
let generate_mem_partial_read env dest src ty =
  let _, cvar = name_cexpr_of_cexpr src in
  let off = offset_of_cexpr env src in
  generate_mem_read ~off:off (cexpr_of_lhs dest) cvar ty

(** Creates the expression to create a GPU buffer [dest] and copy [dest] in it. *)
let generate_mem_write dest src ty =
  Caffect (dest,
	  Cfun_call ("clCreateBuffer",
	    Oenv_field Context :: Cconst (Oopt COPY_READ) :: size_of_ctype ty ::
      ref_of_var src ty :: Cref (Oenv_field Error) :: []))

(** Creates the expression to copy [src] into the GPU buffer [dest],
    generating an offset if necessary. *)
let generate_mem_partial_write env dest src ty = match dest with
  | CLarray _ ->
		  let var, lhs = name_clhs_of_clhs dest in
      let cvar = cexpr_of_lhs lhs in
		  let off = offset_of_clhs env dest in
		  [ Cif (
		      Cuop("!", cvar),
		      [generate_buffer lhs (Cenv.ty var env)], []);
				Caffect ((OLenv_field Error),
				  Cfun_call ("clEnqueueWriteBuffer",
				    Oenv_field Command_queue :: cvar :: 
				    Cconst (Oopt TRUE) :: off :: 
				    size_of_ctype ty :: ref_of_var src ty :: mk_int 0 :: Cconst Cnull ::
				    Cref (Oenv_field Event) :: []))]
  | _ -> [generate_mem_write dest src ty]

(** Creates the expression to copy a value of type [ty] from [src] into [dest]. Expects the
    offset for writing [off_dest] and for reading [off_src]. *)
let generate_mem_copy dest src off_dest off_src ty =
    Caffect((OLenv_field Error),
      Cfun_call ("clEnqueueCopyBuffer",
        Oenv_field Command_queue :: src :: dest :: off_src :: off_dest ::
        size_of_ctype ty :: mk_int 0 :: Cconst Cnull :: Cref (Oenv_field Event) :: []))

(** Creates the expression to retain a memory object. *)
let generate_mem_retain arg  =
  Csexpr (Cfun_call ("clRetainMemObject", [arg]))

(** Creates the expression to release a memory.
    TODO : does not release the memory because of memory corruption with Nvidia after some time. *)
let generate_mem_release arg  =
  (*Cif (arg, [Csexpr (Cfun_call ("clReleaseMemObject", [arg]))], [])*)
  Cif (arg, [Csexpr (Cfun_call ("printf", [Cconst (Cstrlit "Should release memory\\n")]))], [])

(** Creates the expressions to release the GPU memories of a list of variables when possible. *)
let rec rel_of_varlist gpu vars = match vars with
  | [] -> []
  | (s, (_, l)) :: vars ->
      if is_cpu gpu & l = Global then
         generate_mem_release (Cvar s) :: rel_of_varlist gpu vars
      else
        rel_of_varlist gpu vars

(** Creates the expressions to release the GPU memories of a list of persistent
    memories when possible. *)
let rec rel_of_memlist gpu vars = match vars with
  | [] -> []
  | (s, (_, l)) :: vars ->
      if is_cpu gpu & l = Global then
        generate_mem_release (Cfield (Cderef (Cvar "self"), local_qn s)) ::
          rel_of_memlist gpu vars
      else
        rel_of_memlist gpu vars

(** Creates the statement a = [e_1, e_2, ..], which gives a list
    a[i] = e_i.*)
let rec create_affect_lit gpu env parallel dest l ty mem_d mem_s =
  let rec _create_affect_lit dest i = function
    | [] -> []
    | v::l ->
        let stm = create_affect_stm gpu env parallel
          (CLarray (dest, Cconst (Ccint i))) v ty mem_d mem_s in
        stm @(_create_affect_lit dest (i+1) l)
  in
  _create_affect_lit dest 0 l

(** Creates the expression dest <- src (doing automatic memory transfers
    and copying arrays if necessary). *)
and create_affect_stm ?(bar = true) gpu env parallel dest src ty mem_d mem_s =
  (* Transfers between GPU memories on the CPU side. *)
  if is_cpu gpu & mem_d = Global & mem_s = Global then
    match dest with
      | CLfield (CLderef (CLvar "self"), _) -> [Caffect (dest, src)]
      | CLarray (_, _) ->
          let var_out, clhs = name_clhs_of_clhs dest in
          let cvar_out = cexpr_of_lhs clhs in
          let off_l = offset_of_clhs env dest in
				  let _, cvar_in = name_cexpr_of_cexpr src in
				  let off_r = offset_of_cexpr env src in
          [ Cif (
              cvar_out,
              [generate_buffer clhs (Cenv.ty var_out env)], []);
            generate_mem_copy cvar_out cvar_in off_l off_r ty]
      | _ -> Caffect (dest, src) :: generate_mem_retain (cexpr_of_lhs dest) :: []
  (* Transfers from a CPU memory to a GPU memory. *)
    else if is_cpu gpu & mem_d = Global & mem_s != Global then
    match src with
		  | Cvar _
		  | Cref _
		  | Cderef _
		  | Cfield _
		  | Carray _ -> generate_mem_partial_write env dest src ty
      | _ ->
          let new_v = fresh "v" in
          let affect = create_affect_stm gpu env parallel (CLvar new_v) src ty Private mem_s in
          let copy = generate_mem_partial_write env dest (Cvar new_v) ty in
          [Csblock {
            var_decls = [new_v, (ty, Private)];
            block_body = affect @ copy;
          }]
  (* Transfers from a GPU memory to a CPU memory. *)
  else if is_cpu gpu & mem_d != Global & mem_s = Global then
    [generate_mem_partial_read env dest src ty]
  else
    (* Must synchronize after all reads to persistent memory on the GPU when in clone mode. *)
    let barrier_read = match src with
      | Cfield (Cderef (Cvar "self"), _) when is_gpu gpu & parallel -> [create_barrier]
      | _ -> []
    in
	  match ty with
      (* Creates a loop to copy arrays. *)
	    | Cty_arr (n, bty) ->
	        (match src with
           | Carrayint_lit l -> create_affect_lit gpu env parallel dest l bty mem_d mem_s
           | src ->
              let x = gen_symbol () in
              let loc_id = Cfun_call ("get_local_id", [Cconst (Ccint 0)]) in
              let create_loop b step parallel mem_d mem_s =
                Cfor(x,
				             b, mk_int n, step,
				             create_affect_stm ~bar:false gpu env parallel
				               (CLarray (dest, Cvar x))
				               (Carray (src, Cvar x)) bty
			                 mem_d mem_s)
              in
              match bty with
                (* When copying an array, parallelizes the inner loop if possible *)
                | Cty_arr _ when is_gpu gpu & parallel ->
			              [create_loop (mk_int 0) (mk_int 1) parallel mem_d mem_s;
                    create_barrier]
                | _ when is_gpu gpu & parallel ->
                    let create_barrier = if bar then [create_barrier] else [] in
                    (* Supresses the loop if possible when parallel. *)
                    if (n = !size_workgroup) then
                      create_affect_stm gpu env false (CLarray (dest, loc_id))
                        (Carray (src, loc_id)) bty Private Private @
		                  create_barrier
                    else if (n < !size_workgroup) then
                      Cif (Cbop("<", loc_id, mk_int n),
                        create_affect_stm gpu env false (CLarray (dest, loc_id))
                          (Carray (src, loc_id)) bty Private Private, []) ::
		                  create_barrier
                    else
		                  create_loop loc_id
		                    (mk_int !size_workgroup) false Private Private ::
			                create_barrier
                | _ ->
			              [create_loop (mk_int 0) (mk_int 1) parallel mem_d mem_s]
	        )
	    | Cty_id ln ->
          (* Copies manually all the fields of a structure. *)
	        (match src with
	          | Cstructlit (_, ce_list) ->
	              let create_affect { f_name = f_name;
	                                  Signature.f_type = f_type; } e stm_list =
	                let cty = ctype_of_otype f_type in
	                create_affect_stm gpu env parallel
                    (CLfield (dest, f_name)) e cty mem_d mem_s  @ stm_list in
	              List.fold_right2 create_affect (find_struct ln) ce_list [] @
                barrier_read
	          | _ -> Caffect (dest, src) :: barrier_read)
	    | _ -> Caffect (dest, src) :: barrier_read

(** [cexpr_of_static_exp exp] translates the static_exp [se] to a C expression. *)
let rec cexpr_of_static_exp se =
  match se.se_desc with
    | Sint i -> Cconst (Ccint i)
    | Sfloat f -> Cconst (Ccfloat f)
    | Sbool b -> Cconst (Ctag (if b then "true" else "false"))
    | Sstring s -> Cconst (Cstrlit s)
    | Sfield _ -> assert false
    | Sconstructor c -> Cconst (Ctag (cname_of_qn c))
    | Sarray sl -> Carrayint_lit (List.map cexpr_of_static_exp sl)
    | Srecord fl ->
        let ty_name =
          match Modules.unalias_type se.se_ty with
            | Types.Tid n -> cname_of_qn n
            | _ -> assert false
        in
          Cstructlit (ty_name,
                     List.map (fun (_, se) -> cexpr_of_static_exp se) fl)
    | Sarray_power(c,n_list) ->
          (List.fold_left (fun cc n -> Carrayint_lit (repeat_list cc (int_of_static_exp n)))
                     (cexpr_of_static_exp c) n_list)
    | Svar ln ->
        (try
          let cd = find_const ln in
          cexpr_of_static_exp (Static.simplify QualEnv.empty cd.c_value)
        with Not_found -> assert false)
    | Sop _ ->
        let se' = Static.simplify QualEnv.empty se in
          if se = se' then
            Error.message se.se_loc Error.Estatic_exp_compute_failed
          else
            cexpr_of_static_exp se'
    | Stuple _ -> assert false (** TODO *)


(** [cexpr_of_exp exp] translates the Obj action [exp] to a C expression. *)
let rec cexpr_of_exp gpu out_env var_env exp =
  match exp.e_desc with
    | Eextvalue w  -> cexpr_of_ext_value gpu out_env var_env w
    (** Operators *)
    | Eop(op, exps) -> cop_of_op gpu out_env var_env op exps
    (** Structure literals. *)
    | Estruct (tyn, fl) ->
        let cexps = List.map (fun (_,e) -> cexpr_of_exp gpu out_env var_env e) fl in
        let ctyn = cname_of_qn tyn in
        Cstructlit (ctyn, cexps)
    | Earray e_list ->
        Carrayint_lit (cexprs_of_exps gpu out_env var_env e_list)

and cexprs_of_exps gpu out_env var_env exps =
  List.map (cexpr_of_exp gpu out_env var_env) exps

and cop_of_op_aux op_name cexps = match op_name with
    | { qual = Pervasives; name = op } ->
        begin match op,cexps with
          | "~-", [e] -> Cuop ("-", e)
          | "not", [e] -> Cuop ("!", e)
          | (
              "=" | "<>"
            | "&" | "or"
            | "+" | "-" | "*" | "/"
            | "*." | "/." | "+." | "-." | "%"
            | "<" | ">" | "<=" | ">="), [el;er] ->
              Cbop (copname op, el, er)
          | _ -> Cfun_call(op, cexps)
        end
    | { name = op } -> Cfun_call(op,cexps)

(** Translates a Pervasives operator to a C expression *)
and cop_of_op gpu out_env var_env op_name exps =
  let cexps = cexprs_of_exps gpu out_env var_env exps in
  cop_of_op_aux op_name cexps

and clhs_of_pattern gpu out_env var_env l = match l.pat_desc with
  (** Each Obc variable corresponds to a real local C variable. *)
  | Lvar v ->
      let n = name v in
      let n_lhs =
        if IdentSet.mem v out_env & not (is_gpu gpu)
        then CLfield (CLderef (CLvar "out"), local_qn n)
        else CLvar n
      in

      if Cenv.mem n var_env then
        let ty = Cenv.ty n var_env in
        (match ty with
           | Cty_ptr _ -> CLderef n_lhs
           | _ -> n_lhs
        )
      else
        n_lhs
  (** Dereference our [self] struct holding the node's memory. *)
  | Lmem v -> CLfield (CLderef (CLvar "self"), local_qn (name v))
  (** Field access. /!\ Indexed Obj expression should be a valid lhs!  *)
  | Lfield (l, fn) -> CLfield(clhs_of_pattern gpu out_env var_env l, fn)
  | Larray (l, idx) ->
      CLarray(clhs_of_pattern gpu out_env var_env l,
              cexpr_of_exp gpu out_env var_env idx)

and clhs_list_of_pattern_list gpu out_env var_env lhss =
  List.map (clhs_of_pattern gpu out_env var_env) lhss

and cexpr_of_pattern gpu out_env var_env l = match l.pat_desc with
  (** Each Obc variable corresponds to a real local C variable. *)
  | Lvar v ->
      let n = name v in
      let n_lhs =
        if IdentSet.mem v out_env & not (is_gpu gpu)
        then Cfield (Cderef (Cvar "out"), local_qn n)
        else Cvar n
      in

      if Cenv.mem n var_env then
        let ty = Cenv.ty n var_env in
        (match ty with
           | Cty_ptr _ -> Cderef n_lhs
           | _ -> n_lhs
        )
      else
        n_lhs
  (** Dereference our [self] struct holding the node's memory. *)
  | Lmem v -> Cfield (Cderef (Cvar "self"), local_qn (name v))
  (** Field access. /!\ Indexed Obj expression should be a valid lhs!  *)
  | Lfield (l, fn) -> Cfield(cexpr_of_pattern gpu out_env var_env l, fn)
  | Larray (l, idx) ->
      Carray(cexpr_of_pattern gpu out_env var_env l,
             cexpr_of_exp gpu out_env var_env idx)

and cexpr_of_ext_value gpu out_env var_env w = match w.w_desc with
  | Wconst c -> cexpr_of_static_exp c
  (** Each Obc variable corresponds to a plain local C variable. *)
  | Wvar v ->
    let n = name v in
    let n_lhs =
      if IdentSet.mem v out_env & not (is_gpu gpu)
      then Cfield (Cderef (Cvar "out"), local_qn n)
      else Cvar n
    in

    if Cenv.mem n var_env then
      let ty = Cenv.ty n var_env in
      (match ty with
      | Cty_ptr _ -> Cderef n_lhs
      | _ -> n_lhs)
    else
      n_lhs
  (** Dereference our [self] struct holding the node's memory. *)
  | Wmem v -> Cfield (Cderef (Cvar "self"), local_qn (name v))
  (** Field access. /!\ Indexed Obj expression should be a valid lhs!  *)
  | Wfield (l, fn) -> Cfield(cexpr_of_ext_value gpu out_env var_env l, fn)
  | Warray (l, idx) ->
    Carray(cexpr_of_ext_value gpu out_env var_env l,
           cexpr_of_exp gpu out_env var_env idx)

let rec assoc_obj instance obj_env =
  match obj_env with
    | [] -> raise Not_found
    | od :: t ->
        if od.o_ident = instance
        then od
        else assoc_obj instance t

let assoc_cn instance obj_env =
  (assoc_obj (obj_ref_name instance) obj_env).o_class

let is_op = function
  | { qual = Pervasives; name = _ } -> true
  | _ -> false

let out_var_name_of_objn o =
   o ^"_out_st"

(** Creates the transfer between memory locations for inputs when calling functions.
    Automatically desallocates the GPU memories created.
    @return : list of new variables
              list of allocations
              list of desallocations
              list of arguments to call the function *)
let generate_copies_in gpu parallel sig_info vars var_env =
  let inputs = sig_info.node_inputs in
  let rec gen inputs vars =
    (* An auxiliary function *)
    let aux inputs vars a var ty mem =
			let decls, affects, desalocs, vars = gen inputs vars in
	    let priv_to_glob = a.a_mem = Global & mem != Global in
	    let glob_to_priv = mem = Global & a.a_mem != Global in
      (* First case : memory on the CPU and expects GPU memory *)
	    if is_cpu gpu & priv_to_glob then
	      let new_s = fresh "cast" in
	      (new_s, (ty, Global)) :: decls,
	      generate_mem_write (CLvar new_s) var ty :: affects,
	      generate_mem_release (Cvar new_s) :: desalocs,
	      Cvar new_s :: vars
      (* Second case : memory on the GPU and expects CPU memory *)
	    else if is_cpu gpu & glob_to_priv then
	      let new_s = fresh "cast" in
	      (new_s, (ty, Private)) :: decls,
	      (generate_mem_read (Cvar new_s) var ty) :: affects,
	      desalocs,
	      (Cvar new_s) :: vars
      (* On the GPU, only arrays are treated. *)
	    else if is_gpu gpu & (mem != a.a_mem) then
	        if a.a_mem = Global then
	          Error.message no_location Error.Eillegal_cast
	        else
			      (match a.a_type with
			        | Tarray _ ->
				          let new_s = fresh "cast" in
				          (new_s, (ty, a.a_mem)) :: decls,
                  (create_affect_stm
                    gpu var_env parallel (CLvar new_s) var ty a.a_mem mem) @ affects,
                  desalocs,
                  (Cvar new_s) :: vars
			        | _ -> decls, affects, desalocs, var :: vars)
	      else
		      decls, affects, desalocs, var :: vars
    in
    (* Try to find the cast between memories *)
    match inputs, vars with
	    | [], [] -> [], [], [], []
		  | a :: inputs, var :: vars ->
		      let (ty, mem) = assoc_env_cexpr gpu var var_env in
          aux inputs vars a var ty mem
		  | _ -> assert false
  in
  gen inputs vars

(** Creates the transfers between memory locations for outputs when calling functions on the GPU.
    @return : list of new variables
              list of allocations
              list of arguments to call the function *)
let generate_copies_out gpu parallel sig_info vars var_env =
  let outputs = sig_info.node_outputs in
  let rec gen outputs vars =
    (* An auxiliary function *)
    let aux outputs vars a var ty mem =
			let decls, affects, vars = gen outputs vars in
      (* if the memory locations are different, must create a *)
      (* temporary variable to stock the result *)
	    if mem != a.a_mem then
        if a.a_mem = Global then
          Error.message no_location Error.Eillegal_cast
	      else
          let new_s = fresh "cast_out" in
          (new_s, (ty, a.a_mem)) :: decls,
	        (create_affect_stm
	          gpu var_env parallel var (Cvar new_s) ty mem a.a_mem) @ affects,
          ref_of_var (Cvar new_s) ty :: vars
      else
	      decls, affects, ref_of_var (cexpr_of_lhs var) ty :: vars
    in
    (* Try to find the cast between memories *)
    match outputs, vars with
	    | [], [] -> [], [], []
		  | a :: outputs, var :: vars ->
		      let (ty, mem) = assoc_env_lhs gpu var var_env in
          aux outputs vars a var ty mem
		  | _ -> assert false
  in
  gen outputs vars

(** Creates the list of arguments to call [objn], transfering memory if needed.
    [args] are the arguments, [out] where to stock the results. *)
let step_fun_call nc gpu out_env var_env classn sig_info objn out args =
  let gpu_env = if is_cpu gpu then [Cvar environment] else [] in
  if sig_info.node_stateful then (
    let sig_nc = sig_info.node_gpu = No_constraint in
    let mem, decl, affect_in, affect_out =
      (* In the case we are calling a parallel function from a clone mode,*)
      (* persistent memory must be transfered *)
      if is_gpu gpu & not nc & sig_nc then
        let mem_loc = Private in
        let ty = Cty_id (qn_append classn "_mem") in
	      (match objn with
	        | Oobj o ->
              let new_s = fresh "cast_env" in
              Cvar new_s,
              [(new_s, (ty, mem_loc))],
              [Caffect (CLvar new_s, Cfield (Cderef (Cvar "self"), local_qn (name o)))],
              [Caffect (CLfield (CLderef (CLvar "self"), local_qn (name o)), Cvar new_s)]
	        | Oarray (o, l) ->
	            let f = CLfield (CLderef (CLvar "self"), local_qn (name o)) in
	            let rec mk_idx pl = match pl with
	             | [] -> f
	             | p::pl -> CLarray (mk_idx pl, cexpr_of_pattern gpu out_env var_env p)
	            in
	            let obj_lhs = mk_idx l in
              let obj_exp = cexpr_of_lhs obj_lhs in
              let new_s = fresh "cast_env" in
              Cvar new_s,
              [(new_s, (ty, mem_loc))],
              [Caffect (CLvar new_s, obj_exp)],
              [Caffect (obj_lhs, Cvar new_s)]
	      )
      else
        (match objn with
	         | Oobj o -> Cfield (Cderef (Cvar "self"), local_qn (name o)), [], [], []
	         | Oarray (o, l) ->
	             let f = Cfield (Cderef (Cvar "self"), local_qn (name o)) in
	             let rec mk_idx pl = match pl with
	              | [] -> f
	              | p::pl -> Carray (mk_idx pl, cexpr_of_pattern gpu out_env var_env p)
	             in
	               mk_idx l, [], [], []
	      )
      in
      args@ out @ [Caddrof mem] @ gpu_env, decl, affect_in, affect_out
  ) else
    args@ out @ gpu_env, [], [], []

(** Generate the statement to call [objn].
    [outvl] is a list of lhs where to put the results.
    [args] is the list of expressions to use as arguments.*)
let generate_function_call nc gpu parallel out_env var_env obj_env outvl objn args =
  (** Class name for the object to step. *)
  let classln = assoc_cn objn obj_env in
  let classn = cname_of_qn classln in
  let sig_info = find_value classln in

  let decls_in, affects_in, desalocs_in, args =
    generate_copies_in gpu parallel sig_info args var_env in

  (* The calling convention is different between the GPU and the CPU *)
  if is_gpu gpu then
	  let decls_out, affects_out, out =
	    generate_copies_out gpu parallel sig_info outvl var_env in

	  let args, decl_obj, obj_in, obj_out =
      step_fun_call nc gpu out_env var_env classln sig_info objn out args in

	  let fun_call =
	    if is_op classln then
	      cop_of_op_aux classln args
	    else
	      (** The step function takes scalar arguments and its own internal memory
	          holding structure. *)
	      (** Our C expression for the function call. *)
	      Cfun_call (classn ^ "_step", args)
	  in
	  match outvl with
	    | [outv] when is_op classln ->
	        (* we assume that no right-hand side variable is global in this case *)
	        let (ty, mem) = assoc_env_lhs gpu outv var_env in
	        create_affect_stm gpu var_env parallel outv fun_call ty mem Private
	    | _ -> [Csblock { var_decls = decls_in @ decl_obj @ decls_out;
	                      block_body = affects_in @ obj_in @ [Csexpr fun_call] @
	                        affects_out @ obj_out @ desalocs_in;}]

  else
    let out = Cvar (out_var_name_of_objn classn) in

	  let fun_call =
	    if is_op classln then
	      cop_of_op_aux classln args
	    else
        let out = [Caddrof out] in
	      (** The step function takes scalar arguments and its own internal memory
	          holding structure. *)
	      let args, _, _, _ =
          step_fun_call nc gpu out_env var_env classln sig_info objn out args in
	      (** Our C expression for the function call. *)
	      Cfun_call (classn ^ "_step", args)
	  in

  (** Act according to the length of our list. Step functions with
      multiple return values will return a structure, and we care of
      assigning each field to the corresponding local variable. *)
  match outvl with
    | [] -> [Csblock { var_decls = decls_in;
                       block_body = affects_in @ (Csexpr fun_call :: desalocs_in);}]
    | [outv] when is_op classln ->
        (* we assume that no right-hand side variable is global in this case *)
        let (ty, mem) = assoc_env_lhs gpu outv var_env in
        create_affect_stm gpu var_env parallel outv fun_call ty mem Private
    | _ ->
        (* Remove options *)
        let out_sig = names_mem_of_arg_list sig_info.node_outputs in
        let create_affect outv (out_name, out_mem) =
          let (ty, mem) = assoc_env_lhs gpu outv var_env in
	        create_affect_stm
	          gpu var_env parallel outv (Cfield (out, local_qn out_name)) ty mem out_mem
        in
          Csblock { var_decls = decls_in;
                    block_body = affects_in @ (Csexpr fun_call :: desalocs_in);} ::
          (List.flatten (map2 create_affect outvl out_sig))

(** Create the statement dest = c where c = v^n^m... *)
let rec create_affect_const gpu parallel var_env (dest : clhs) c =
  match c.se_desc with
    | Svar ln ->
        let se = Static.simplify QualEnv.empty (find_const ln).c_value in
        create_affect_const gpu parallel var_env dest se
    | Sarray_power(c, n_list) ->
        let rec make_loop power_list replace = match power_list with
          | [] -> dest, replace
          | p :: power_list ->
            let x = gen_symbol () in
            let e, replace =
              make_loop power_list
                    (fun y -> [Cfor(x, mk_int 0,
                              cexpr_of_static_exp p, mk_int 1, replace y)]) in
            let e =  (CLarray (e, Cvar x)) in
            e, replace
        in
        let e, b =
          (* In case we are in a clone mode on the GPU, parallelizes the inner loop created. *)
	        if is_gpu gpu & is_clone parallel then
	          match n_list with
	            | p :: power_list ->
	              let p = cexpr_of_static_exp p in
	              (match p with
	                | Cconst (Ccint vi) when vi = !size_workgroup ->
					            let e, replace =
					              make_loop power_list (fun y -> y) in
					            let e = CLarray (e, Cfun_call("get_local_id", [mk_int 0])) in
					            e, replace
	                | Cconst (Ccint vi) when vi < !size_workgroup ->
					            let e, replace =
					              make_loop power_list
	                        (fun y ->
	                          [Cif (Cbop("<", Cfun_call("get_local_id", [mk_int 0]), p), y, [])]) in
					            let e = CLarray (e, Cfun_call("get_local_id", [mk_int 0])) in
					            e, replace
	                | _ ->
					            let x = gen_symbol () in
					            let e, replace =
					              make_loop power_list
					                    (fun y ->
                                [Cfor(x, Cfun_call("get_local_id", [mk_int 0]),
                                  p, mk_int !size_workgroup, y)]) in
					            let e = CLarray (e, Cvar x) in
					            e, replace)
              | _ -> assert false
	        else
		        make_loop n_list (fun y -> y)
        in
        let affect = b (create_affect_const gpu parallel var_env e c) in
        if is_gpu gpu & is_clone parallel then
          affect @ [create_barrier]
        else
          affect
    | Sarray cl ->
        let create_affect_idx c (i, affl) =
          let dest = CLarray (dest, Cconst (Ccint i)) in
            (i - 1, create_affect_const gpu parallel var_env dest c @ affl)
        in
          snd (List.fold_right create_affect_idx cl (List.length cl - 1, []))
    | Srecord f_se_list ->
        let affect_field affl (f, se) =
          let dest_f = CLfield (dest, f) in
            (create_affect_const gpu parallel var_env dest_f se) @ affl
        in
          List.fold_left affect_field [] f_se_list
    | _ -> [Caffect (dest, cexpr_of_static_exp c)]

(** Translates an Obj action to a list of C statements.

    @param  ?init     true when creating the initialization of persistent memory
            nc        true when translating a No_constraint function
            gpu       the Types.gpu of a function (does not accept No_constraint)
            parallel  an instance of type parallelisation
            out_env   an IdentSet containing all the output variables
            var_env   a Cenv mapping the variables defined to their type and memory location
            obj_env   a list of Obc obj_dec
            act       the Obc action to translate

    @return A list of cstm *)
let rec cstm_of_act ?(init = false) nc gpu parallel out_env var_env obj_env act =
  match act with
      (** Cosmetic : cases on boolean values are converted to if statements. *)
    | Acase (c, [({name = "true"}, te); ({ name = "false" }, fe)])
    | Acase (c, [({name = "false"}, fe); ({ name = "true"}, te)]) ->
        let cc = cexpr_of_exp gpu out_env var_env c in
        let cte = cstm_of_act_list ~init:init nc gpu parallel out_env var_env obj_env te in
        let cfe = cstm_of_act_list ~init:init nc gpu parallel out_env var_env obj_env fe in
        [Cif (cc, cte, cfe)]
    | Acase (c, [({name = "true"}, te)]) ->
        let cc = cexpr_of_exp gpu out_env var_env c in
        let cte = cstm_of_act_list ~init:init nc gpu parallel out_env var_env obj_env te in
        let cfe = [] in
        [Cif (cc, cte, cfe)]
    | Acase (c, [({name = "false"}, fe)]) ->
        let cc = Cuop ("!", (cexpr_of_exp gpu out_env var_env c)) in
        let cte = cstm_of_act_list ~init:init nc gpu parallel out_env var_env obj_env fe in
        let cfe = [] in
        [Cif (cc, cte, cfe)]


    (** Translation of case into a C switch statement is simple enough: we
        just recursively translate obj expressions and statements to
        corresponding C constructs, and cautiously "shortnamize"
        constructor names. *)
    | Acase (e, cl) ->
        (** [ccl_of_obccl] translates an Obc clause to a C clause. *)
        let ccl =
          List.map
            (fun (c,act) -> cname_of_qn c,
               cstm_of_act_list ~init:init nc gpu parallel out_env var_env obj_env act) cl in
        [Cswitch (cexpr_of_exp gpu out_env var_env e, ccl)]

    | Ablock b ->
        cstm_of_act_list ~init:init nc gpu parallel out_env var_env obj_env b

    (** Creates a loop and recursively applies the translation function on sub-statements.
        Parallelizes the work between work-groups when in a kernel. *)
    | Afor ({ v_ident = x } as vd, i1, i2, act) ->
        let s, (t, m) = cvar_of_vd vd in
        let var_env = Cenv.add s (t, m) var_env in
        (match parallel with
          | WG (size :: size_l) ->
              (* This mean we have to parallelize *)
              let div_size = List.fold_left ( * ) 1 size_l in
              let mod_size = div_size * size in
              let next_par = if size_l = [] then WI else WG size_l in
			        [Csblock {
		            var_decls = [name x, (Cty_int, Private)];
		            block_body =
		              Caffect (
				            CLvar (name x),
				            Cbop ("+", cexpr_of_exp gpu out_env var_env i1,
                          Cbop("/",
					                     Cbop("%", Cfun_call ("get_group_id",[Cconst (Ccint 0)]),
	                               mk_int mod_size),
                               mk_int div_size))) ::
				          cstm_of_act_list ~init:init nc gpu next_par out_env var_env obj_env act;}]
          | _ ->
              (* Normal case *)
			        [Cfor(name x, cexpr_of_exp gpu out_env var_env i1,
			              cexpr_of_exp gpu out_env var_env i2, mk_int 1,
			              cstm_of_act_list ~init:init nc gpu parallel out_env var_env obj_env act)])
    
    (** Creates a parallel loop and recursively applies
        the translation function on sub-statements. *)
    | Apfor ({ v_ident = x } as vd, i, act) ->
        let s, (t, m) = cvar_of_vd vd in
        let var_env = Cenv.add s (t, m) var_env in
        (match parallel with
          | WG (size :: size_l) ->
              (* In a kernel, parallelizes between all work-items of all work-groups *)
              let div_size = List.fold_left (fun x y -> x*y) 1 size_l in
              let mod_size = div_size * size in
              let next_par = if size_l = [] then Parallel else WG size_l in
			        [Csblock {
		            var_decls = [name x, (Cty_int, Private)];
		            block_body = [
			            Caffect (
				            CLvar (name x),
	                  Cbop(
	                    "/",
				                Cbop(
	                      "%",
	                      Cfun_call ("get_global_id", [Cconst (Ccint 0)]),
	                        mk_int mod_size),
	                    mk_int div_size));
                  (* Must check if the current work-item has to work. *)
                  (* This prohibits barriers when not in a clone mode. *)
				          Cif (
				            Cbop (
				              "<",
				              Cvar (name x),
				              cexpr_of_exp gpu out_env var_env i),
				            cstm_of_act_list ~init:init nc gpu next_par out_env var_env obj_env act,
				            [])];}]
          | _ ->
              (* Outside a kernel, parallelizes between the local work-items. *)
              let i = cexpr_of_exp gpu out_env var_env i in
              (match i with
                | Cconst (Ccint vi) when vi = !size_workgroup ->
                    (* If the loop is the same size as the size of a work-group, *)
                    (* does not create the loop. *)
						        [Csblock {
					            var_decls = [name x, (Cty_int, Private)];
					            block_body =
                        Caffect ((CLvar (name x)), (Cfun_call ("get_local_id", [mk_int 0]))) ::
                        cstm_of_act_list ~init:init nc gpu Parallel
                          out_env var_env obj_env act @
                        [create_barrier];}]
                | Cconst (Ccint vi) when vi < !size_workgroup ->
						        [Csblock {
					            var_decls = [name x, (Cty_int, Private)];
					            block_body = [
                        Caffect ((CLvar (name x)), (Cfun_call ("get_local_id", [mk_int 0])));
                        Cif (Cbop("<", Cvar (name x), i),
                          cstm_of_act_list ~init:init nc gpu Parallel
                            out_env var_env obj_env act, []);
                        create_barrier];}]
                | _ ->
						        [Cfor(name x,
						          Cfun_call (
						            "get_local_id",
						            [Cconst (Ccint 0)]),
						          i,
					            mk_int !size_workgroup,
						          cstm_of_act_list ~init:init nc gpu Parallel
                        out_env var_env obj_env act);
					          create_barrier]))

    (** Translate constant assignment *)
    | Aassgn (vn, { e_desc = Eextvalue { w_desc = Wconst c }; }) ->
        let vn = clhs_of_pattern gpu out_env var_env vn in
        let (ty, mem) = assoc_env_lhs gpu vn var_env in
        (* If writes to the GPU, creates a temporary variable to be able to copy the constant. *)
        if is_cpu gpu & mem = Global then
          let new_v = fresh "v" in
          let v = new_v, (ty, Private) in
          let var_env = Cenv.add new_v (ty, Private) var_env in
          let affect = create_affect_const gpu parallel var_env (CLvar new_v) c in
          let copy =
            create_affect_stm gpu var_env (is_clone parallel) vn (Cvar new_v) ty mem Private in
          [Csblock {
            var_decls = [v];
            block_body = affect @ copy;}]
        else
          create_affect_const gpu parallel var_env vn c

    (** Purely syntactic translation from an Obc local variable to a C
        local one, with recursive translation of the rhs expression. *)
    | Aassgn (vn, ({ e_desc = Eextvalue ({ w_desc = Wvar _ } as ext); } as e))
    | Aassgn (vn, ({ e_desc = Eextvalue ({ w_desc = Wmem _ } as ext); } as e))
    | Aassgn (vn, ({ e_desc = Eextvalue ({ w_desc = Warray _ } as ext); } as e)) ->
        let vn = clhs_of_pattern gpu out_env var_env vn in
        let (ty, mem) = assoc_env_lhs gpu vn var_env in
        let v = name_of_ext_value ext in
        let mem_v = Cenv.loc v var_env in
        let ce = cexpr_of_exp gpu out_env var_env e in
        create_affect_stm gpu var_env (is_clone parallel) vn ce ty mem mem_v
        
    | Aassgn (vn, e) ->
        let vn = clhs_of_pattern gpu out_env var_env vn in
        let (ty, mem) = assoc_env_lhs gpu vn var_env in
        let ce = cexpr_of_exp gpu out_env var_env e in
        create_affect_stm gpu var_env (is_clone parallel) vn ce ty mem Private

    (** Our Aop marks an operator invocation that will perform side effects. Just
        translate to a simple C statement. *)
    | Aop (op_name, args) ->
        [Csexpr (cop_of_op gpu out_env var_env op_name args)]

    (** Reinitialization of an object variable, extracting the reset
        function's name from our environment [obj_env]. *)
    | Acall (name_list, o, Mreset, args) ->
        assert_empty name_list;
        assert_empty args;
        let on = obj_ref_name o in
        let obj = assoc_obj on obj_env in
        let classn = cname_of_qn obj.o_class in
			  let sig_info = find_value obj.o_class in
        let sig_nc = sig_info.node_gpu = No_constraint in
        let gpu_env = if is_cpu gpu then [Cvar environment] else [] in
        let field = (CLfield (CLderef (CLvar "self"), local_qn (name on))) in
        let name_reset = if init then classn ^ "_init" else classn ^ "_reset" in
        (match o with
          | Oobj _ ->
              (* If reseting the memory of a No_constraint function from another type *)
              (* of function on the GPU, must transfer the memory *)
              if is_gpu gpu & not nc & sig_nc then
                let mem_loc = Private in
	              let ty = Cty_id (qn_append obj.o_class "_mem") in
					      let new_s = fresh "cast_self" in
					      let var = (new_s, (ty, mem_loc)) in
	              let field_expr = cexpr_of_lhs field in
	              let affect_in = Caffect (CLvar new_s, field_expr) in
	              let affect_out = Caffect (field, Cvar new_s) in
	              [Csblock { 
	                var_decls = [var];
	                block_body = affect_in ::
	                  Csexpr (Cfun_call (classn ^ "_reset", [Caddrof (Cvar new_s)] )) ::
	                  affect_out :: [];}]
              (* Normal case *)
              else
                let field = cexpr_of_lhs field in
                [Csexpr (Cfun_call (name_reset, Caddrof field :: gpu_env))]
          | Oarray (_, pl) ->
              let rec mk_loop pl field = match pl with 
                | [] ->
              (* If reseting the memory of a No_constraint function from another type *)
              (* of function on the GPU, must transfer the memory *)
                  if is_gpu gpu & not nc & sig_nc then
                    let mem_loc = Private in
                    let ty = Cty_id (qn_append obj.o_class "_mem") in
						        let new_s = fresh "cast_self" in
						        let var = (new_s, (ty, mem_loc)) in
                    let field_expr = cexpr_of_lhs field in
                    let affect_in = Caffect (CLvar new_s, field_expr) in
                    let affect_out = Caffect (field, Cvar new_s) in
                    [Csblock { 
                      var_decls = [var];
                      block_body = affect_in ::
                        Csexpr (Cfun_call (name_reset, [Caddrof (Cvar new_s)])) ::
                        affect_out :: [];}]
              (* Normal case *)
                  else
                    let field = cexpr_of_lhs field in
                    [Csexpr (Cfun_call (name_reset, Caddrof field :: gpu_env ))]
                | p::pl -> 
                  let field = CLarray(field, cexpr_of_pattern GPU out_env var_env p) in
                    mk_loop pl field
               in
                 mk_loop pl field
        )

    (** Step functions applications can return multiple values.
        On the CPU, we use a local structure to hold the results.
        On the GPU, we pass the adresses to store the results. *)
    | Acall (outvl, objn, Mstep, el) ->
        let args = cexprs_of_exps gpu out_env var_env el in
        let outvl = clhs_list_of_pattern_list gpu out_env var_env outvl in
        generate_function_call 
          nc gpu (is_clone parallel) out_env var_env obj_env outvl objn args


and cstm_of_act_list ?(init = false) nc gpu parallel out_env var_env obj_env b =
  let l = List.map cvar_of_vd b.b_locals in
  let var_env = add_env l var_env in
  let cstm = List.flatten 
    (List.map (cstm_of_act ~init:init nc gpu parallel out_env var_env obj_env) b.b_body) in
	match l with
	  | [] -> cstm
	  | _ -> 
        let rel = rel_of_varlist gpu l in
        [Csblock { var_decls = l; block_body = cstm @ rel }]


(** functions to generate the caller *)

(** Creates the needed buffers in a kernel caller, copying the inputs. *)
let generate_mem_in mem_env locals inputs outputs =
	let create_locals =
	  List.fold_right (fun x l ->
      let n = Cenv.find (name x.v_ident) mem_env in
      (generate_buffer (CLvar n) (ctype_of_otype x.v_type)) :: l)
	  (locals @ outputs) []
	in
	let create_mems =
	  List.fold_right (fun x l ->
      let n = Cenv.find (name x.v_ident) mem_env in
      let ty = ctype_of_otype x.v_type in
      if x.v_mem = Global then
        l
      else
        (generate_mem_write (CLvar n) (Cvar (name x.v_ident)) ty) :: l)
	  inputs create_locals
	in
	create_mems

(** Creates the expressions to set the arguments and to create the kernels.

    @return the list of expressions to set the arguments
            the list of expressions to create the kernels
            a Kers binding the number of the kernel in the function to its name
            a Kers binding the number of the kernel to its list of sizes
            the number of kernels to launch *)
let generate_arguments obj_env body mem_env =
  let code_of_arg ker_name (acc, i) arg =
    let name = match arg.a_name with
      | Some n -> n
      | None -> assert false
    in
    let gen_arg =
	    if Cenv.mem name mem_env then
		    generate_argument_kernel
		      (Cvar ker_name) (mk_int i) (Cref (Cvar (Cenv.find name mem_env))) :: acc
      else
        (* If the variable is not in the environment then it must be a memory *)
		    generate_argument_kernel
		      (Cvar ker_name) (mk_int i) (Cref (Cfield (Cderef (Cvar "self"), local_qn name))) :: acc
    in
    gen_arg, i + 1
  in
    
  let rec generate act_l (acc_args, acc_create, ker_names, ker_sizes, nbr_ker) = match act_l with
    | [] -> acc_args, acc_create, ker_names, ker_sizes, nbr_ker
    | (Acall (_, ref, _, _)) :: act_l ->
        let ker_name = fresh ("ker" ^ string_of_int(nbr_ker)) in
        let ker_names = Kers.add nbr_ker ker_name ker_names in
        let on = obj_ref_name ref in
        let obj = assoc_obj on obj_env in
	      let s = Modules.find_value obj.o_class in
        let sizes = match s.node_gpu with
          | Parallel_kernel (si, b) -> si, b
          | Kernel -> [1], false
          | _ -> assert false
        in
        let ker_sizes = Kers.add nbr_ker sizes ker_sizes in
        let l, i = List.fold_left (code_of_arg ker_name) ([], 0) (s.node_inputs) in
        let l, i = List.fold_left (code_of_arg ker_name) (l, i) (s.node_outputs) in
        let l =
          if s.node_stateful then
            generate_argument_kernel (Cvar ker_name) (mk_int i)
              (Cref (Cfield (Cderef (Cvar "self"), local_qn (name on)))) :: l
          else
            l
        in
        let acc_create =
          generate_kernel (CLvar ker_name) ((cname_of_qn obj.o_class) ^ "_step") :: acc_create
        in
        generate act_l (l @ acc_args, acc_create, ker_names, ker_sizes, nbr_ker + 1)
    | _ -> assert false
  in
  generate body.b_body ([], [], Kers.empty, Kers.empty, 0)

(** Creates a lot of verbose to call a kernel

    @param  ker_names  a Kers mapping the number of the kernel to its name
            ker_sizes  a Kers mapping a kernel to its list of sizes of parallelization
            nbr_ker    the number of kernels to launch

    @return the list of kernels as variables
            the list of kernel events as variables
            the list of kernel sizes as variables
            the list of expressions to affect the sizes
            the list of expressions to launch the kernels
            the list of releases *)
let generate_verbose ker_names ker_sizes nbr_ker =
  let rec create_stuff nbr = match nbr with
    | 0 -> [], [], ["workGroupSize", (Cty_arr (1, Cty_size_t), Private)],
          [Caffect (CLarray (CLvar "workGroupSize", Cconst (Ccint 0)),
            Cconst (Ccint !size_workgroup))],
          [], [], (Cconst Cnull, mk_int 0)

    | nbr ->
        let a, z, e, r, t, y, (ev_ptr, ev_nbr) = create_stuff (nbr - 1) in
        let ker_name = Kers.find (nbr - 1) ker_names in
        let (sizes, pmap) = Kers.find (nbr - 1) ker_sizes in
        let ker_event = fresh (ker_name ^ "_event") in
        let size = List.fold_left (fun s n -> s * n) 1 sizes in
        let size = if pmap then size + !size_workgroup -
          (size mod !size_workgroup) else size * !size_workgroup in
        let ker_size = fresh (ker_name ^ "_globalSize") in
	        (ker_name, (Oty_kernel, Private)) :: a,
	        (ker_event, (Oty_event, Private)) :: z,
	        (ker_size, (Cty_arr (1, Cty_size_t), Private)) :: e,
	        (Caffect (
	          CLarray (CLvar ker_size, Cconst (Ccint 0)), mk_int size)) :: r,
	        (Caffect (
	          OLenv_field Error,
	          Cfun_call (
	            "clEnqueueNDRangeKernel",
	            Oenv_field Command_queue :: Cvar ker_name ::
	            mk_int 1 :: Cconst Cnull :: Cvar ker_size ::
	            Cvar "workGroupSize" :: ev_nbr :: ev_ptr ::
	            Cref (Cvar ker_event) :: []))) :: t,
          (Csexpr (Cfun_call ("clReleaseKernel", [Cvar ker_name])) ::
          Csexpr (Cfun_call ("clReleaseEvent", [Cvar ker_event])) :: y),
          (Cref (Cvar ker_event), mk_int 1)
  in
	let a, z, e, r, t, y, _ = create_stuff nbr_ker in
	  List.rev a, List.rev z, List.rev e, List.rev r, List.rev t, List.rev y

(** Translates a list of objects into a list of variables and creates the releases *)
let cvar_of_objs gpu objs =
	let cvar_of_obj gpu obj (decls, rels) =
	let sig_info = find_value obj.o_class in
	  let name = out_var_name_of_objn (cname_of_qn obj.o_class) in
	  let decl = (Cty_id (qn_append obj.o_class "_out"), Private) in
		if Cenv.mem name decls then
		  decls, rels
		else if not (is_cpu gpu) then
		  Cenv.add name (Cty_id (qn_append obj.o_class "_out"), Private) decls, rels
		else
		  let out_sig = names_mem_of_arg_list sig_info.node_outputs in
		    let mem_release (s, m) l = match m with
		      | Global ->
		          let var = Cfield (Cvar name, local_qn s) in
		          generate_mem_release var :: l
		      | _ -> l
		    in
		    let rel = List.fold_right mem_release out_sig [] in
		    Cenv.add name decl decls, rel @ rels
	in
  let vars, rels =
    List.fold_right (cvar_of_obj gpu) 
	    (List.filter (fun obj -> not (is_op obj.o_class)) objs) (Cenv.empty, [])
	in
  Cenv.bindings vars, rels
	

(** {2 step() and reset() functions generation *)

(** Builds the argument list of step function*)
let step_fun_args n md gpu nc =
  let args = List.map (cvar_of_vd ~ptr:(is_kernel gpu)) md.m_inputs in
  let out_arg =
    if (is_gpu gpu) then
      List.map (cvar_of_vd ~ptr:(is_gpu gpu)) md.m_outputs
    else
      [("out", (Cty_ptr (Cty_id (qn_append n "_out")), Private))]
  in
  let context_arg =
    if is_stateful n then
      if is_gpu gpu & not nc then
        [("self", (Cty_ptr (Cty_id (qn_append n "_mem")), Global))]
      else
        [("self", (Cty_ptr (Cty_id (qn_append n "_mem")), Private))]
    else
      []
  in
  let device_arg =
    if is_gpu gpu then
      []
    else
      [(environment, (Cty_ptr (Cty_id (local_qn "opencl_environment")), Private))]
  in
    args @ out_arg @ context_arg @ device_arg


(** Returns a C function definition corresponding an Obc step function.

    @param  ?nc   true if the initial type of the function was No_constraint
            gpu   the Types.gpu of the function. No_constraint should be
                    translated to GPU or CPU before
            n     Obc class name
            mem   a list of Obc var_dec
            objs  a list of Obc obj_dec
            md    the method_def to translate, must correspond to a step function

    A step function can have multiple return values, whereas C does not allow such functions.
    On the CPU we declare a structure with a field by return value.
    On the GPU we give the adresses of the variables to affect. *)
let fun_def_of_step_fun ?(nc = false) gpu n mem objs md =
  
  (* All functions but kernel callers *)
  if (is_cpu gpu) || (is_gpu gpu) then
	  let fun_name = (cname_of_qn n) ^ "_step" in
	  (** Its arguments, translating Obc types to C types and adding our internal
	      memory structure. *)
	  let args = step_fun_args n md gpu nc in

	  (** Out vars for function calls *)
    let out_vars, out_rels =
      if is_cpu gpu then
        cvar_of_objs gpu objs
      else
        [], []
    in
	
	  (** The environments *)
	  let mems = List.map (cvar_of_vd ~ptr:(is_kernel gpu)) mem in
	  let mems = mems @ List.map (cvar_of_vd ~ptr:(is_gpu gpu)) md.m_outputs in
	  let var_env = add_env (args @ mems) Cenv.empty in
	  let var_env = add_env out_vars var_env in
	  let out_env =
	    List.fold_left
	      (fun out_env vd -> IdentSet.add vd.v_ident out_env)
	      IdentSet.empty
	      md.m_outputs
	  in

    (** The body *)
    let body =
      match gpu with
        | Parallel_kernel (s, _) ->
		        cstm_of_act_list nc gpu (WG s) out_env var_env objs md.m_body
        | _ when (is_gpu gpu) & (not nc) ->
		        cstm_of_act_list nc gpu WI out_env var_env objs md.m_body
        | _ ->
		        cstm_of_act_list nc gpu Parallel out_env var_env objs md.m_body
    in
    let body = body @ out_rels in

	  Cfundef {
	    f_name = fun_name;
	    f_retty = Cty_void;
	    f_args = args;
	    f_body = {
	      var_decls = out_vars;
	      block_body = body
	    };
      f_kernel = is_kernel gpu;
    }

  (* kernel_caller *)
  else
	  let fun_name = (cname_of_qn n) ^ "_step" in
	  let args = step_fun_args n md gpu nc in

    (* Creates the GPU variables and the environment from the inputs. *)
	  let (mems, mem_env) = List.fold_right (fun x (m, e) ->
        let name = name x.v_ident in
        if x.v_mem = Global then m, (Cenv.add name name e)
        else
		      let n = fresh ("cl_" ^ name) in
		      omem_of_vd n :: m, (Cenv.add name n e))
      md.m_inputs ([], Cenv.empty) in

    (* Creates the GPU variables and the environment from the outputs and local variables. *)
	  let (mems, mem_env) = List.fold_right (fun x (m, e) ->
        let name = name x.v_ident in
	      let n = fresh ("cl_" ^ name) in
	      omem_of_vd n :: m, (Cenv.add name n e))
      (md.m_body.b_locals @ md.m_outputs) (mems, mem_env) in

    (* Creates the memory releases for created buffers. *)
    let rel_mems = List.fold_right (fun x acc ->
        if x.v_mem = Global then
          acc
        else
          generate_mem_release (Cvar (Cenv.find (name x.v_ident) mem_env)) :: acc)
      (md.m_inputs @ md.m_outputs) [] in

    let rel_mems = List.fold_right (fun x acc -> 
        generate_mem_release (Cvar (Cenv.find (name x.v_ident) mem_env)) :: acc)
      md.m_body.b_locals rel_mems in

    (* Creates the expressions to create the buffers. *)
    let copy_in = generate_mem_in mem_env md.m_body.b_locals md.m_inputs md.m_outputs in
    (* Creates the expression to copy the memory from the CPU to the GPU. *)
    let copy_out =
		  List.fold_right
        (fun x acc ->
          let name = name x.v_ident in
          if x.v_mem = Global then
            Caffect (
              CLfield (CLderef (CLvar "out"), local_qn name),
              Cvar (Cenv.find name mem_env)) :: acc
          else
	          generate_mem_read
					    (Cfield (Cderef (Cvar "out"), local_qn name))
					    (Cvar (Cenv.find name mem_env)) (ctype_of_otype x.v_type) :: acc)
		    md.m_outputs [] in

    (* Creates the expressions to set the arguments and create the kernels. *)
    let set_args, create_kers, ker_names, ker_sizes, nbr_ker =
      generate_arguments objs md.m_body mem_env in

    (* Creates the kernels, sizes and calls *)
    let def_kers, def_events, def_sizes, sizes, calls, rels =
      generate_verbose ker_names ker_sizes nbr_ker in

    let var_decls = mems @ def_kers @ def_events @ def_sizes in

    let body = mk_block sizes :: mk_block create_kers :: mk_block copy_in ::
               mk_block set_args :: mk_wait_finish :: mk_block calls :: mk_wait_finish ::
               mk_block copy_out :: mk_block rel_mems :: mk_block rels :: [] in

	  Cfundef {
	    f_name = fun_name;
	    f_retty = Cty_void;
	    f_args = args;
	    f_body = {
	      var_decls = var_decls;
	      block_body = body
	    };
      f_kernel = false;
    }


(** [mem_decl_of_class_def cd] returns a declaration for a C structure holding
    internal variables and objects of the Obc class definition [cd]. *)
let mem_decl_of_class_def cd =
  (** This one just translates the class name to a struct name following the
      convention we described above. *)
  let struct_field_of_obj_dec l od =
    if is_stateful od.o_class then
      let ty = Cty_id (qn_append od.o_class "_mem") in
      let ty = match od.o_size with
        | Some nl -> 
	          let rec mk_idx nl = match nl with 
	            | [] -> ty
	            | n::nl -> Cty_arr (int_of_static_exp n, mk_idx nl)
	          in
	            mk_idx nl
        | None -> ty in
        if cd.cd_gpu = Kernel_caller then
          (name od.o_ident, (ty, Global))::l
        else
          (name od.o_ident, (ty, Private))::l
    else
      l
  in
    if is_stateful cd.cd_name then (
      (** Fields corresponding to normal memory variables. *)
      let mem_fields = List.map cvar_of_vd cd.cd_mems in
      (** Fields corresponding to object variables. *)
      let obj_fields = List.fold_left struct_field_of_obj_dec [] cd.cd_objs in
        [Cdecl_struct ((cname_of_qn cd.cd_name) ^ "_mem",
                       mem_fields @ obj_fields)]
    ) else
      []


let out_decl_of_class_def cd =
  (** Fields corresponding to output variables. *)
  let step_m = find_step_method cd in
  let out_fields = List.map cvar_of_vd step_m.m_outputs in
    [Cdecl_struct ((cname_of_qn cd.cd_name) ^ "_out", out_fields)]
  

(** [reset_fun_def_of_class_def cd] returns the defintion of the C function tasked to
    reset the class [cd]. [init] is true to create the function initializing the memory. *)
let reset_fun_def_of_class_def ?(init = false) ?(nc = false) gpu cd =
	let name_fun =
	  if init then
	    (cname_of_qn cd.cd_name) ^ "_init"
	  else
	    (cname_of_qn cd.cd_name) ^ "_reset"
	in
  let mem_loc =
    if is_gpu gpu & not nc then
      Global
    else
      Private
  in
  try
	  let var_env = List.map (cvar_of_vd ~ptr:(is_kernel gpu)) cd.cd_mems in
	  let reset = find_reset_method cd in
	  let rel = 
	    if init then
	      []
	    else
	      rel_of_memlist gpu var_env
	  in
	  let var_env = add_env var_env Cenv.empty in
	  let args =
	    if is_gpu gpu then
	      [("self", (Cty_ptr (Cty_id (qn_append cd.cd_name "_mem")), mem_loc))]
	    else
        ("self", (Cty_ptr (Cty_id (qn_append cd.cd_name "_mem")), mem_loc)) ::
	      (environment, (Cty_ptr (Cty_id (local_qn "opencl_environment")), Private)) :: []
	  in

	  if gpu != Kernel_caller then
		  let body =
	      match gpu with
	        | Parallel_kernel (s, _) ->
			        cstm_of_act_list ~init:init nc gpu (WG s) 
                IdentSet.empty var_env cd.cd_objs reset.m_body
	        | _ when (is_gpu gpu) & (not nc) ->
			        cstm_of_act_list ~init:init nc gpu WI 
                IdentSet.empty var_env cd.cd_objs reset.m_body
	        | _ ->
			        cstm_of_act_list ~init:init nc gpu Parallel 
                IdentSet.empty var_env cd.cd_objs reset.m_body
		  in
      let body = rel @ body in
		  Cfundef {
		    f_name = name_fun;
		    f_retty = Cty_void;
		    f_args = args;
		    f_body = {
		      var_decls = [];
		      block_body = body;
		    };
		    f_kernel = is_kernel gpu;
		  }

    (* To reset the memories of the functions running on the GPU, we must launch kernels. *)
	  else
      (* Removes all the function calls from the Obc act list and launches kernels instead. *)
	    (* We assume that no object is an array because of the split. *)
	    let rec clean body = match body with
	      | [] -> [], []
	      | Acall (_, o, Mreset, _) :: body ->
            let cstm, body = clean body in
		        let on = obj_ref_name o in
		        let obj = assoc_obj on cd.cd_objs in
		        let classn = cname_of_qn obj.o_class in
					  let sig_info = find_value obj.o_class in
            let sig_gpu = sig_info.node_gpu in
            let size =
              match sig_gpu with
                | Kernel -> Carraysize_t_lit [mk_int !size_workgroup]
                | Parallel_kernel (sizes, pmap) -> 
						        let size = List.fold_left (fun s n -> s * n) 1 sizes in
						        let size = if pmap then size + !size_workgroup -
                      (size mod !size_workgroup) else size * !size_workgroup in
                    Carraysize_t_lit [mk_int size]
                | _  -> assert false
            in  
	          let ker = fresh "ker_reset" in
            let field = Cfield (Cderef (Cvar "self"), local_qn (name on)) in
            (* All the expressions to launch the kernel. *)
            let bbody =
              generate_buffer (CLfield (CLderef (CLvar "self"), local_qn (name on)))
	              (Cty_id (local_qn (classn ^ "_mem"))) ::
              generate_kernel (CLvar ker) (classn ^ "_reset") ::
              generate_argument_kernel (Cvar ker) (mk_int 0) (Cref field) :: mk_wait_finish ::
							Caffect (OLenv_field Error,
							  Cfun_call ("clEnqueueNDRangeKernel",
							    Oenv_field Command_queue :: Cvar ker :: mk_int 1 :: Cconst Cnull :: 
			            size :: Carraysize_t_lit [mk_int !size_workgroup] ::
	                mk_int 0 :: Cconst Cnull :: Cref (Oenv_field Event) :: [])) ::
			        mk_wait_finish :: []
            in
            let bbody = if init then bbody else generate_mem_release field :: bbody in
	          (Csblock {
	            var_decls = [(ker, (Oty_kernel, Private))];
	            block_body = bbody }) :: cstm,
            body
	      | o :: body ->
            let cstm, body = clean body in
            cstm, o :: body
	    in
      let cstm, body = clean reset.m_body.b_body in

      (* Translates the remaining Obc actions. *)
	    let body = cstm_of_act_list ~init:init nc CPU Parallel
        IdentSet.empty var_env cd.cd_objs {reset.m_body with b_body = body} in
	    let body = rel @ cstm @ body in

		  Cfundef {
		    f_name = name_fun;
		    f_retty = Cty_void;
		    f_args = args;
		    f_body = {
		      var_decls = [];
		      block_body = body;
		    };
		    f_kernel = is_kernel gpu;
		  }

  with Not_found ->
	  Cfundef {
	    f_name = name_fun;
	    f_retty = Cty_void;
	    f_args = [];
	    f_body = {var_decls = []; block_body = []};
      f_kernel = false;
	  }

    


(** [cdecl_and_cfun_of_class_def cd] translates the class definition [cd] to
    both a C and an OpenCL program. *)
let cdefs_and_cdecls_of_class_def cd =
  (** We keep the state of our class in a structure, holding both internal
      variables and the state of other nodes. For a class named ["cname"], the
      structure will be called ["cname_mem"]. *)
  let step_m = find_step_method cd in
  let memory_struct_decl = mem_decl_of_class_def cd in
  let out_struct_decl = out_decl_of_class_def cd in

  (* In the case of a function both for CPU and GPU, we must create two different definitions *)
  if cd.cd_gpu = No_constraint then
	  let c_step_fun_def = fun_def_of_step_fun ~nc:true CPU cd.cd_name
	    cd.cd_mems cd.cd_objs step_m in
	  let cl_step_fun_def = fun_def_of_step_fun ~nc:true GPU cd.cd_name
	    cd.cd_mems cd.cd_objs step_m in
	  (* C function for resetting our memory structure. *)
	  let c_reset_fun_def = reset_fun_def_of_class_def ~nc:true CPU cd in
	  let cl_reset_fun_def = reset_fun_def_of_class_def ~nc:true GPU cd in
	  let c_res_fun_decl = cdecl_of_cfundef c_reset_fun_def in
	  let cl_res_fun_decl = cdecl_of_cfundef cl_reset_fun_def in
	  let c_init_fun_def = reset_fun_def_of_class_def ~init:true ~nc:true CPU cd in
	  let c_init_fun_decl = cdecl_of_cfundef c_init_fun_def in
	  let c_step_fun_decl = cdecl_of_cfundef c_step_fun_def in
	  let cl_step_fun_decl = cdecl_of_cfundef cl_step_fun_def in
	
	  (* change the declarations depending on the statefulness *)
	  let (c_decls, cl_decls, c_defs, cl_defs) = 
	    if is_stateful cd.cd_name then
	      ([c_init_fun_decl; c_res_fun_decl; c_step_fun_decl],
        [cl_res_fun_decl; cl_step_fun_decl],
        [c_init_fun_def; c_reset_fun_def; c_step_fun_def],
        [cl_reset_fun_def; cl_step_fun_def])
	    else
	      ([c_step_fun_decl], [cl_step_fun_decl], [c_step_fun_def], [cl_step_fun_def])
	  in
    let c_decls = memory_struct_decl @ out_struct_decl @ c_decls in
    let cl_decls = memory_struct_decl @ cl_decls in
    (c_decls, cl_decls), (c_defs, cl_defs)

  else
	  let step_fun_def = fun_def_of_step_fun cd.cd_gpu cd.cd_name
	    cd.cd_mems cd.cd_objs step_m in
	  (* C function for resetting our memory structure. *)
	  let reset_fun_def = reset_fun_def_of_class_def cd.cd_gpu cd in
	  let res_fun_decl = cdecl_of_cfundef reset_fun_def in
	  let step_fun_decl = cdecl_of_cfundef step_fun_def in
	
	  (* change the declarations depending on the statefulness *)
	  let (decls, defs) =
	    if is_stateful cd.cd_name & is_gpu cd.cd_gpu then
        (* For GPU functions, resetting and initializing a memory is the same. *)
	      ([res_fun_decl; step_fun_decl], [reset_fun_def; step_fun_def])
      else if is_stateful cd.cd_name then
			  let init_fun_def = reset_fun_def_of_class_def ~init:true cd.cd_gpu cd in
			  let init_fun_decl = cdecl_of_cfundef init_fun_def in
	      ([init_fun_decl; res_fun_decl; step_fun_decl], [init_fun_def; reset_fun_def; step_fun_def])
	    else
	      ([step_fun_decl], [step_fun_def])
	  in
	
	  if is_gpu cd.cd_gpu then
	    (memory_struct_decl, memory_struct_decl @ decls), ([], defs)
	  else
	    (memory_struct_decl @ out_struct_decl @ decls, []), (defs, [])


(** Translates an Obc type declaration to its C counterpart. *)
let cdefs_and_cdecls_of_type_decl otd =
  let name = cname_of_qn otd.t_name in
  match otd.t_desc with
    | Type_abs -> [], ([], []) (*assert false*)
    | Type_alias ty ->
      [], ([Cdecl_typedef (ctype_of_otype ty, name)], [])
    | Type_enum nl ->
        let of_string_fun = Cfundef
          { f_name = name ^ "_of_string";
            f_retty = Cty_id otd.t_name;
            f_args = [("s", (Cty_ptr Cty_char, Private))];
            f_body =
              { var_decls = [];
                block_body =
                  let gen_if t =
                    let t = cname_of_qn t in
                    let funcall = Cfun_call ("strcmp", [Cvar "s";
                                                        Cconst (Cstrlit t)]) in
                    let cond = Cbop ("==", funcall, Cconst (Ccint 0)) in
                    Cif (cond, [Creturn (Cconst (Ctag t))], []) in
                  map gen_if nl; };
            f_kernel = false;
          }
        and to_string_fun = Cfundef
          { f_name = "string_of_" ^ name;
            f_retty = Cty_ptr Cty_char;
            f_args = [("x", (Cty_id otd.t_name, Private)); ("buf", (Cty_ptr Cty_char, Private))];
            f_body =
              { var_decls = [];
                block_body =
                  let gen_clause t =
                    let t = cname_of_qn t in
                    let fun_call =
                      Cfun_call ("strcpy", [Cvar "buf";
                                            Cconst (Cstrlit t)]) in
                    (t, [Csexpr fun_call]) in
                  [Cswitch (Cvar "x", map gen_clause nl);
                   Creturn (Cvar "buf")]; };
            f_kernel = false;
          } in
        ([of_string_fun; to_string_fun],
         ([Cdecl_enum (name, List.map cname_of_qn nl)],
          [cdecl_of_cfundef of_string_fun;
          cdecl_of_cfundef to_string_fun]))
    | Type_struct fl ->
        let decls = List.map (fun f -> cname_of_qn f.Signature.f_name,
                                (ctype_of_otype f.Signature.f_type, Private)) fl in
        let decl = Cdecl_struct (name, decls) in
        ([], ([decl], []))

(** [cfile_list_of_oprog oprog] translates the Obc program [oprog] to a list of
    C source and header files. *)
let cfile_list_of_oprog_ty_decls name oprog =
  let types = Obc_utils.program_types oprog in
  let cdefs_and_cdecls = List.map cdefs_and_cdecls_of_type_decl types in

  let (cty_defs, cty_decls) = List.split cdefs_and_cdecls in
  let (cty_decls, cfun_decls) = List.split cty_decls in
  let cty_decls = List.concat cty_decls in
  let cfun_decls = List.concat cfun_decls in
  let filename_types = name ^ "_types" in
  let types_h = (filename_types ^ ".h",
                 Cheader (["stdbool"; "assert"; "pervasives"; "opencl_decade"],
                          cty_decls @ cfun_decls)) in
  let types_c = (filename_types ^ ".c", Csource (concat cty_defs)) in

  filename_types, [types_h; types_c], cty_decls

let sort_classes classes =
  let rec aux classes = match classes with
    | c :: classes when is_kernel c.cd_gpu -> (aux classes) @ [c]
    | _ -> classes
  in aux classes

let global_file_header name prog =
  let dependencies = ModulSet.elements (Obc_utils.Deps.deps_program prog) in
  let c_dependencies = List.map (fun m -> String.uncapitalize (modul_to_string m)) dependencies in
  let cl_dependencies = 
    List.map (fun m -> (String.uncapitalize (modul_to_string m)) ^ "_gpu") dependencies in

  let classes = program_classes prog in
  let classes = sort_classes classes in
  let (decls, defs) =
    List.split (List.map cdefs_and_cdecls_of_class_def classes) in
  let (c_decls, cl_decls) = List.split decls in
  let (c_defs, cl_defs) = List.split defs in
  let c_decls = List.concat c_decls
  and c_defs = List.concat c_defs in
  let cl_decls = List.concat cl_decls
  and cl_defs = List.concat cl_defs in

  let (ty_fname, ty_files, ty_decls) = cfile_list_of_oprog_ty_decls name prog in

  let c_header =
    (name ^ ".h", Cheader (ty_fname :: c_dependencies, c_decls))
  and c_source =
    (name ^ ".c", Csource c_defs) in
  let cl_header =
    (name ^ "_gpu.h", Oheader (cl_dependencies, ty_decls @ cl_decls))
  and cl_source =
    (name ^ "_gpu.cl", Osource cl_defs) in

  [c_header; c_source; cl_header; cl_source] @ ty_files
