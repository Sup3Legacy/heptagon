 (**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(* Corrects the memories of the kernels : after mls2obc, the memories are *)
(* associated to the kernels but should be associated to the callers. *)


open Idents
open Names
open Gpu
open Obc
open Obc_utils
open Obc_mapfold

module M = struct
  type t = ident
  let compare = ident_compare
end

module Setid = Set.Make(M)

let rec add_env n l env = match l with
  | [] -> env
  | vd :: l -> add_env n l (QualEnv.add n vd env)

let rec split vdl s l1 l2 = match vdl with
  | [] -> l1, l2
  | vd :: vdl ->
      if (Setid.mem vd.v_ident s) then
        split vdl s (vd::l1) l2
      else
        split vdl s l1 (vd::l2)

let rec find_locals ml = match ml with
  | [] -> assert false
  | { m_name = Mstep; m_body = body } :: _ -> body.b_locals
  | _ :: ml -> find_locals ml

let rec find_reset ml = match ml with
  | [] -> assert false
  | { m_name = Mreset; m_body = body } :: _ -> body.b_body
  | _ :: ml -> find_reset ml

let rec modify_locals ml vars = match ml with
  | [] -> []
  | { m_name = Mstep; m_body = body } as m :: ml ->
      {m with m_body = {body with b_locals = vars}} :: ml
  | m :: ml -> m :: (modify_locals ml vars)

let rec modify_reset ml al = match ml with
  | [] -> []
  | { m_name = Mreset; m_body = body } as m :: ml ->
      {m with m_body = {body with b_body = al}} :: ml
  | m :: ml -> m :: (modify_reset ml al)

let rec clean_act_list al = match al with
  | [] -> [], []
  | a :: al ->
      let resets, calls = clean_act_list al in
      match a with
			  | Acall _ -> resets, a :: calls
			  | Aassgn _ -> a :: resets, calls
			  | Aop _ -> a :: resets, calls
			  | Afor (vd, e1, e2, b) ->
            let resb, callb = clean_block b in
            (match resb, callb with
              | None, _ -> resets, a :: calls
              | _, None -> a :: resets, calls
              | Some br, Some bc -> Afor(vd, e1, e2, br) :: resets, Afor(vd, e1, e2, bc) :: calls)
			  | Ablock b ->
            let resb, callb = clean_block b in
            (match resb, callb with
              | None, _ -> resets, a :: calls
              | _, None -> a :: resets, calls
              | Some br, Some bc -> Ablock br :: resets, Ablock bc :: calls)
			  (* parallel for *)
			  | Apfor (vd, e, b) ->
            let resb, callb = clean_block b in
            (match resb, callb with
              | None, _ -> resets, a :: calls
              | _, None -> a :: resets, calls
              | Some br, Some bc -> Apfor(vd, e, br) :: resets, Apfor(vd, e, bc) :: calls)
			  | Acase _ -> assert false

and clean_block b =
  let resets, calls = clean_act_list b.b_body in
  match resets, calls with
    | [], _ -> None, Some {b with b_body = calls}
    | _, [] -> Some {b with b_body = resets}, None
    | _, _ -> Some {b with b_body = resets}, Some {b with b_body = calls}

let lhsdesc funs ((env, gpu, l, s) as acc) ld = match ld, gpu with
  | Lmem x, (Kernel | Parallel_kernel _) -> Lvar x, (env, gpu, l, Setid.add x s)
  | Lvar x, Kernel_caller -> if List.mem x l then Lmem x, acc else ld, acc
  | _, _ -> Obc_mapfold.lhsdesc funs acc ld

let evdesc funs ((env, gpu, l, s) as acc) wd = match wd, gpu with
  | Wmem x, (Kernel | Parallel_kernel _) -> Wvar x, (env, gpu, l, Setid.add x s)
  | Wvar x, Kernel_caller -> if List.mem x l then Wmem x, acc else wd, acc
  | _, _ -> Obc_mapfold.evdesc funs acc wd

let class_def funs ((env, _, _, _) as acc) cd = match cd.cd_gpu with
  | Kernel
  | Parallel_kernel _ when cd.cd_stateful ->
      let cd, (env, gpu, l, s) = Obc_mapfold.class_def funs (env, cd.cd_gpu, [], Setid.empty) cd in
      let reset = find_reset cd.cd_methods in
      let reset, calls = clean_act_list reset in
      let cd = {cd with cd_methods = modify_reset cd.cd_methods calls } in
      let env = QualEnv.add cd.cd_name (s, reset) env in
      cd, (env, gpu, l, s)
  | Kernel_caller when cd.cd_stateful ->
      let vdl = find_locals cd.cd_methods in
      let rec aux fn mems vars resets = match fn with
        | [] -> mems, vars, resets
        | { o_class = n } :: fn ->
            let s, reset = QualEnv.find n env in
            let mem, vars = split vars s [] [] in
            aux fn (mem @ mems) vars (reset @ resets)
      in
      let mems, vars, resets = aux cd.cd_objs [] vdl [] in
      let mems = List.map (fun x -> { x with v_mem = Global }) mems in
      let methods = modify_locals cd.cd_methods vars in
      let methods = modify_reset methods ((find_reset methods) @ resets) in
      let cd = {cd with cd_methods = methods; cd_mems = mems } in
      Obc_mapfold.class_def
        funs (env, Kernel_caller, (List.map (fun x -> x.v_ident) mems), Setid.empty) cd
  | _ -> cd, acc

let funs =
  { defaults with
      lhsdesc = lhsdesc;
      evdesc = evdesc;
      class_def = class_def;
  }

let program p =
  let p, _ = Obc_mapfold.program_it funs (QualEnv.empty, No_constraint, [], Setid.empty) p in
  p