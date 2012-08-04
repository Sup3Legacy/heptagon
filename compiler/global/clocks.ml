(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

open Names
open Idents
open Signature


type ct =
  | Ck of ck
  | Cprod of ct list

and sampling_value = static_exp

and ck =
  | Cbase
  | Cvar of link ref
  | Con of ck * sampling_value * var_ident

and link =
  | Cindex of int
  | Clink of ck


let compare_sv se1 se2 = static_exp_compare se1 se2
let equal_sv se1 se2 = 0 = (compare_sv se1 se2)

exception Unify

let invalid_clock = Cprod []


let index = ref 0

let gen_index () = (incr index; !index)

(** returns a new clock variable *)
let fresh_clock () = Cvar { contents = Cindex (gen_index ()); }

(** returns a new clock type corresponding to the data type [ty] *)
let rec fresh_ct ty = match ty with
  | Tprod ty_list ->
      (match ty_list with
        | [] -> Ck (fresh_clock())
        | _ -> Cprod (List.map fresh_ct ty_list))
  | Tarray (t, _) -> fresh_ct t
  | Tid _ | Tinvalid -> Ck (fresh_clock())
  | Tfuture (_,t) -> fresh_ct t
  | Tbounded _ -> Ck (fresh_clock())


(** returns the canonic (short) representant of a [ck]
    and update it to this value. *)
let rec ck_repr ck = match ck with
  | Cbase | Con _
  | Cvar { contents = Cindex _ } -> ck
  | Cvar (({ contents = Clink ck } as link)) ->
      let ck = ck_repr ck in
      link.contents <- Clink ck;
      ck

let fail_to_unify () =
  if not !Compiler_options.no_clocking_error then raise Unify

(** verifies that index is fresh in ck. *)
let rec occur_check index ck =
  let ck = ck_repr ck in
  match ck with
    | Cbase -> ()
    | Cvar { contents = Cindex n } when index <> n -> ()
    | Con (ck, _, _) -> occur_check index ck
    | _ -> raise Unify


(** unify ck *)
and unify_ck ck1 ck2 =
  let ck1 = ck_repr ck1 in
  let ck2 = ck_repr ck2 in
  if ck1 == ck2 then ()
  else
    try match (ck1, ck2) with
     | Cbase, Cbase -> ()
     | Cvar { contents = Cindex n1 }, Cvar { contents = Cindex n2 } when n1 = n2 -> ()
     | Con (ck1, c1, n1), Con (ck2, c2, n2) when (equal_sv c1 c2) & (n1 = n2) ->
         unify_ck ck1 ck2
     | Cvar ({ contents = Cindex n } as v), ck
     | ck, Cvar ({ contents = Cindex n } as v) ->
         occur_check n ck;
         v.contents <- Clink ck
     | _ -> raise Unify
    with Unify ->
      fail_to_unify ()


(** unify ct *)
let rec unify t1 t2 =
  if t1 == t2 then () else
  try match (t1, t2) with
    | (Ck (Cbase | Cvar { contents = Cindex _; }), Cprod [])
    | (Cprod [], Ck (Cbase | Cvar { contents = Cindex _; })) -> ()
    | (Ck ck1, Ck ck2) -> unify_ck ck1 ck2
    | (Cprod t1_list, Cprod t2_list) -> unify_list t1_list t2_list
    | _ -> raise Unify
  with Unify ->
    fail_to_unify ()

and unify_list t1_list t2_list =
  try List.iter2 unify t1_list t2_list
  with _ -> fail_to_unify ()


let rec skeleton ck = function
  | Tprod ty_list ->
      (match ty_list with
        | [_] -> Ck ck
        | l -> Cprod (List.map (skeleton ck) l))
  | Tarray (t, _) | Tfuture (_, t) -> skeleton ck t
  | Tid _ | Tinvalid -> Ck ck
  | Tbounded _ -> Ck ck

let unprod ct =
  let rec f acc ct = match ct with
    | Ck ck -> ck::acc
    | Cprod ct_l -> List.fold_left f acc ct_l
  in
  f [] ct

let prod ck_l = match ck_l with
  | [ck] -> Ck ck
  | _ -> Cprod (List.map (fun ck -> Ck ck) ck_l)

let rec root_ck_of ck = match ck_repr ck with
  | Cbase
  | Cvar { contents = Cindex _ } -> ck
  | Con(ck,_,_) -> root_ck_of ck
  | Cvar { contents = Clink _ } -> Misc.internal_error "Clocks, wrong repr"


(** Given [ root = . on b] and [ck = . on b on d], returns ck on this new root : [. on d].
    @raise Not_a_root if [root] is not a root of [ck]. *)
exception Not_a_root
let rec reroot_ck root ck =
  try unify_ck root ck; Cbase
  with Unify ->
    begin match ck with
      | Con(ck, c,v) -> Con(reroot_ck root ck,c,v)
      | _ -> raise Not_a_root
    end


(** Find the biggest common root of the list of clocks [ck_l].
    Return this root and the clocks rerooted.*)
let common_root_ck_list ck_l =
  let rec find_root root = (* tries to reroot on [root], if it fails, reduce the root *)
    try (List.map (reroot_ck root) ck_l, root)
    with Not_a_root ->
      begin match root with
        | Con(ck,_,_) -> find_root ck
        | _ -> (ck_l, Cbase) (* if the root can't be reduced, common root is Cbase *)
      end
  in
  match ck_l with
    | [] -> [], Cbase
    | _ -> find_root (List.hd ck_l)


let rec last_clock ct = match ct with
  | Ck ck -> ck
  | Cprod l -> last_clock (Misc.last_element l)

(** returns whether [ck1] and [ck2] are leafs of the same clock node :
  E.g. .... on C1(x) and .... on C2(x) are. *)
let same_control ck1 ck2 = match ck_repr ck1, ck_repr ck2 with
  | Cbase, Cbase -> true
  | Con(_,_,x1), Con(_,_,x2) -> x1 = x2
  | Cvar {contents = Cindex i1}, Cvar {contents = Cindex i2} -> i1 = i2
  | _ -> false

(** returns the first clock of a ct. *)
let rec first_ck ct = match ct with
  | Ck ck -> ck
  | Cprod [] -> assert false
  | Cprod (ct::_) -> first_ck ct

(** Generate a signature clock from a clock *)
let rec ck_to_sck ck =
  let ck = ck_repr ck in
  match ck with
    | Cbase -> Signature.Cbase
    | Con (ck,c,x) -> Signature.Con(ck_to_sck ck, c, Idents.source_name x)
    | _ -> Misc.internal_error "Signature couldn't translate ck"

let are_disjoint ck1 ck2 =
  let rec list_of_samplers acc ck = match ck with
    | Cbase | Cvar _ -> acc
    | Con(ck, c, x) -> list_of_samplers ((c, x)::acc) ck
  in
  let rec disjoint_samplers s_ck1 s_ck2 = match s_ck1, s_ck2 with
    | [], _ -> false
    | _ , [] -> false
    | (c1, x1)::s_ck1, (c2, x2)::s_ck2 ->
        if Idents.ident_compare x1 x2 <> 0 then
          false
        else
          not (equal_sv c1 c2) || disjoint_samplers s_ck1 s_ck2
  in
  disjoint_samplers (list_of_samplers [] ck1) (list_of_samplers [] ck2)

(** Comparison functions *)
let rec clock_compare ck1 ck2 = match ck1, ck2 with
  | Cvar { contents = Clink ck1; }, _ -> clock_compare ck1 ck2
  | _, Cvar { contents = Clink ck2; } -> clock_compare ck1 ck2
  | Cbase, Cbase -> 0
  | Cvar lr1, Cvar lr2 -> link_compare !lr1 !lr2
  | Con (ck1, cn1, vi1), Con (ck2, cn2, vi2) ->
      let cr1 = static_exp_compare cn1 cn2 in
      if cr1 <> 0 then cr1 else
        let cr2 = ident_compare vi1 vi2 in
        if cr2 <> 0 then cr2 else clock_compare ck1 ck2
  | Cbase , _ -> 1

  | Cvar _, Cbase -> -1
  | Cvar _, _ -> 1

  | Con _, _ -> -1

and link_compare li1 li2 = match li1, li2 with
  | Cindex _, Cindex _ -> 0
  | Clink ck1, Clink ck2 -> clock_compare ck1 ck2
  | Cindex _, _ -> 1
  | Clink _, _ -> -1