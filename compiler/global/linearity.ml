open Format
open Names
open Misc

type linearity_var = name

type linearity =
  | Ltop
  | Lat of linearity_var
  | Lvar of linearity_var (*a linearity var, used in functions sig *)
  | Ltuple of linearity list

module LinearitySet = Set.Make(struct
  type t = linearity
  let compare = compare
end)

(** Returns a linearity object from a linearity list. *)
let prod = function
  | [l] -> l
  | l -> Ltuple l

let linearity_list_of_linearity = function
  | Ltuple l -> l
  | l -> [l]

let rec lin_skeleton lin = function
  | Types.Tprod l -> Ltuple (List.map (lin_skeleton lin) l)
  | _ -> lin

(** Same as Misc.split_last but on a linearity. *)
let split_last_lin = function
  | Ltuple l ->
      let l, acc = split_last l in
        Ltuple l, acc
  | l ->
      Ltuple [], l

let rec is_not_linear = function
  | Ltop -> true
  | Ltuple l -> List.for_all is_not_linear l
  | _ -> false

exception UnifyFailed

(** Unifies lin with expected_lin and returns the result
    of the unification. Applies subtyping and instantiate linearity vars. *)
let rec unify_lin expected_lin lin =
  match expected_lin,lin with
    | Ltop, Lat _ -> Ltop
    | Ltop, Lvar _ -> Ltop
    | Lat r1, Lat r2 when r1 = r2 -> Lat r1
    | Ltop, Ltop -> Ltop
    | Ltuple l1, Ltuple l2 -> Ltuple (List.map2 unify_lin l1 l2)
    | Lvar _, Lat r -> Lat r
    | Lat r, Lvar _ -> Lat r
    | _, _ -> raise UnifyFailed

let rec lin_to_string = function
  | Ltop -> "at T"
  | Lat r -> "at "^r
  | Lvar r -> "at _"^r
  | Ltuple l_list -> String.concat ", " (List.map lin_to_string l_list)

let print_linearity ff l =
  fprintf ff " %s" (lin_to_string l)

