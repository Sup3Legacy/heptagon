(**************************************************************************)
(*                                                                        *)
(*  Heptagon                                                              *)
(*                                                                        *)
(*  Author : Marc Pouzet                                                  *)
(*  Organization : Demons, LRI, University of Paris-Sud, Orsay            *)
(*                                                                        *)
(**************************************************************************)

(* Misc. functions *)
val optional : ('a -> 'b) -> 'a option -> 'b option
(** Optional with accumulator *)
val optional_wacc : ('a -> 'b -> 'c*'a) -> 'a -> 'b option -> ('c option * 'a)
val optunit : ('a -> unit) -> 'a option -> unit
val split_string : string -> char -> string list

(* Generation of unique names. Mandatory call of reset_symbol between
   set_min_symbol and gen_symbol *)
(*val set_min_symbol : int -> unit*)
val gen_symbol : unit -> string
val reset_symbol : unit -> unit

(** [unique l] returns the [l] list without duplicates. O([length l]). *)
val unique : 'a list -> 'a list

(** [incomplete_map f l] applies f to all the elements of
  l except the last element. *)
val incomplete_map : ('a -> 'a) -> 'a list -> 'a list

(** [last_element l] returns the last element of the list l.*)
val last_element : 'a list -> 'a

(** [split_last l] returns the list l without its last element
    and the last element of the list .*)
val split_last : 'a list -> ('a list * 'a)

(** [remove x l] removes all occurrences of x from list l.*)
val remove : 'a -> 'a list -> 'a list

(** [is_empty l] returns whether the list l is empty.*)
val is_empty : 'a list -> bool

(** [repeat_list v n] returns a list with n times the value v. *)
val repeat_list : 'a -> int -> 'a list

(** Same as List.mem_assoc but using the value instead of the key. *)
val memd_assoc : 'b -> ('a * 'b) list -> bool

(** Same as List.assoc but searching for a data and returning the key. *)
val assocd : 'b -> ('a * 'b) list -> 'a

(** [list_compare c l1 l2] compares the lists [l1] and [l2] according to
    lexicographical order induced by [c]. *)
val list_compare : ('a -> 'a -> int) -> 'a list -> 'a list -> int

val option_compare : ('a -> 'a -> int) -> 'a option -> 'a option -> int

(** Mapfold *)
val mapfold: ('a -> 'b -> 'c * 'a) -> 'a -> 'b list -> 'c list * 'a

(** Mapfold, right version. *)
val mapfold_right
  : ('a -> 'acc -> 'acc * 'b) -> 'a list -> 'acc -> 'acc * 'b list

(** Mapi *)
val mapi: (int -> 'a -> 'b) -> 'a list -> 'b list
val mapi2: (int -> 'a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
val mapi3: (int -> 'a -> 'b -> 'c -> 'd) ->
  'a list -> 'b list -> 'c list -> 'd list

(** Right fold for non-empty lists. fold_right_1 f [x] -> x. *)
val fold_right_1 : ('a -> 'a -> 'a) -> 'a list -> 'a

val gen : (int -> 'a -> 'a) -> 'a -> int -> 'a

val fold_righti : (int -> 'a -> 'b -> 'b) -> 'a list -> 'b -> 'b

(** Functions to decompose a list into a tuple *)
val assert_empty : 'a list -> unit
val assert_1 : 'a list -> 'a
val assert_1min : 'a list -> 'a * 'a list
val assert_2 : 'a list -> 'a * 'a
val assert_2min : 'a list -> 'a * 'a * 'a list
val assert_3 : 'a list -> 'a * 'a * 'a
