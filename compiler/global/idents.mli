
open Names

(** This modules manages unique identifiers,
  /!\ To be effective, [enter_node] has to be called when entering a node
  [gen_var] generates a variable identifier
  [name] returns a unique name (inside its node) from an identifier. *)

(** The (abstract) type of identifiers*)
type ident

(** Type to be used for local variables *)
type var_ident = ident

(** Comparison on idents with the same properties as [Pervasives.compare] *)
val ident_compare : ident -> ident -> int

(** Get the full name of an identifier (it is guaranteed to be unique) *)
val name : ident -> string

(** Get the source name of an identifier (useful when dealing with signatures *)
val source_name : ident -> string

(** [gen_fresh pass_name kind_to_string kind]
    generate a fresh ident with a sweet [name].
    It should be used to define a [fresh] function specific to a pass. *)
val gen_fresh : string -> ('a -> string) -> ?reset:bool -> 'a -> ident

(** [gen_var pass_name name]
    generates a fresh ident with a sweet [name] *)
val gen_var : string -> ?reset:bool -> string -> ident

(** [ident_of_name n] returns an fresh identifier corresponding
  to a _source_ variable (do not use it for generated variables). *)
val ident_of_name : ?reset:bool -> string -> ident

val is_reset : ident -> bool

(** /!\ [enter_node qualname] should be called every time we enter a node with name [qualname]. *)
val enter_node : Names.qualname -> unit

(** [clone_node f fc] allows to clone node [f] so that all idents used in [f] are also in [f'] *)
val clone_node : Names.qualname -> Names.qualname -> unit

(** [local_qn name] returns [name] as being local to the current node *)
val local_qn : Names.name -> Names.qualname

(** Maps taking an identifier as a key. *)
module Env :
sig
  include (Map.S with type key = ident)

  val append : 'a t -> 'a t -> 'a t
  val union : 'a t -> 'a t -> 'a t
  val diff : 'a t -> 'b t -> 'a t
  val partition : (key -> bool) -> 'a t -> 'a t * 'a t
  val print_t : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
end

(** A set of identifiers. *)
module IdentSet :
sig
  include (Set.S with type elt = ident)
  val print_t : Format.formatter -> t -> unit
end
