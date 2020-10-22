module L = Location

type t [@@deriving eq, ord, sexp_of]

val equal_with_location : t -> t -> bool

val compare_with_location : t -> t -> int

val make : string -> L.position * L.position -> t

val of_ident : Ident.t -> t

val make_unloc : string -> t

val create_from_name_and_prefix : string -> t -> t

val content : t -> string

val pp : Format.formatter -> t -> unit

val positions : t -> L.position * L.position

module Set : Set.S with type elt = t

module Bag : CCMultiSet.S with type elt = t

module Map : Map.S with type key = t
