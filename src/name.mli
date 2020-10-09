module L = Location

type t [@@deriving eq, ord, sexp_of]

val equal_with_location : t -> t -> bool

val make : string -> L.position * L.position -> t

val create_from_name_and_prefix : string -> t -> t

val pp : Format.formatter -> String.t L.t -> unit

val positions : t -> L.position * L.position
