module L = Location

type t [@@deriving eq, ord, sexp_of]

val equal_with_location : t -> t -> bool

val make : string -> L.position * L.position -> t

val pp : Format.formatter -> t -> unit

val positions : t -> L.position * L.position

val of_ident : Ident.t -> t
