(** Symbols are hash-consed strings *)

type t

val make : string -> t

val compare : t -> t -> int

val compare_string : t -> t -> int

val hash : t -> int

val equal : t -> t -> bool

val to_string : t -> string

val pp : CCFormat.formatter -> t -> unit
