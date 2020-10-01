open Sexplib.Std
module L = Location

type t = string L.t [@@deriving eq, ord, sexp_of]

let equal_with_location = equal

let make s loc = L.make s loc

let pp fmt L.{ content; _ } = String.pp fmt content

let equal L.{ content = c1; _ } L.{ content = c2; _ } = String.equal c1 c2
