open Sexplib.Std
module L = Location

type t = string L.t [@@deriving eq, ord, sexp_of]

let equal_with_location = equal

let make s loc = L.make s loc

let create_from_name_and_prefix pref n =
  L.make (pref ^ L.content n) (n.startpos, n.endpos)
let pp fmt L.{ content; _ } = String.pp fmt content

let equal c1 c2 = L.equal_content String.equal c1 c2

let positions = L.positions
