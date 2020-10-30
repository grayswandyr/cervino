open Sexplib.Std
module L = Location

type t = string L.t [@@deriving eq, ord, sexp_of]

let content = L.content

let hash id = String.hash (content id)

let equal_with_location = equal

let compare_with_location = compare

let equal x y = String.equal (content x) (content y)

let compare x y = String.compare (content x) (content y)

let make s loc = L.make s loc

let make_unloc s = L.make s (Lexing.dummy_pos, Lexing.dummy_pos)

let create_from_name_and_prefix pref n =
  L.make (pref ^ L.content n) (n.startpos, n.endpos)


let pp fmt L.{ content; _ } = Fmt.string fmt content

let positions = L.positions

let of_ident (id : Ident.t) = make (Ident.content id) (Ident.positions id)

let fresh =
  let c = ref 0 in
  fun prefix ->
    assert (!c < max_int);
    let res = make_unloc @@ prefix ^ "_" ^ string_of_int !c in
    incr c;
    res


module Elt = struct
  type nonrec t = t

  let compare = compare
end

module Set = Set.Make (Elt)
module Bag = CCMultiSet.Make (Elt)
module Map = Map.Make (Elt)
