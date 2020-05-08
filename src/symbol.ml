open Containers
module H = Hashcons

type t = string H.hash_consed

module S = H.Make (struct
  type t = string

  let hash = String.hash

  let equal = String.equal
end)

(* ********************* *)
(* table for hashconsing *)
(* ********************* *)
let table = S.create 271

(* ********************* *)

let make s = S.hashcons table s

let hash sym = sym.H.hkey

let compare s1 s2 = s1.H.tag - s2.H.tag

let compare_string s1 s2 = String.compare s1.H.node s2.H.node

let equal x1 x2 = Stdlib.(x1 == x2)

let pp out at = Format.fprintf out "%s" at.H.node

let to_string x = Containers.Format.to_string pp x
