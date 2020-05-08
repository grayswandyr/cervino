open Containers
open Lexing

type t =
  { begp : Lexing.position
  ; endp : Lexing.position
  }

let from_positions (begp, endp) =
  assert (begp.pos_cnum <= endp.pos_cnum);
  { begp; endp }


let begl { begp; _ } = begp.pos_lnum

let begc { begp; _ } = begp.pos_cnum - begp.pos_bol

let endl { endp; _ } = endp.pos_lnum

let endc { endp; _ } = endp.pos_cnum - endp.pos_bol

let to_ints loc = ((begl loc, begc loc), (endl loc, endc loc))

let span (loc1, loc2) =
  let begp =
    if loc1.begp.pos_cnum < loc2.begp.pos_cnum then loc1.begp else loc2.begp
  in
  let endp =
    if loc1.endp.pos_cnum > loc2.endp.pos_cnum then loc1.endp else loc2.endp
  in
  from_positions (begp, endp)


let string_of_position p =
  let (l, c), (l2, c2) = to_ints p in
  Printf.sprintf "%d.%d-%d.%d" l c l2 c2


let dummy = { begp = Lexing.dummy_pos; endp = Lexing.dummy_pos }

type 'a located =
  { data : 'a
  ; loc : t
  }

let make_located data loc = { data; loc }

let pp pp out { data; _ } = pp out data
