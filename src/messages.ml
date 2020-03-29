module C = Containers

let fail s =
  prerr_endline s;
  exit 1


(* adapted from a file by François Pottier *)
let positions lexbuf =
  let open Lexing in
  let pos1 = lexeme_start_p lexbuf  in
  let pos2 = lexeme_end_p lexbuf in
  let file = pos1.pos_fname in
  let line = pos1.pos_lnum in
  let char1 = pos1.pos_cnum - pos1.pos_bol in
  let char2 = pos2.pos_cnum - pos1.pos_bol in (* intentionally [pos1.pos_bol] *)
  Printf.sprintf "File %S, line %d, characters %d-%d:\n" file line (char1 + 1) (char2 + 1)


let located_error lexbuf msg =
  fail (positions lexbuf ^ msg)