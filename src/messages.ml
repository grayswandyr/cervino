module C = Containers

let print msg =
  C.Format.(printf "%a@." (hovbox ~i:2 string) msg)


let eprint msg =
  C.Format.(eprintf "%a@." (hovbox ~i:2 string) msg)

let show s =
  print s

let info s =
  print ("[INFO] " ^ s)

let warning s =
  eprint ("[WARNING] " ^ s)

let fail s =
  eprint ("[ERROR] " ^ s);
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
  C.Format.sprintf "File %S, line %d, characters %d-%d:@\n" file line (char1 + 1) (char2 + 1)

let located_fail lexbuf msg =
  fail (positions lexbuf ^ msg)