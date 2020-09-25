type 'a t =
  { content : 'a
  ; startpos : Lexing.position [@printer fun fmt _ -> Format.pp_print_string fmt "_"]
  ; endpos : Lexing.position [@printer fun fmt _ -> Format.pp_print_string fmt "_"]
  }
[@@deriving show { with_path = false }]

let make content (startpos, endpos) = { content; startpos; endpos }

(* inspired by http://gallium.inria.fr/~fpottier/X/INF564/html/error.ml.html *)
(* first column is at index 1, last column is the pointer in lexbuf *)
let get_file_line_chars lexbuf =
  let open Lexing in
  let pos1 = lexeme_start_p lexbuf in
  let pos2 = lexeme_end_p lexbuf in
  let file = pos1.pos_fname in
  let line = pos1.pos_lnum in
  let char1 = pos1.pos_cnum - pos1.pos_bol + 1 in
  let char2 = pos2.pos_cnum - pos1.pos_bol + 1 in
  (* intentionally [pos1.pos_bol] *)
  (file, line, char1, char2)


let pp_positions fmt lexbuf =
  let _, line, char1, char2 = get_file_line_chars lexbuf in
  Fmt.pf fmt "Line %d, characters %d-%d:" line char1 char2


let pp_excerpt fmt lexbuf =
  let file, line, idx1, idx2 = get_file_line_chars lexbuf in
  assert (idx2 >= idx1);
  IO.with_in file
  @@ fun ic ->
  let lines = IO.read_lines_l ic in
  match List.get_at_idx (line - 1) lines with
  | None ->
      assert false
  | Some l ->
      let blanks, carets =
        (String.repeat " " (idx1 - 1), String.repeat "^" (idx2 - idx1 + 1))
      in
      Fmt.pf fmt "| %s@\n| %s%s" l blanks carets
