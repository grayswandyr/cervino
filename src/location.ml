type position = Lexing.position =
  { pos_fname : string;
    pos_lnum : int;
    pos_bol : int;
    pos_cnum : int
  }
[@@deriving eq, ord]

let dummy = { pos_fname = "<dummy>"; pos_lnum = 0; pos_bol = 0; pos_cnum = 0 }

type 'a t =
  { content : 'a;
    startpos : position;
    endpos : position
  }
[@@deriving eq, ord]

let sexp_of_t sexp_of_a { content; _ } = sexp_of_a content

let pp pp_content fmt { content; _ } = pp_content fmt content

let show pp_content { content; _ } = Format.sprintf "%a" pp_content content

let make content (startpos, endpos) = { content; startpos; endpos }

let content { content; _ } = content

let positions { startpos; endpos; _ } = (startpos, endpos)

let equal_content eq_c { content = c1; _ } { content = c2; _ } = eq_c c1 c2

(* inspired by http://gallium.inria.fr/~fpottier/X/INF564/html/error.ml.html *)
(* first column is at index 1, last column is the pointer in lexbuf *)
let get_file_line_chars pos1 pos2 =
  let file = pos1.pos_fname in
  let line = pos1.pos_lnum - 1 in
  let char1 = pos1.pos_cnum - pos1.pos_bol + 1 in
  let char2 = pos2.pos_cnum - pos1.pos_bol + 1 in
  (* intentionally [pos1.pos_bol] *)
  (file, line, char1, char2)


let positions_of_lexbuf lexbuf =
  let open Lexing in
  let pos1 = lexeme_start_p lexbuf in
  let pos2 = lexeme_end_p lexbuf in
  (pos1, pos2)


let pp_positions fmt (pos1, pos2) =
  let _, line, char1, char2 = get_file_line_chars pos1 pos2 in
  Fmt.pf fmt "Line %d, characters %d-%d:" line char1 char2


let pp_excerpt fmt (pos1, pos2) =
  let file, line, idx1, idx2 = get_file_line_chars pos1 pos2 in
  assert (idx2 >= idx1);
  IO.with_in file
  @@ fun ic ->
  let lines = IO.read_lines_l ic in
  match List.get_at_idx (line - 1) lines with
  | None ->
      Msg.err (fun m -> m "%s: internal error" __LOC__)
  | Some l ->
      let blanks, carets =
        (String.repeat " " (idx1 - 1), String.repeat "^" (idx2 - idx1 + 1))
      in
      Fmt.pf fmt "| %s@\n| %s%s" l blanks carets


let pp_location fmt pos = Fmt.pf fmt "%a@\n%a" pp_positions pos pp_excerpt pos
