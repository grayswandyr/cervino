type position = Lexing.position =
  { pos_fname : string;
    pos_lnum : int;
    pos_bol : int;
    pos_cnum : int
  }
[@@deriving eq, ord]

let dummy = Lexing.dummy_pos

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

(* returns a column number, first column is at index 1 *)
let column { pos_cnum; pos_bol; _ } = pos_cnum - pos_bol + 1

(* in general, pos2 is the cloumn immediately after the culprit symbol so we remove 1*)
let get_file_line_chars pos1 pos2 =
  let file = pos1.pos_fname in
  let line = pos1.pos_lnum in
  let char1 = column pos1 in
  (* in general, pos2 is the column immediately after the culprit token so we decrement it *)
  let char2 = column pos2 - 1 in
  (file, line, char1, char2)


let positions_of_lexbuf lexbuf =
  let open Lexing in
  let pos1 = lexeme_start_p lexbuf in
  let pos2 = lexeme_end_p lexbuf in
  (pos1, pos2)


let excerpt fmt (pos1, pos2) =
  let file, line, col1, col2 = get_file_line_chars pos1 pos2 in
  assert (col2 >= col1);
  IO.with_in file
  @@ fun ic ->
  let lines = IO.read_lines_l ic in
  match List.get_at_idx (line - 1) lines with
  | None ->
      ()
  | Some l ->
      let blanks, carets =
        (String.repeat " " (col1 - 1), String.repeat "^" (col2 - col1 + 1))
      in
      Fmt.pf
        fmt
        "Line %d, %s:@\n| %s@\n| %s%s"
        line
        ( if col2 = col1
        then Printf.sprintf "character %d" col2
        else Printf.sprintf "characters %d-%d" col1 col2 )
        l
        blanks
        carets
