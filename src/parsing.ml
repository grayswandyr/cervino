let parse_lexbuf lexbuf =
  let open Parser in
  try parse Scanner.main lexbuf with
  | Error ->
      let pos = Location.positions_of_lexbuf lexbuf in
      Msg.err
      @@ fun m ->
      m
        "%a syntax error:@\n%a"
        Location.pp_positions
        pos
        Location.pp_excerpt
        pos


let parse_file file =
  IO.with_in file
  @@ fun ic ->
  let lexbuf = Lexing.from_channel ic in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = file };
  parse_lexbuf lexbuf


let parse_string s =
  let lexbuf = Lexing.from_string s in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = "<string>" };
  parse_lexbuf lexbuf
