let parse_lexbuf lexbuf =
  let open Parser in
  try parse Scanner.main lexbuf with
  | Error ->
      let pos = Location.positions_of_lexbuf lexbuf in
      Msg.err @@ fun m -> m "Syntax error.@\n%a" Location.excerpt pos


let parse_file file =
  IO.with_in file
  @@ fun ic ->
  let lexbuf = Lexing.from_channel ic in
  Lexing.set_filename lexbuf file;
  parse_lexbuf lexbuf


let parse_string s =
  let lexbuf = Lexing.from_string s in
  parse_lexbuf lexbuf
