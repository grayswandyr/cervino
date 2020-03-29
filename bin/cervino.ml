open Libcervino


module C = Containers

let parse_file file =
  let open Parser in 
  C.IO.with_in file @@ fun ic -> begin
    let lexbuf = Lexing.from_channel ic in
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = file};
    try 
      ignore @@ parse Scanner.main lexbuf
    with
    | Error -> Messages.located_error lexbuf "Syntax error"
  end

let () = 
  parse_file Sys.argv.(1)
