open Libcervino
open Containers

module C = Containers

let parse_file file =
  let open Parser in 
  C.IO.with_in file @@ fun ic -> begin
    let lexbuf = Lexing.from_channel ic in
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = file};
    try 
      parse Scanner.main lexbuf
    with
    | Error -> Messages.located_fail lexbuf "Syntax error"
  end

let () = 
  let msg = 
    {|This is a proof of concept program. Fed models are expected to be written in a well-formed fragment of Electrum; furthermore, many necessary verifications are not performed.|} 
  in
  Messages.info msg;
  let model = parse_file Sys.argv.(1) in
  Cst.print Format.std_formatter model

