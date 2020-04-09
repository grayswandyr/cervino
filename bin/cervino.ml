open Libcervino
open Containers


let parse_file file =
  let open Parser in 
  IO.with_in file @@ fun ic -> begin
    let lexbuf = Lexing.from_channel ic in
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = file};
    try 
      parse Scanner.main lexbuf
    with
    | Error -> Messages.located_fail lexbuf "Syntax error"
  end

let () = 
  let msg = 
    {|This is a proof of concept program: models are expected to be written in (a specific fragment of) valid Electrum.|} 
  in
  Messages.info msg;
  let model = parse_file Sys.argv.(1) in
  Cst.print Format.std_formatter model;
  match Wf.analyze_model model with
  | None -> Messages.info "Model is well-formed."
  | Some f -> 
    let faulty = Format.to_string Cst.print_foltl f in
    Messages.fail ("Model is not well-formed, an existential quantifier appears under an `always` connective:\n" ^ faulty)