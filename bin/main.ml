open Libcervino
open Containers

module M = Messages

let parse_file file =
  let open Parser in 
  IO.with_in file @@ fun ic -> begin
    let lexbuf = Lexing.from_channel ic in
    lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = file};
    try 
      parse Scanner.main lexbuf
    with
    | Error -> M.located_fail lexbuf "Syntax error"
  end

let main file = 
  let msg = 
    "This program is a proof-of-concept: fed models are taken to be 
    valid Electrum." 
  in
  M.info msg;
  let model = parse_file file in
  M.info "Showing recognized model (reformatted):";
  M.show (Format.to_string Cst.print model);
  (match Wf.analyze_model model with
   | None -> M.info "Model is well-formed."
   | Some (Quant (q, _, _) as f) -> 
     let polarity = match q with
     | All -> "in negative position "
     | Some_ -> ""
     in
     let msg = 
     Format.(sprintf "`%a` appears %sunder an `always` connective:@\n%a" 
Cst.print_quant q
polarity
    Cst.print_foltl f)
    in
    M.fail msg
  | Some _ -> assert false)
