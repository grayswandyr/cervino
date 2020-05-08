open Libcervino
open Containers
module M = Messages
module L = Location

let parse_file file =
  let open Parser in
  IO.with_in file
  @@ fun ic ->
  let lexbuf = Lexing.from_channel ic in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = file };
  try parse Scanner.main lexbuf with
  | Error ->
      M.located_fail lexbuf "Syntax error"


let main file debug =
  if debug then M.debug_is_on := true;
  M.info "This program expects valid Electrum files.";
  let model = parse_file file in
  M.debug "Recognized model:";
  M.debug Format.(sprintf "@\n%a" Cst.print model);
  Wf.check_and_report model;
  let model' = Abstraction.abstract_model model in
  M.info Format.(sprintf "Generated model:@\n%a" Cst.print model')
