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


let main file =
  let msg =
    "This program is a proof-of-concept: fed models are taken to be \n\
    \    valid Electrum."
  in
  M.info msg;
  let model = parse_file file in
  M.info "Showing recognized model (reformatted):";
  M.show (Format.to_string Cst.print model);
  match Wf.analyze_model model with
  | None ->
      M.info "Model is well-formed."
  | Some
      ( ((L.{ loc = g_loc; _ } as g), g_pol)
      , (pol, (L.{ data = Quant (q, _, _); loc } as f)) ) ->
      let g_polarity = if g_pol then "n" else " negated" in
      let f_polarity = if pol then "" else "negatively " in
      let msg =
        Format.(
          sprintf
            "`%a` appears %sunder a%s `always` connective:@\n\
             %d:%d-...: %a@\n\
             %d:%d-...: %a"
            Cst.print_quant
            q
            f_polarity
            g_polarity
            (L.begl g_loc)
            (L.begc g_loc)
            Cst.print_foltl
            g
            (L.begl loc)
            (L.begc loc)
            Cst.print_foltl
            f)
      in

      M.fail msg
  | Some _ ->
      assert false