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

let main file = 
  let msg = 
    "This program is a proof-of-concept: fed models are taken to be 
    valid Electrum." 
  in
  Messages.info msg;
  let model = parse_file file in
  Messages.info "Showing recognized model (reformatted):";
  Messages.show (Format.to_string Cst.print model);
  (match Wf.analyze_model model with
   | None -> Messages.info "Model is well-formed."
   | Some f -> 
     let faulty = Format.to_string Cst.print_foltl f in
     Messages.fail ("Model is not well-formed, an existential quantifier appears under an `always` connective:\n" ^ faulty))



open Cmdliner
let infile =
  let doc = "File to process (must already be valid Electrum)." in
  Arg.(
    required
    & pos 0 (some ~none:"missing FILE" non_dir_file) None
    & info [] ~docv:"ELECTRUM_FILE" ~doc)

let main_term =
  Term.(
    const main $ infile)


let main_info =
  let doc = "complete verification of (some) Electrum models" in
  let man = [
    `S Manpage.s_authors
  ; `P {|Julien BRUNEL (ONERA), David CHEMOUIL (ONERA), \ 
    Quentin PEYRAS (ONERA).|}
  ; `S "COPYRIGHT"
  ; `P "Cervino (C) 2020 ONERA."
  ; `P
      "Cervino is free software: you can redistribute it and/or modify it \
       under the terms of the Mozilla Public License, v. 2.0. If a copy of \
       the MPL was not distributed with this file, You can obtain one at \
       http://mozilla.org/MPL/2.0/."
  ; `P
      "Cervino is distributed in the hope that it will be useful, but \
       WITHOUT ANY WARRANTY; without even the implied warranty of \
       MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. "
  ; `S "THIRD-PARTY SOFTWARE"
  ; `P
      {|Cervino relies on third-party free software, 
         please refer to the Cervino 
         OPAM repository for the full text of their licenses.|}
  ]
  in
  Term.info "cervino" ~doc ~man


let () =
  (* process commandline arguments and run the actual main (Main.main) function *)
  match Term.eval ~catch:true (main_term, main_info) with
  | _ ->
    exit 1
