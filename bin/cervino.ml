open Cmdliner

(* DOC *)

let main_info =
  let doc = "verification of Cervino models" in
  let man =
    [ `S Manpage.s_authors;
      `P
        {|Julien BRUNEL (ONERA), David CHEMOUIL (ONERA), Quentin PEYRAS (ONERA).|};
      `S "COPYRIGHT";
      `P "Cervino (C) 2020-2021 ONERA.";
      `P
        "Cervino is free software: you can redistribute it and/or modify it \
         under the terms of the Mozilla Public License, v. 2.0. If a copy of \
         the MPL was not distributed with this file, You can obtain one at \
         http://mozilla.org/MPL/2.0/.";
      `P
        "Cervino is distributed in the hope that it will be useful, but \
         WITHOUT ANY WARRANTY; without even the implied warranty of \
         MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. ";
      `S "THIRD-PARTY SOFTWARE";
      `P
        {|Cervino relies on third-party free software, 
         please refer to their respective OPAM 
         repository for the full text of their licenses.|}
    ]
  in
  Term.info "cervino.exe" ~doc ~man ~exits:Term.default_exits


(* OPTIONS *)
let nobound =
  let doc =
    "If present, does not compute the scope (the bound on the sort domain)."
  in
  Arg.(value & flag & info [ "nb"; "nobound" ] ~doc)


let preinstantiate_only =
  let doc = "If present, perform a pre-instantiation step." in
  Arg.(value & flag & info [ "p"; "pre-instantiate" ] ~doc)


let instantiate_only =
  let doc =
    "If present, perform the instantiation pass only (deactivates the \
     well-formedness check)."
  in
  Arg.(value & flag & info [ "i"; "instantiate" ] ~doc)


let unfold_event_quantification =
  let doc =
    "If present, unfold the event axiom existential quantification (brittle \
     option)."
  in
  Arg.(value & flag & info [ "u"; "unfold-event-axiom" ] ~doc)


let output_cervino =
  let doc = "If present, output Cervino code (Electrum code otherwise)." in
  Arg.(value & flag & info [ "c"; "cervino" ] ~doc)


let check =
  let doc = "Name of the property to check." in
  Arg.(
    required
    & pos 0 (some ~none:"missing PROPERTY" string) None
    & info [] ~docv:"PROPERTY" ~doc)


let infile =
  let doc = "Input (Cervino) file." in
  Arg.(
    required
    & pos 1 (some ~none:"missing CERVINO_FILE" non_dir_file) None
    & info [] ~docv:"CERVINO_FILE" ~doc)


let outfile =
  let doc =
    "Name of the file to generate. If absent, the file is printed on the \
     standard output (except if the -s option is present)."
  in
  Arg.(value & pos 2 (some string) None & info [] ~docv:"OUTPUT_FILE" ~doc)


let call_electrum =
  let doc =
    "If present, let Cervino call the Electrum Analyzer solver (with the nuXmv \
     model checker) on the generated Electrum file and report its result. The \
     Electrum Analyzer and nuXmv must be properly installed. The path to the \
     JAR containing the Electrum Analyzer must be set using the --ej option or \
     ELECTRUM_JAR environment variable. The `java` program must also be in the \
     PATH."
  in
  Arg.(value & flag & info [ "s"; "solve" ] ~doc)


let electrum_jar =
  let doc = "Path to the Electrum Analyzer JAR file" in
  let env = Arg.env_var ~doc "ELECTRUM_JAR" in
  Arg.(
    value
    & opt non_dir_file ""
    & info [ "ej"; "electrum-jar" ] ~docv:"PATH" ~doc ~env)


let java_exe =
  let doc = "Path to the `java` program" in
  Arg.(value & opt non_dir_file "java" & info [ "java" ] ~docv:"PATH" ~doc)


(* verbosity options (already def'd in Logs_cli, thx!) *)
let verbosity = Logs_cli.level ()

let main_term =
  Term.(
    const Main.main
    $ call_electrum
    $ electrum_jar
    $ java_exe
    $ verbosity
    $ nobound
    $ preinstantiate_only
    $ instantiate_only
    $ unfold_event_quantification
    $ output_cervino
    $ check
    $ infile
    $ outfile)


(* MAIN *)

let main = (main_term, main_info)

let () = Term.(exit @@ eval ~catch:false main)
