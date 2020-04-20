open Cmdliner

(* DOC *)

let main_info =
  let doc = "complete verification of (some) Electrum models" in
  let man =
    [ `S "RECOGNIZED LANGUAGE"
    ; `P
        {|Cervino makes almost no analysis of fed models, so these must already be valid Electrum. Furthermore, only a small fragment of the language is recognized, which essentially corresponds to MS-FOLTL in Electrum syntax. The following is NOT accepted: opening modules; relation qualifiers; `one`, `lone`  and `no` quantifiers; relation composition operators (except `->` to form tuples, of constants and bound variables only); unnamed commands;  `extends` keyword. Also, zero-argument predicates must be called with `[]`. 
    |}
    ; `S "EVENTS and TRACES"
    ; `P
        {|Cervino expects models where events are modelled as predicates whose name begins with an underscore `_` and is at least 3 characters long (incl. `_`). The body of such events can only contain conjuctions or disjunctions of universally-quantified relation applications (primed or not). Said otherwise, the body of events should look like:|}
    ; `P "{ (all x : S | x->c in r1) and (all y : T : d->y not in r2) ... }"
    ; `P
        {|Cervino also expects that input models feature a fact called `_events` that only says that, at any instant, there are suitable valuations of event parameters so that at least one event is fired. Said otherwise, the fact body looks like :|}
    ; `P "{ always (some p1: S, p2: T | _e1[p1, p2] or _e2[p1] or...) }"
    ; `P
        {|When Cervino applies its algorithm, this fact will be deleted, os it is important that it only contains the formula shown above (in particular, initial conditions should be stated elsewhere).|}
    ; `S Manpage.s_authors
    ; `P
        {|Julien BRUNEL (ONERA), David CHEMOUIL (ONERA), Quentin PEYRAS (ONERA).|}
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


(* OPTIONS *)

let infile =
  let doc = "File to process (must already be valid Electrum)." in
  Arg.(
    required
    & pos 0 (some ~none:"missing FILE" non_dir_file) None
    & info [] ~docv:"ELECTRUM_FILE" ~doc)

let debug =
  let doc =
    {|If present, print debugging information. |}
  in
  Arg.(value & flag & info [ "d" ] ~doc)


let main_term = Term.(const Main.main $ infile $ debug)

(* MAIN *)

let () =
  match Term.eval ~catch:true (main_term, main_info) with
  | `Error _ ->
    exit 1
  | _ ->
    exit 0
