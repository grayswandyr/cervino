open Libcervino

(* inspired by Logs_fmt code *)
let keyword =
  let open! Logs in
  function
  | App -> "" | Error -> "E" | Warning -> "W" | Info -> "I" | Debug -> "D"


let short =
  let open! Logs in
  function
  | App -> "" | Error -> "E" | Warning -> "W" | Info -> "I" | Debug -> "D"


let pp_header ppf (l, h) =
  let open! Logs in
  let open Logs_fmt in
  let pp_h ppf style h = Fmt.pf ppf "[%a] " Fmt.(styled style string) h in
  match l with
  | App ->
    ( match h with
    | None ->
        ()
    | Some h ->
        Fmt.pf ppf "[%a] " Fmt.(styled app_style string) h )
  | Error | Warning | Info | Debug ->
      pp_h ppf (Msg.style l)
      @@ Option.map_or ~default:(keyword l) (fun s -> short l ^ s) h


let run_electrum java_exe electrum_jar cervino_file property electrum_file =
  (* Inspired by nunchaku-inria/logitest/src/Misc.ml (BSD licence). *)
  let sigterm_handler =
    Sys.Signal_handle
      (fun _ ->
        print_endline "Received termination signal! Exiting.";
        Unix.kill 0 Sys.sigterm;
        (* kill children *)
        exit 1)
  in
  let previous_handler = Sys.signal Sys.sigterm sigterm_handler in
  let to_call =
    Printf.sprintf
      "%s -jar %s --cli --nuXmv %s"
      java_exe
      electrum_jar
      electrum_file
  in
  Msg.info (fun m -> m "Calling solver:@[<h2>@ %s@]" to_call);
  (* currently, EA prints on the error output rather than the standard one, even for working runs *)
  let _okout, errout, errcode = CCUnix.call "%s" to_call in
  (* go back to default behavior *)
  Sys.set_signal Sys.sigterm previous_handler;
  if errcode <> 0
  then
    Msg.err (fun m ->
        m
          "Error when running the Electrum Analyzer solver:@\n\
           Error code: %d@\n\
           Full output: %s"
          errcode
          errout)
  else if (* currently, EA prints on the error output rather than the standard one, even for working runs *)
          String.Find.(find ~pattern:(compile "(outcome UNSAT)") errout) > -1
  then
    Logs.app (fun m -> m "File %S, property %S: valid." cervino_file property)
  else if String.Find.(find ~pattern:(compile "(outcome SAT)") errout) > -1
  then
    Logs.app (fun m ->
        m "File %S, property %S: cannot conclude." cervino_file property)
  else
    Msg.err (fun m ->
        m
          "Error when running the Electrum Analyzer solver:@\nFull output: %s"
          errout)


let main
    call_solver
    electrum_jar
    java_exe
    verbosity
    nobound
    preinstantiate_only
    instantiate_only
    unfold_event_axiom
    output_cervino
    property
    input_file
    output_file =
  Printexc.record_backtrace true;
  Logs.set_reporter (Logs_fmt.reporter ~pp_header ());
  Fmt_tty.setup_std_outputs ();
  Logs.set_level ~all:true verbosity;
  if call_solver && String.is_empty electrum_jar
  then
    Msg.err (fun m ->
        m
          "Error: no known path to the Electrum Analyzer JAR (check usage of \
           --ej option or ELECTRUM_JAR environment variable)");
  if call_solver && output_cervino
  then Msg.err (fun m -> m "Error: incompatible flags: -s and -c");
  if preinstantiate_only && instantiate_only
  then Msg.err (fun m -> m "Error: incompatible flags: -p and -i");
  let version =
    match Build_info.V1.version () with
    | None ->
        "(development version)"
    | Some v ->
        "[" ^ Build_info.V1.Version.to_string v ^ "]"
  in
  Logs.app (fun m ->
      m "%a" Fmt.(styled `Bold string) ("cervino (C) 2020-2021 ONERA " ^ version));
  (* real work done here *)
  try
    Msg.info (fun m -> m "Processing file %S." input_file);
    let model = Parsing.parse_file input_file in
    Msg.info (fun m -> m "Parsing done.");
    Msg.debug (fun m -> m "Recognized model:@.%a" Cst.pp model);
    let ast = Cst_to_ast.convert model property in
    Msg.info (fun m -> m "Conversion to AST done.");
    Msg.debug (fun m -> m "AST:@.%a" Ast.pp ast);

    if not instantiate_only then Wf.check ast;
    let result_wo_bounds =
      Transfo.convert
        ~preinstantiate_only
        ~instantiate_only
        ~unfold_event_axiom
        ast
    in
    let result =
      if nobound || Option.is_none ast.check.chk_using
      then result_wo_bounds
      else Ast.compute_scope result_wo_bounds
    in
    let pp =
      if output_cervino
      then Ast.Cervino.pp
      else Ast.pp_electrum ast.check.chk_using
    in
    match output_file with
    | None ->
        if call_solver
        then (
          let electrum_file = Filename.temp_file "cervino" ".als" in
          IO.with_out electrum_file (fun out ->
              let fmt = Format.formatter_of_out_channel out in
              pp fmt result);
          run_electrum java_exe electrum_jar input_file property electrum_file )
        else pp Fmt.stdout result
    | Some electrum_file ->
        IO.with_out electrum_file (fun out ->
            let fmt = Format.formatter_of_out_channel out in
            pp fmt result);
        if call_solver
        then
          run_electrum java_exe electrum_jar input_file property electrum_file
  with
  | Exit ->
      ()
