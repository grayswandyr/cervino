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
      @@ CCOpt.map_or ~default:(keyword l) (fun s -> short l ^ s) h


let main verbosity check input output =
  Printexc.record_backtrace true;
  Logs.set_reporter (Logs_fmt.reporter ~pp_header ());
  Fmt_tty.setup_std_outputs ();
  Logs.set_level ~all:true verbosity;
  let version =
    match Build_info.V1.version () with
    | None ->
        "(development version)"
    | Some v ->
        "[" ^ Build_info.V1.Version.to_string v ^ "]"
  in
  Logs.app (fun m ->
      m "%a" Fmt.(styled `Bold string) ("cervino (C) 2020 ONERA " ^ version));
  (* real work done here *)
  try
    Msg.info (fun m -> m "Processing file %S." input);
    let model = Parsing.parse_file input in
    Msg.info (fun m -> m "Parsing done.");
    Msg.debug (fun m -> m "Recognized model:@.%a" Cst.pp model);
    let ast = Cst_to_ast.convert model check in
    Msg.info (fun m -> m "Conversion to AST done.");
    Msg.debug (fun m -> m "AST:@.%a" Ast.pp ast);
    match output with
    | None ->
        Ast.Electrum.pp Fmt.stdout ast
    | Some s ->
        IO.with_out s (fun out ->
            let fmt = Format.formatter_of_out_channel out in
            Ast.Electrum.pp fmt ast)
  with
  | Exit ->
      ()
