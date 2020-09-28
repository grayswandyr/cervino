module Setup = struct
  let cervino_src =
    Logs.Src.create "cervino.onera.fr" ~doc:"logs cervino events"


  module M = (val Logs.src_log cervino_src : Logs.LOG)

  include M
end

let debug = Setup.debug

let info = Setup.info

let warn = Setup.warn

let err m = Setup.kmsg (fun () -> raise Exit) Logs.Error m

let style =
  let open! Logs in
  let open Logs_fmt in
  function
  | App ->
      app_style
  | Error ->
      err_style
  | Warning ->
      warn_style
  | Info ->
      info_style
  | Debug ->
      debug_style
