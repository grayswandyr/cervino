open Ast

let check_event { ev_name; ev_body; _ } =
  let rec walk f =
    match f with
    | Exists (_, { var_name; _ }, _) ->
        Msg.err (fun m ->
            m
              "Event `%a`: irregular quantification on `%a`@\n%a"
              Name.pp
              ev_name
              Name.pp
              var_name
              Location.excerpt
              (Name.positions var_name))
    | G _ ->
        Msg.err (fun m ->
            m "Event `%a` actually contains a `G` connective" Name.pp ev_name)
    | F _ ->
        Msg.err (fun m ->
            m "Event `%a` actually contains a `F` connective" Name.pp ev_name)
    | (Lit (Pos_app (n, _, _)) | Lit (Neg_app (n, _, _))) when n > 1 ->
        Msg.err (fun m ->
            m
              "Event `%a` actually refers to later than just the next instant"
              Name.pp
              ev_name)
    | True | False | Lit _ ->
        ()
    | And (f1, f2) | Or (f1, f2) ->
        walk f1;
        walk f2
    | All (_, _, f) ->
        walk f
  in
  walk ev_body


let check_elt f =
  let module Env = struct
    type t =
      { saw_g : bool;
        saw_all : bool;
        saw_all_exists : bool
      }

    let empty = { saw_g = false; saw_all = false; saw_all_exists = false }
  end in
  let open Env in
  let rec walk env = function
    | Exists (_, { var_name; _ }, _) when env.saw_g ->
        Msg.err (fun m ->
            m
              "Irregular quantification (nesting of type G/some) on `%a`@\n%a"
              Name.pp
              var_name
              Location.excerpt
              (Name.positions var_name))
    | All (_, { var_name; _ }, _) when env.saw_all_exists ->
        Msg.err (fun m ->
            m
              "Irregular quantification (nesting of type all/some/all) on `%a`@\n\
               %a"
              Name.pp
              var_name
              Location.excerpt
              (Name.positions var_name))
    | Exists (_, _, f) when env.saw_all ->
        walk { env with saw_all_exists = true } f
    | Exists (_, _, f) ->
        walk env f
    | All (_, _, f) ->
        walk { env with saw_all = true } f
    | G f ->
        walk { env with saw_g = true } f
    | F f ->
        walk env f
    | True | False | Lit _ ->
        ()
    | And (f1, f2) | Or (f1, f2) ->
        walk env f1;
        walk env f2
  in
  walk Env.empty f


let check
    { model = { events; axioms; _ }; check = { chk_body; chk_assuming; _ } } =
  List.iter check_event events;
  List.iter check_elt (not_ chk_body :: chk_assuming :: axioms)
