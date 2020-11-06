open Ast

let rec check_event evt f =
  match f with
  | Exists ({ var_name; _ }, _) ->
      Msg.err (fun m ->
          m
            "Event `%a`: irregular quantification on `%a`@\n%a"
            Name.pp
            evt
            Name.pp
            var_name
            Location.excerpt
            (Name.positions var_name))
  | G _ ->
      Msg.err (fun m ->
          m "Event `%a` actually contains a `G` connective" Name.pp evt)
  | F _ ->
      Msg.err (fun m ->
          m "Event `%a` actually contains a `F` connective" Name.pp evt)
  | (Lit (Pos_app (n, _, _)) | Lit (Neg_app (n, _, _))) when n > 1 ->
      Msg.err (fun m ->
          m
            "Event `%a` actually refers to later than just the next instant"
            Name.pp
            evt)
  | True | False | Lit _ ->
      ()
  | And (f1, f2) | Or (f1, f2) ->
      check_event evt f1;
      check_event evt f2
  | All (_, f) ->
      check_event evt f


(* checks that a formula is in the ELT fragment *)
let check_elt f =
  let rec check_inner = function
    | Exists ({ var_name; _ }, _) ->
        Msg.err (fun m ->
            m
              "Irregular quantification on `%a`@\n%a"
              Name.pp
              var_name
              Location.excerpt
              (Name.positions var_name))
    | True | False | Lit _ ->
        ()
    | And (f1, f2) | Or (f1, f2) ->
        check_inner f1;
        check_inner f2
    | All (_, f) | G f | F f ->
        check_inner f
  in
  (* the exists quantifier at the toplevel is ok *)
  let rec check_outer = function
    | Exists (_, f) ->
        check_outer f
    | Or (f1, f2) ->
        check_outer f1;
        check_outer f2
    | f ->
        check_inner f
  in
  check_outer f


let check
    { model = { events; axioms; _ }; check = { chk_body; chk_assuming; _ } } =
  List.iter (fun { ev_name; ev_body; _ } -> check_event ev_name ev_body) events;
  List.iter check_elt (chk_assuming :: axioms);
  check_elt (not_ chk_body)
