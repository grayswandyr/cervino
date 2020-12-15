open Ast

let transform_event_tfc f ev =
  let stab_form = match f ev.ev_name with Some e -> e | None -> ev.ev_body in
  let stab_axiom = implies stab_form (next stab_form) in
  make_event
    ~ev_name:ev.ev_name
    ~ev_args:ev.ev_args
    ~ev_body:(and_ ev.ev_body stab_axiom)
    ~ev_modifies:ev.ev_modifies
    ()


(* In each concerned event : adds the stability axiom and deletes the moddifies field. *)
let convert ({ check = { chk_using; _ }; model } as ast) =
  let updated_events =
    match chk_using with
    | Some (TFC f) ->
        List.map (transform_event_tfc f) model.events
    | _ ->
        failwith
          "error in transfo_TFC.convert: specified transformation is not TFC"
  in
  let updated_model =
    make_model
      ~sorts:model.sorts
      ~relations:model.relations
      ~constants:model.constants
      ~closures:model.closures
      ~axioms:model.axioms
      ~events:updated_events
      ()
  in
  Ast.make ~model:updated_model ~check:ast.check
