open Ast

(* in this file, "E" predicates are called "e_pred" *)

(* given a list of variables [x:s, y:t], returns an assoc list [ ((x,s), _Ex); ((y,t), _Ey)] where
each relation as the same profile as the originating variable (and where variables are typed as
terms). *)
let make_e_preds vars : (term, relation) List.Assoc.t =
  let open List.Infix in
  let+ ({ var_name; var_sort } as v) = vars in
  let e_pred =
    make_relation
      ~rel_name:(Name.create_from_name_and_prefix "_E" var_name)
      ~rel_profile:[ var_sort ]
      ()
  in
  (var v, e_pred)


let get_e_pred v vrs = List.Assoc.get ~eq:equal_term v vrs

let ( .![] ) e_pred arg = lit (pos_app 0 e_pred [ arg ])

let rec abstract_formula (vrs : (term, relation) List.Assoc.t) f : formula =
  match f with
  | True ->
      true_
  | False ->
      false_
  | (Lit (Pos_app (_, _, args)) | Lit (Neg_app (_, _, args))) as literal ->
      let open List.Infix in
      (* get atoms of the shape `! E_y_a(y_a)` for any `y_a` (from `vrs`) that is free in `args` *)
      let negated_e_preds =
        let* term, e_pred = vrs in
        let* () = Mysc.List.guard @@ List.mem ~eq:equal_term term args in
        List.return (not_ e_pred.![term])
      in
      disj (literal :: negated_e_preds)
  | Lit (Eq (t_i, t_j)) as literal ->
    ( match (get_e_pred t_i vrs, get_e_pred t_j vrs) with
    | Some e_pred_i, Some e_pred_j ->
        and_
          (implies e_pred_i.![t_i] e_pred_j.![t_i])
          (implies e_pred_j.![t_j] e_pred_i.![t_j])
    | Some e_pred, None ->
        e_pred.![t_j]
    | None, Some e_pred ->
        e_pred.![t_i]
    | None, None ->
        literal )
  | Lit (Not_eq (t_i, t_j)) as literal ->
    ( match (get_e_pred t_i vrs, get_e_pred t_j vrs) with
    | Some e_pred_i, Some e_pred_j ->
        and_
          (implies e_pred_i.![t_i] @@ not_ e_pred_j.![t_i])
          (implies e_pred_j.![t_j] @@ not_ e_pred_i.![t_j])
    | Some e_pred, None ->
        not_ e_pred.![t_j]
    | None, Some e_pred ->
        not_ e_pred.![t_i]
    | None, None ->
        literal )
  | And (f1, f2) ->
      and_ (abstract_formula vrs f1) (abstract_formula vrs f2)
  | Or (f1, f2) ->
      or_ (abstract_formula vrs f1) (abstract_formula vrs f2)
  | All (x, f) ->
      all x (abstract_formula vrs f)
  | F _ | G _ | Exists _ ->
      (* forbidden cases *)
      Msg.err (fun m ->
          m "[%s] forbidden subformula in an event: %a" __LOC__ pp_formula f)


(* Creates a formula (always all x : s,y :s | ev1[x] or ev2[y]). 
Also returns the list of variables bound by the said quantifier. *)
let abstract_events (events : event list) : relation list * formula =
  let f, vars = Cervino_semantics.quantify_events Ast.all events in
  let vars_e_preds = make_e_preds vars in
  let f' = abstract_formula vars_e_preds f in
  (List.map snd vars_e_preds, f')


(* creates the formula `G (/\ all x,y :s | E(x) && E(y) => x = y) for any `E` predicate (with sort
`s`) *)
let make_e_preds_axiom (e_preds : relation list) : formula =
  let open List.Infix in
  let make_x var_sort =
    make_variable ~var_name:(Name.make_unloc "_x") ~var_sort
  in
  let make_y var_sort =
    make_variable ~var_name:(Name.make_unloc "_y") ~var_sort
  in
  let formulas =
    let+ ({ rel_name; rel_profile } as e_pred) = e_preds in
    match rel_profile with
    | [] | _ :: _ :: _ ->
        Msg.err (fun m ->
            m
              "[%s] %a has arity %d"
              __LOC__
              Name.pp
              rel_name
              (List.length rel_profile))
    | [ s ] ->
        let x = make_x s in
        let y = make_y s in
        let term_x = var x in
        let term_y = var y in
        let e_pred_x = lit @@ pos_app 0 e_pred [ term_x ] in
        let e_pred_y = lit @@ pos_app 0 e_pred [ term_y ] in
        all x
        @@ all y
        @@ implies (and_ e_pred_x e_pred_y) (lit @@ eq term_x term_y)
  in
  always @@ conj formulas


(* Takes a model with events and retruns a model without events, with events expanded and quantified universally; also adds an axiom stating that `E` predicates are "lone". *)
let convert { model; check } =
  let e_preds, all_events_axiom = abstract_events model.events in
  let e_preds_axiom = make_e_preds_axiom e_preds in
  let model' =
    make_model
      ~sorts:model.sorts
      ~relations:(e_preds @ model.relations)
      ~constants:model.constants
      ~closures:model.closures
      ~axioms:(all_events_axiom :: e_preds_axiom :: model.axioms)
      ~events:[]
      ()
  in
  make ~model:model' ~check
