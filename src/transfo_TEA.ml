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
  | All (folding_csts, x, f) ->
      all ?folding_csts x (abstract_formula vrs f)
  | F _ | G _ | Exists _ ->
      (* forbidden cases *)
      Msg.err (fun m ->
          m "[%s] forbidden subformula in an event: %a" __LOC__ pp_formula f)


(* Creates a formula (always all x : s,y :s | ev1[x] or ev2[y]). 
Also returns the list of variables bound by the said quantifier. *)
let abstract_events (events : event list) : relation list * formula =
  (* notice `f` does not contain a leading `always`, see def. of `quantify_events` *)
  let f, vars = Cervino_semantics.quantify_events Ast.all events in
  let vars_e_preds = make_e_preds vars in
  (* add missing `always` after abstracting (as abstraction fails on F/G/exists) *)
  let f' = always @@ abstract_formula vars_e_preds f in
  (List.map snd vars_e_preds, f')


(* creates the formula `G (/\ all x,y :s | E(x) && E(y) => x = y) for any `E` predicate (with sort
`s`) (technically, it's made sort by sort, to avoid repeating the same quantification. *)
let make_e_preds_axiom (e_preds : relation list) : formula =
  let open List.Infix in
  let make_x var_sort =
    make_variable ~var_name:(Name.make_unloc "_eax") ~var_sort
  in
  let make_y var_sort =
    make_variable ~var_name:(Name.make_unloc "_eay") ~var_sort
  in
  let e_preds_by_sort =
    let hash { rel_profile; rel_name } =
      match rel_profile with
      | [ s ] ->
          Name.hash s
      | [] | _ :: _ :: _ ->
          Msg.err (fun m ->
              m
                "[%s] %a has arity %d"
                __LOC__
                Name.pp
                rel_name
                (List.length rel_profile))
    in
    let eq r1 r2 = List.equal Name.equal r1.rel_profile r2.rel_profile in
    List.group_by ~hash ~eq e_preds
  in
  let formulas =
    let* e_preds_for_one_sort = e_preds_by_sort in
    let the_sort =
      match e_preds_for_one_sort with
      | { rel_profile = [ s ]; _ } :: _ ->
          s
      | _ ->
          assert false
    in
    let x = make_x the_sort in
    let y = make_y the_sort in
    let term_x = var x in
    let term_y = var y in
    let formula_for_one_sort =
      let* e_pred = e_preds_for_one_sort in
      let e_pred_x = lit @@ pos_app 0 e_pred [ term_x ] in
      let e_pred_y = lit @@ pos_app 0 e_pred [ term_y ] in
      List.return @@ implies (and_ e_pred_x e_pred_y) (lit @@ eq term_x term_y)
    in
    List.return @@ all x @@ all y @@ conj formula_for_one_sort
  in
  always @@ conj formulas


(* Takes a model with events and retruns a model without events, with events expanded and quantified universally; also adds an axiom stating that `E` predicates are "lone". *)
let convert { model; check } =
  let e_preds, axiom_for_events = abstract_events model.events in
  let e_preds_axiom = make_e_preds_axiom e_preds in
  let updated_relations = e_preds @ model.relations in
  let check_as_axiom = not_ check.chk_body in
  let updated_axioms =
    e_preds_axiom
    :: axiom_for_events
    :: check_as_axiom
    :: check.chk_assuming
    :: model.axioms
  in
  let updated_model =
    make_model
      ~sorts:model.sorts
      ~relations:updated_relations
      ~constants:model.constants
      ~closures:model.closures
      ~axioms:updated_axioms
      ~events:[]
      ()
  in
  let updated_check = { check with chk_body = false_; chk_assuming = true_ } in
  make ~model:updated_model ~check:updated_check
