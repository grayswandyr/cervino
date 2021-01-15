open Ast

(* classic substitution, used below *)
let substitute (subst : (variable * term) list) (t : term) : term =
  match t with
  | Cst _ ->
      t
  | Var x ->
    ( match List.assoc_opt ~eq:equal_variable x subst with
    | None ->
        t
    | Some c ->
        c )


(* unfolds the (G exists ...) event axioms by intantiating every existential quantifier with 2 fresh constants (that must not be considered by instantiation passes). *)
let unfold_event_formula axioms =
  (* keep already created fresh constants (as we will meet the same variable several times, we don't want to create new fresh constants for them) *)
  let constants : (variable * constant list) list ref = ref [] in
  (* retrieves (if they exist) or creates 1 or 2 (depends on formula temporality) fresh constants for a given bound variable *)
  let constants_for_bound_var ({ var_name; var_sort } as var) fml =
    match List.assoc_opt ~eq:equal_variable var !constants with
    | None ->
        let nb = if fst (nb_next fml) then 2 else 1 in
        let base_name = Name.content var_name in
        let cs =
          List.init nb (fun _ ->
              make_constant ~cst_name:(Name.fresh base_name) ~cst_sort:var_sort)
        in
        constants := (var, cs) :: !constants;
        cs
    | Some cs ->
        cs
  in
  (* walk through a formula that began with G immediately followed by exists and unfold existential quantifiers on ad-hoc (fresh) constants. A substitution keeps track of each constant associated to a bound variabe. *)
  let rec unfold (subst : (variable * term) list) fml =
    match fml with
    | Exists (_, v, f) ->
        let cs = constants_for_bound_var v f in
        let fmls = List.map (fun c -> unfold ((v, cst c) :: subst) f) cs in
        disj fmls
    | All (folding_csts, v, f) ->
        (* univ. quantifiers may hide a previous existential binding, so we remove any corresponding association from the substitution before walking down *)
        let subst' =
          List.filter (fun (x, _) -> not @@ equal_variable x v) subst
        in
        all ~folding_csts v (unfold subst' f)
    | True | False ->
        fml
    | F f ->
        eventually @@ unfold subst f
    | G f ->
        always @@ unfold subst f
    | And (f1, f2) ->
        and_ (unfold subst f1) (unfold subst f2)
    | Or (f1, f2) ->
        or_ (unfold subst f1) (unfold subst f2)
    | Lit (Pos_app (nexts, p, args)) ->
        lit (pos_app nexts p (List.map (substitute subst) args))
    | Lit (Neg_app (nexts, p, args)) ->
        lit (neg_app nexts p (List.map (substitute subst) args))
    | Lit (Eq (nexts, t1, t2)) ->
        lit (eq nexts (substitute subst t1) (substitute subst t2))
    | Lit (Not_eq (nexts, t1, t2)) ->
        lit (neq nexts (substitute subst t1) (substitute subst t2))
  in
  (* seek the (G exists ...) formula and unfold its (exists ...) part *)
  let change_event_axiom = function
    | G (Exists _ as f) ->
        Msg.debug (fun m -> m "Found event axiom@.");
        always (unfold [] f)
    | f ->
        f
  in
  let updated_axioms = List.map change_event_axiom axioms in
  (* retrieves the newly created constants *)
  let fresh_constants = List.flat_map snd !constants in
  (fresh_constants, updated_axioms)


(* must be done AFTER instantiation *)
let convert { model; check } =
  let fresh_constants, updated_axioms = unfold_event_formula model.axioms in
  let updated_model =
    make_model
      ~sorts:model.sorts
      ~relations:model.relations
      ~constants:(fresh_constants @ model.constants)
      ~closures:model.closures
      ~axioms:updated_axioms
      ~events:model.events
      ()
  in
  Ast.make ~model:updated_model ~check
