open Ast

(* 
let instantiate_constants v consts fml =
    conj
        @@ List.map (fun cur_const -> substitute v ~by:cur_const subfml)
        @@ List.filter
             (fun c -> equal_sort v.var_sort (sort_of_term c))
             constlist
*)
let instantiate_constants v consts fml =
  (* use the list monad operator: let* *)
  let open List.Infix in
  (* define the set of formulas as follows: *)
  let fmls =
    (* for any c in consts *)
    let* c = consts in
    (* such that the guard is true *)
    let* () = Mysc.List.guard (equal_sort v.var_sort (sort_of_term c)) in
    (* return the substitution *)
    List.return @@ substitute v ~by:c fml
  in
  conj fmls


(*Instantiates all the unversal quantifiers in fml with constants in constlist. *)
let rec instantiate_tprl constlist fml =
  match fml with
  | (True | False | Lit _) as f ->
      f
  | And (f1, f2) ->
      and_ (instantiate_tprl constlist f1) (instantiate_tprl constlist f2)
  | Or (f1, f2) ->
      or_ (instantiate_tprl constlist f1) (instantiate_tprl constlist f2)
  | Exists (v, f) ->
      exists v (instantiate_tprl constlist f)
  | All (v, f) ->
      let subfml = instantiate_tprl constlist f in
      if is_temporal f
      then instantiate_constants v constlist subfml
      else all v subfml
  | F f ->
      eventually @@ instantiate_tprl constlist f
  | G f ->
      always @@ instantiate_tprl constlist f


let rec instantiate_ae constlist fml =
  match fml with
  | (True | False | Lit _) as f ->
      f
  | And (f1, f2) ->
      and_ (instantiate_ae constlist f1) (instantiate_ae constlist f2)
  | Or (f1, f2) ->
      or_ (instantiate_ae constlist f1) (instantiate_ae constlist f2)
  | Exists (v, f) ->
      exists v (instantiate_ae constlist f)
  | All (v, f) ->
      let subfml = instantiate_ae constlist f in
      if includes_exists f
      then instantiate_constants v constlist subfml
      else all v subfml
  | F f ->
      eventually @@ instantiate_ae constlist f
  | G f ->
      always @@ instantiate_ae constlist f


(* Does not handle instantiation in check body because it is to be negated in cervino semantics. *)
let convert ast =
  let const = List.map cst ast.model.constants in
  let updated_axioms = List.map (instantiate_tprl const) ast.model.axioms in
  let updated_assuming = instantiate_tprl const ast.check.chk_assuming in
  let updated_model =
    make_model
      ~sorts:ast.model.sorts
      ~relations:ast.model.relations
      ~constants:ast.model.constants
      ~closures:ast.model.closures
      ~axioms:updated_axioms
      ~events:ast.model.events
      ()
  in
  let updated_check = { ast.check with chk_assuming = updated_assuming } in
  Ast.make ~model:updated_model ~check:updated_check
