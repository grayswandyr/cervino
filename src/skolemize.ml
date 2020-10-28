open Ast

let constant_from_var var_x =
  let xname = var_x.var_name in
  let n = Name.make ("_sk_" ^ Name.content xname) (Name.positions xname) in
  make_constant ~cst_name:n ~cst_sort:var_x.var_sort


let rec skolemize fml =
  match fml with
  | True | False | Lit _ ->
      ([], fml)
  | And (f1, f2) ->
      let csts1, skfml1 = skolemize f1 in
      let csts2, skfml2 = skolemize f2 in
      (List.append csts1 csts2, and_ skfml1 skfml2)
  | Or (f1, f2) ->
      let csts1, skfml1 = skolemize f1 in
      let csts2, skfml2 = skolemize f2 in
      (List.append csts1 csts2, or_ skfml1 skfml2)
  | Exists (x, f) ->
      let cst_x = constant_from_var x in
      let csts_f, skfml = skolemize f in
      (cst_x :: csts_f, substitute x ~by:(cst cst_x) skfml)
  | All _ ->
      ([], fml)
  | F f ->
      skolemize f
  | G f ->
      ([], always f)


let skolemize_list_fml fml_list =
  List.fold_right
    (fun f (cur_csts, cur_axioms) ->
      let c, skfml = skolemize f in
      (List.append c cur_csts, skfml :: cur_axioms))
    fml_list
    ([], [])


(* Does not handle check body formula because it is to be negated. *)
let convert ast =
  let ast_mod = ast.model in
  let csts_from_axioms, updated_axioms = skolemize_list_fml ast_mod.axioms in
  let csts_from_assuming, updated_assuming = skolemize ast.check.chk_assuming in
  let updated_csts =
    List.append ast_mod.constants
    @@ List.append csts_from_axioms csts_from_assuming
  in
  let m =
    make_model
      ~sorts:ast_mod.sorts
      ~relations:ast_mod.relations
      ~constants:updated_csts
      ~closures:ast_mod.closures
      ~axioms:updated_axioms
      ~events:ast_mod.events
      ()
  in
  let updated_chk = { ast.check with chk_assuming = updated_assuming } in
  Ast.make ~model:m ~check:updated_chk
