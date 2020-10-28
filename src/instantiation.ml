open Ast

(*Instantiates all the unversal quantifiers in fml with constants in constlist. *)
let rec instantiate constlist fml =
  match fml with
  | (True | False | Lit _) as f -> f
  | And (f1, f2) -> and_ (instantiate constlist f1) (instantiate constlist f2)
  | Or (f1, f2) -> or_ (instantiate constlist f1) (instantiate constlist f2)
  | Exists (v, f) -> exists v (instantiate constlist f)
  | All (v, f) ->
      let subfml = instantiate constlist f in
      if is_temporal f then
        conj
        @@ List.map
             (fun cur_const -> substitute v ~by:cur_const subfml)
             constlist
      else all v subfml
  | F f -> eventually @@ instantiate constlist f
  | G f -> always @@ instantiate constlist f

  (* Does not handle instantiation in check body because it is to be negated in cervino semantics. *)
let convert ast =
  let const = List.map cst ast.model.constants in
  let updated_axioms = List.map (instantiate const) ast.model.axioms in
  (*let updated_chkbody = instantiate const ast.check.chk_body in*)
  (* let updated_chkbody = ast.check.chk_body in *)
  let updated_assuming = instantiate const ast.check.chk_assuming in
  let updated_model =
    make_model ~sorts:ast.model.sorts ~relations:ast.model.relations
      ~constants:ast.model.constants ~closures:ast.model.closures
      ~axioms:updated_axioms ~events:ast.model.events ()
  in
  let updated_check =
    {ast.check with
    chk_assuming = updated_assuming;
      }
(*    make_check ~chk_name:ast.check.chk_name ~chk_body:updated_chkbody
      ~chk_assuming:updated_assuming ~chk_using:ast.check.chk_using
      *)
  in
  Ast.make ~model:updated_model ~check:updated_check
