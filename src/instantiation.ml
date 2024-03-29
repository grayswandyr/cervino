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


(*Instantiates all the unversal quantifiers "all x | f" in fml with values in
    constlist if f is temporal. 
    Values in constlist are updated by adding existentially quantified vairables.*)
let rec instantiate_tprl constlist fml =
  match fml with
  | (True | False | Lit _) as f ->
      f
  | And (f1, f2) ->
      and_ (instantiate_tprl constlist f1) (instantiate_tprl constlist f2)
  | Or (f1, f2) ->
      or_ (instantiate_tprl constlist f1) (instantiate_tprl constlist f2)
  | Exists (folding_csts, v, f) ->
      exists ~folding_csts v (instantiate_tprl (var v :: constlist) f)
  | All (None, v, f) ->
      let subfml = instantiate_tprl constlist f in
      if is_temporal f
      then instantiate_constants v constlist subfml
      else all ~folding_csts:None v subfml
  | All (Some [], _, _) ->
      true_
  | All ((Some csts as folding_csts), v, f) ->
      let csts_sorts =
        List.map (fun c -> c.cst_sort) csts |> List.sort_uniq ~cmp:compare_sort
      in
      if List.length csts_sorts >= 2
      then
        Msg.err (fun m ->
            m
              "Folding constants with different sorts: %a"
              Format.(list Name.pp)
              (List.map (fun c -> c.cst_name) csts))
      else
        let sort = List.hd csts_sorts in
        if not @@ equal_sort sort v.var_sort
        then
          Msg.err (fun m ->
              m
                "Folding constant(s) with sort %a but quantified variable %a \
                 has sort %a"
                Name.pp
                sort
                Name.pp
                v.var_name
                Name.pp
                v.var_sort)
        else
          let subfml = instantiate_tprl constlist f in
          if is_temporal f
          then instantiate_constants v (List.map cst csts) subfml
          else all ~folding_csts v subfml
  | F f ->
      eventually @@ instantiate_tprl constlist f
  | G f ->
      always @@ instantiate_tprl constlist f


(* Instantiates all subformulas of the form (all x | f) in fml with values
    in constlist if f includes an existential quantifer. 
    Values in constlist are updated by adding existentially quantified vairables.*)
let rec instantiate_ae constlist fml =
  match fml with
  | (True | False | Lit _) as f ->
      f
  | And (f1, f2) ->
      and_ (instantiate_ae constlist f1) (instantiate_ae constlist f2)
  | Or (f1, f2) ->
      or_ (instantiate_ae constlist f1) (instantiate_ae constlist f2)
  | Exists (folding_csts, v, f) ->
      exists ~folding_csts v (instantiate_ae (var v :: constlist) f)
  | All (folding_csts, v, f) ->
      let subfml = instantiate_ae constlist f in
      if includes_exists f
      then instantiate_constants v constlist subfml
      else all ~folding_csts v subfml
  | F f ->
      eventually @@ instantiate_ae constlist f
  | G f ->
      always @@ instantiate_ae constlist f


let convert_ae ast =
  let const = List.map cst ast.model.constants in
  let updated_axioms = List.map (instantiate_ae const) ast.model.axioms in
  let updated_assuming = instantiate_ae const ast.check.chk_assuming in
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
