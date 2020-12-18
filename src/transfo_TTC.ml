open Ast

let find_transitive_closure m rel =
  Option.map (fun p -> p.tc)
  @@ List.find_pred
       (fun cur_path -> equal_relation cur_path.base rel)
       m.closures


let closure_axiom m rel x vars fml =
  let s = x.var_sort in
  let x_propag =
    make_variable ~var_name:(Name.make_unloc "_tcPx") ~var_sort:s
  in
  let y_propag =
    make_variable ~var_name:(Name.make_unloc "_tcPy") ~var_sort:s
  in

  let propagate =
    all
      x_propag
      (all
         y_propag
         (implies
            (lit @@ pos_app 0 rel [ var x_propag; var y_propag ])
            ( always
            @@ implies
                 (substitute x ~by:(var x_propag) fml)
                 (eventually @@ substitute x ~by:(var y_propag) fml) )))
  in
  let fresh_x = make_variable ~var_name:(Name.make_unloc "_tcx") ~var_sort:s in
  let fresh_y = make_variable ~var_name:(Name.make_unloc "_tcy") ~var_sort:s in
  let term_x = var fresh_x in
  let term_y = var fresh_y in
  match find_transitive_closure m rel with
  | None ->
      true_
  | Some tc_rel ->
      all_many
        vars
        ( implies propagate
        @@ all_many
             [ fresh_x; fresh_y ]
             (implies
                (lit @@ pos_app 0 tc_rel [ term_x; term_y ])
                ( always
                @@ implies
                     (substitute x ~by:term_x fml)
                     (eventually @@ substitute x ~by:term_y fml) )) )


(* Adds the TC axiom to the model axioms. Same as convert except that in the
   added axiom, the universal quantifiers that have an existential quantifier
   in their scope are instantiated. This allows these existential quantifiers
   to be later skolemized.
*)
let convert_instantiated_TC_axiom ast =
  let m = ast.model in
  let check = ast.check in
  let const = List.map cst ast.model.constants in
  match check.chk_using with
  | Some (TTC (Some (r, x, varlist, fml))) ->
      let tc_axiom = closure_axiom m r x varlist fml in
      let inst_tc_axiom = Instantiation.instantiate_ae const tc_axiom in
      let updated_axioms = inst_tc_axiom :: m.axioms in
      let updated_model =
        make_model
          ~sorts:m.sorts
          ~relations:m.relations
          ~constants:m.constants
          ~closures:m.closures
          ~axioms:updated_axioms
          ~events:m.events
          ()
      in
      Ast.make ~model:updated_model ~check
  | Some (TTC None) ->
      ast
  | _ ->
      assert false


(* Adds the transitive closure axiom to the model axioms. *)
let convert ast =
  let m = ast.model in
  let check = ast.check in
  match check.chk_using with
  | Some (TTC (Some (r, x, varlist, fml))) ->
      let updated_axioms = closure_axiom m r x varlist fml :: m.axioms in
      let updated_model =
        make_model
          ~sorts:m.sorts
          ~relations:m.relations
          ~constants:m.constants
          ~closures:m.closures
          ~axioms:updated_axioms
          ~events:m.events
          ()
      in
      Ast.make ~model:updated_model ~check
  | Some (TTC None) ->
      ast
  | _ ->
      assert false
