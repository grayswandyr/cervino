open Ast

let find_transitive_closure m rel =
  Option.map (fun p -> p.tc)
  @@ List.find_pred
       (fun cur_path -> equal_relation cur_path.base rel)
       m.closures


let closure_axiom m rel x vars fml =
  let s = x.var_sort in
  let x_propag =
    make_variable ~var_name:(Name.make_unloc "_ttc_propagate_x") ~var_sort:s
  in
  let y_propag =
    make_variable ~var_name:(Name.make_unloc "_ttc_propagate_y") ~var_sort:s
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
                 (substitute x x_propag fml)
                 (eventually @@ substitute x y_propag fml) )))
  in
  let fresh_x =
    make_variable ~var_name:(Name.make_unloc "_ttc_x") ~var_sort:s
  in
  let fresh_y =
    make_variable ~var_name:(Name.make_unloc "_ttc_y") ~var_sort:s
  in
  match find_transitive_closure m rel with
  | None ->
      true_
  | Some tc_rel ->
      all
        fresh_x
        ( all fresh_y
        @@ List.fold_right
             all
             vars
             (implies
                (and_
                   propagate
                   (lit @@ pos_app 0 tc_rel [ var fresh_x; var fresh_y ]))
                ( always
                @@ implies
                     (substitute x fresh_x fml)
                     (eventually @@ substitute x fresh_y fml) )) )


let convert m_with_check =
  let m = m_with_check.model in
  let check = m_with_check.check in
  match check.chk_using with
  | TTC (r, x, varlist, fml) ->
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
  | _ ->
      assert false
