open Ast
module Sorts = Name.Set

(*let build_pred_eq = function
| Var (v) -> make_relation ~rel_name:(Name.create_from_name_and_prefix "_eq_" (sort_of_var v)) 
                ~rel_profile:[sort_of_var v] ()
| Cst (c) -> make_relation ~rel_name:(Name.create_from_name_and_prefix "_eq_" (sort_of_cst c))
~rel_profile:[sort_of_cst c] ()

let build_pred_eq_name = function
| Var (v) -> Name.create_from_name_and_prefix "_eq_" (sort_of_var v)
| Cst (c) -> Name.create_from_name_and_prefix "_eq_" (sort_of_cst c)
*)

let build_pred_eq_from_sort s =
  make_relation
    ~rel_name:(Name.create_from_name_and_prefix "_eq_" s)
    ~rel_profile:[ s; s ]
    ()


let build_pred_eq_name_from_sort = Name.create_from_name_and_prefix "_eq_"

let equivalence_axioms_for_rel rel =
  assert (
    List.length rel.rel_profile = 2
    && equal_sort (List.hd rel.rel_profile) (List.nth rel.rel_profile 1) );
  let p = rel.rel_profile in
  let var_sort = List.hd p in
  let varx = make_variable ~var_name:(Name.make_unloc "_x") ~var_sort in
  let tx = var varx in
  let vary = make_variable ~var_name:(Name.make_unloc "_y") ~var_sort in
  let ty = var vary in
  let varz = make_variable ~var_name:(Name.make_unloc "_z") ~var_sort in
  let tz = var varz in
  let app terms = lit @@ pos_app 0 rel terms in
  let refl = app [ tx; tx ] in
  let symm = implies (app [ tx; ty ]) (app [ ty; tx ]) in
  let tran =
    implies (and_ (app [ tx; ty ]) (app [ ty; tz ])) (app [ tx; tz ])
  in
  always @@ all varx @@ all vary @@ all varz @@ conj [ refl; symm; tran ]


let rec remove_eq_fml = function
  | True ->
      (Sorts.empty, true_)
  | False ->
      (Sorts.empty, false_)
  | Lit liter ->
    ( match liter with
    | Pos_app (i, n, tl) ->
        (Sorts.empty, lit (pos_app i n tl))
    | Neg_app (i, n, tl) ->
        (Sorts.empty, lit (neg_app i n tl))
    | Eq (t1, t2) ->
        let s = sort_of_term t1 in
        let pred_eq = build_pred_eq_from_sort s in
        (Sorts.add s Sorts.empty, lit @@ pos_app 0 pred_eq [ t1; t2 ])
    | Not_eq (t1, t2) ->
        let s = sort_of_term t1 in
        let pred_eq = build_pred_eq_from_sort s in
        (Sorts.add s Sorts.empty, lit @@ neg_app 0 pred_eq [ t1; t2 ]) )
  | And (f1, f2) ->
      let ss1, fml1 = remove_eq_fml f1 in
      let ss2, fml2 = remove_eq_fml f2 in
      (Sorts.union ss1 ss2, and_ fml1 fml2)
  | Or (f1, f2) ->
      let ss1, fml1 = remove_eq_fml f1 in
      let ss2, fml2 = remove_eq_fml f2 in
      (Sorts.union ss1 ss2, or_ fml1 fml2)
  | Exists (v, f) ->
      let ss, fml = remove_eq_fml f in
      (ss, exists v fml)
  | All (v, f) ->
      let ss, fml = remove_eq_fml f in
      (ss, all v fml)
  | F f ->
      let ss, fml = remove_eq_fml f in
      (ss, eventually fml)
  | G f ->
      let ss, fml = remove_eq_fml f in
      (ss, always fml)


let remove_eq_fml_list =
  List.fold_left
    (fun (acc_sort_set, acc_fml_list) cur_fml ->
      let new_ss, new_fml = remove_eq_fml cur_fml in
      (Sorts.union acc_sort_set new_ss, new_fml :: acc_fml_list))
    (Sorts.empty, [])


let remove_eq_in_event ev =
  let ss, updated_body = remove_eq_fml ev.ev_body in
  (ss, { ev with ev_body = updated_body })


let remove_eq_in_event_list =
  List.fold_left
    (fun (acc_sort_set, acc_event_list) cur_event ->
      let new_ss, new_event = remove_eq_in_event cur_event in
      (Sorts.union acc_sort_set new_ss, new_event :: acc_event_list))
    (Sorts.empty, [])


(* returns an equality axiom for the ith sort of the profile of rel *)
(* For instance, if p is a rel of profile [s1; s2] equality axiom p 0
   returns the formula
     all x:s1, all y:s1, x=y => all eqvar0 : s2, always p(x, eqvar0) <=> p(y, eqvar0)
*)
let equality_axiom_for_rel_at_i rel i =
  let prof = rel.rel_profile in
  let s = List.nth rel.rel_profile i in
  let restricted_prof = List.filteri (fun k _ -> not @@ Int.equal k i) prof in
  let aux_vars =
    List.foldi
      (fun list_acc i cur_sort ->
        let var =
          make_variable
            ~var_name:(Name.make_unloc ("_e" ^ string_of_int i))
            ~var_sort:cur_sort
        in
        var :: list_acc)
      []
      restricted_prof
  in
  let vars_except_i = List.rev aux_vars in
  let varname_x = Name.make_unloc "_x" in
  let var_x = make_variable ~var_name:varname_x ~var_sort:s in
  let term_x = var var_x in
  let varname_y = Name.make_unloc "_y" in
  let var_y = make_variable ~var_name:varname_y ~var_sort:s in
  let term_y = var var_y in
  let left_tuple = List.insert_at_idx i term_x (List.map var vars_except_i) in
  let right_tuple = List.insert_at_idx i term_y (List.map var vars_except_i) in
  let left_atom = lit @@ pos_app 0 rel left_tuple in
  let right_atom = lit @@ pos_app 0 rel right_tuple in
  all_many vars_except_i (iff left_atom right_atom)


let equality_axiom_for_rel_and_s rel s =
  let eq_axioms, _ =
    List.fold_left
      (fun (cur_list, cur_idx) cur_sort ->
        if equal_sort cur_sort s
        then (equality_axiom_for_rel_at_i rel cur_idx :: cur_list, cur_idx + 1)
        else (cur_list, cur_idx + 1))
      ([], 0)
      rel.rel_profile
  in
  eq_axioms


let equality_axiom_for_rel_list_and_s rel_list s =
  let varname_x = Name.make_unloc "_x" in
  let var_x = make_variable ~var_name:varname_x ~var_sort:s in
  let varname_y = Name.make_unloc "_y" in
  let term_x = var var_x in
  let var_y = make_variable ~var_name:varname_y ~var_sort:s in
  let term_y = var var_y in
  let x_equals_y =
    lit @@ pos_app 0 (build_pred_eq_from_sort s) [ term_x; term_y ]
  in
  always
  @@ all var_x
  @@ all var_y
  @@ implies x_equals_y
  @@ conj
  @@ List.flat_map (fun rel -> equality_axiom_for_rel_and_s rel s) rel_list


(*Adds relations for equality (without adding equality axioms nor replacing '=' is formulas) *)
let add_eq_relations ast =
  let eq_sorts_axioms, _ = remove_eq_fml_list ast.model.axioms in
  let eq_sorts_events, _ = remove_eq_in_event_list ast.model.events in
  let eq_sorts_chk_fml, _ = remove_eq_fml ast.check.chk_body in
  let eq_sorts_assuming, _ = remove_eq_fml ast.check.chk_assuming in
  let eq_sorts =
    Sorts.union eq_sorts_axioms
    @@ Sorts.union
         eq_sorts_events
         (Sorts.union eq_sorts_chk_fml eq_sorts_assuming)
  in
  let relations_eq =
    Sorts.fold
      (fun s rel_list -> build_pred_eq_from_sort s :: rel_list)
      eq_sorts
      []
  in
  let updated_model =
    { ast.model with
      relations =
        List.union
          ~eq:(fun r1 r2 -> Name.equal r1.rel_name r2.rel_name)
          ast.model.relations
          relations_eq
    }
  in
  { model = updated_model; check = ast.check }


(*Adds equality relations (if necessary) and equality axioms and replaces '=' by these relaitons in formulas. *)
let convert ast =
  let eq_sorts_axioms, updated_axioms = remove_eq_fml_list ast.model.axioms in
  let eq_sorts_events, updated_events =
    remove_eq_in_event_list ast.model.events
  in
  let eq_sorts_chk_fml, updated_chk_fml = remove_eq_fml ast.check.chk_body in
  let eq_sorts_assuming, updated_assuming =
    remove_eq_fml ast.check.chk_assuming
  in
  let updated_check =
    { ast.check with
      chk_body = updated_chk_fml;
      chk_assuming = updated_assuming
    }
    (* make_check
       ~chk_name:m.check.chk_name
       ~chk_body:updated_chk_fml
       ~chk_assuming:updated_assuming
       ~chk_using:m.check.chk_using*)
  in
  let eq_sorts =
    Sorts.union eq_sorts_axioms
    @@ Sorts.union
         eq_sorts_events
         (Sorts.union eq_sorts_chk_fml eq_sorts_assuming)
  in
  let relations_eq =
    Sorts.fold
      (fun s rel_list -> build_pred_eq_from_sort s :: rel_list)
      eq_sorts
      []
  in
  let equality_axioms =
    Sorts.fold
      (fun s cur_fmls ->
        equality_axiom_for_rel_list_and_s ast.model.relations s :: cur_fmls)
      eq_sorts
      []
  in
  let equivalence_axs = List.map equivalence_axioms_for_rel relations_eq in
  let updated_model =
    { ast.model with
      relations =
        List.union
          ~eq:(fun r1 r2 -> Name.equal r1.rel_name r2.rel_name)
          ast.model.relations
          relations_eq;
      axioms = equivalence_axs @ equality_axioms @ updated_axioms;
      events = updated_events
    }
  in
  { model = updated_model; check = updated_check }
