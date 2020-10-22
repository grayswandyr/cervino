open Ast

let expand_evt_modifes { mod_rel; mod_mods } =
  let vars_expand =
    List.foldi
      (fun acc_list i cur_sort ->
        let var =
          make_variable
            ~var_name:(Name.make_unloc ("_m" ^ string_of_int i))
            ~var_sort:cur_sort
        in
        var :: acc_list)
      []
      mod_rel.rel_profile
  in
  let terms_expand = List.map var vars_expand in
  let unchanged_condition =
    List.fold_left
      (fun acc_fml cur_termlist ->
        and_ acc_fml (neq_term_list terms_expand cur_termlist))
      true_
      mod_mods
  in
  let unchanged_formula =
    implies
      unchanged_condition
      (iff
         (lit @@ pos_app 0 mod_rel terms_expand)
         (lit @@ pos_app 1 mod_rel terms_expand))
  in
  List.fold_right all vars_expand unchanged_formula


let expand_modifies_full_event evt =
  let fml_to_add = conj @@ List.map expand_evt_modifes evt.ev_modifies in
  make_event
    ~ev_name:evt.ev_name
    ~ev_args:evt.ev_args
    ~ev_body:(and_ evt.ev_body fml_to_add)
    ~ev_modifies:[]
    ()


let expand_modifies_model m =
  let new_events = List.map expand_modifies_full_event m.events in
  { m with events = new_events }


let convert m_with_check =
  let updated_model = expand_modifies_model m_with_check.model in
  Ast.make ~model:updated_model ~check:m_with_check.check
