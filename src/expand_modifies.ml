open Ast

let expand_evt_modifies { mod_rel; mod_mods } =
  let vars_expand =
    List.foldi
      (fun acc_list i cur_sort ->
        let var =
          make_variable
            ~var_name:(Name.make_unloc ("_em" ^ string_of_int i))
            ~var_sort:cur_sort
        in
        var :: acc_list)
      []
      mod_rel.rel_profile
    (* fix reversed order in accumulator above *)
    |> List.rev
  in
  let terms_expand = List.map var vars_expand in
  let unchanged_conditions = List.map (neq_term_list terms_expand) mod_mods in
  let same =
    iff
      (lit @@ pos_app 0 mod_rel terms_expand)
      (lit @@ pos_app 1 mod_rel terms_expand)
  in
  let unchanged_formula = implies (conj unchanged_conditions) same in
  (*if mod_mods is empty, meaning there is "modifies r" without "at t1, t2" then do not add any frame condition for r*)
  if List.is_empty mod_mods
  then true_
  else all_many vars_expand unchanged_formula


let expand_modifies_full_event relations evt =
  (* non-cited relations must be processed too, by saying they modify nothing *)
  let non_cited_modifies =
    let open List.Infix in
    let* rel = relations in
    let* () =
      Mysc.List.guard
      @@ not
      @@ List.exists
           (fun { mod_rel; _ } -> equal_relation mod_rel rel)
           evt.ev_modifies
    in
    List.return @@ make_ev_modify ~mod_rel:rel ()
  in
  let fml_to_add =
    conj @@ List.map expand_evt_modifies (evt.ev_modifies @ non_cited_modifies)
  in
  make_event
    ~ev_name:evt.ev_name
    ~ev_args:evt.ev_args
    ~ev_body:(and_ evt.ev_body fml_to_add)
    ~ev_modifies:[]
    ()


let expand_modifies_model m =
  let new_events = List.map (expand_modifies_full_event m.relations) m.events in
  { m with events = new_events }


let convert m_with_check =
  let updated_model = expand_modifies_model m_with_check.model in
  Ast.make ~model:updated_model ~check:m_with_check.check
