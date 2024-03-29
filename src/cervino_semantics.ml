open Ast
module SortBag = Name.Bag
module VarMap = Name.Map

let create_var s i =
  make_variable
    ~var_name:(Name.make_unloc ("_s_" ^ Name.content s ^ string_of_int i))
    ~var_sort:s


let create_vars_up_to_k s k =
  assert (k > 0);
  let rec walk vars i =
    if i <= 0 then vars else walk (create_var s i :: vars) (i - 1)
  in
  walk [] k


let nb_occ list elt = List.count (fun x -> equal_sort (fst x) elt) list

let occ_list_from_sortlist sortlist =
  let rec walk acc sortlist =
    match sortlist with
    | [] ->
        List.rev acc
    | hd :: tl ->
        let n = nb_occ acc hd in
        walk ((hd, n + 1) :: acc) tl
  in
  walk [] sortlist


let find_fresh_vars_from_occ_list map occlist =
  let open List.Infix in
  (* let+ s, i occlist in E  === List.map (fun (s,i) -> E) occlist *)
  let+ s, i = occlist in
  assert (i > 0);
  match VarMap.get s map with
  | None ->
      Msg.err (fun m -> m "[%s] sort not found: %a" __LOC__ Name.pp s)
  | Some vl ->
      (* Msg.debug (fun m ->
          m
            "Try to access elt number %d of map occ list for sort %a"
            i
            Name.pp
            s); *)
      assert (i - 1 < List.length vl);
      List.nth vl (i - 1)


(* IMPORTANT COMMENT!!! ALSO USED IN TEA!!!

Creates a formula ([quantifier] x : s,y :s | ev1[x] or ev2[y]) (NOTICE the *absence* of a leading
`always`, see `semantics_of_events` below). Also returns the list of variables bound by the said quantifier. 

This is a bit more than strictly necessary for the semantics, but it is also used for the abstract
semantics implemented by TEA. This is also why we don't add an `always` in front, here.
*)
let quantify_events quantifier events =
  let quantified_sorts = Ast.sort_bag_of_events events in
  (* maps each sort of an event argument to a list of fresh variables *)
  (* the map is used to generate each fresh variable only once *)
  let map_sort_fresh_vars =
    SortBag.fold quantified_sorts VarMap.empty (fun cur_map cur_i cur_s ->
        VarMap.add cur_s (create_vars_up_to_k cur_s cur_i) cur_map)
  in
  let fml_events =
    List.map
      (fun ev ->
        let newvars =
          find_fresh_vars_from_occ_list map_sort_fresh_vars
          @@ occ_list_from_sortlist (List.map sort_of_var ev.ev_args)
        in
        substitute_list ev.ev_args ~by:(List.map var newvars) ev.ev_body)
      events
  in
  let quantified_vars =
    List.flat_map snd (VarMap.to_list map_sort_fresh_vars)
  in
  (List.fold_right quantifier quantified_vars (disj fml_events), quantified_vars)


(* BEFORE MODIFYING: SEE COMMENT OF quantify_events ABOVE!!!*)
let semantics_of_events events = always @@ fst @@ quantify_events exists events

(* Puts the formula of the semantics of events (always some x,y | ev1[x] or ev2[y]) in axioms. *)
(* Puts the check formula (after nagating it) and the assuming formula in axioms. *)
(* Removes eventsn check body and check assuming. Does not handle modifies fields. *)
let convert { model; check } =
  let axiom_for_events = semantics_of_events model.events in
  let check_as_axiom = not_ check.chk_body in
  let updated_axioms =
    axiom_for_events :: check_as_axiom :: check.chk_assuming :: model.axioms
  in
  let updated_model =
    make_model
      ~sorts:model.sorts
      ~relations:model.relations
      ~constants:model.constants
      ~closures:model.closures
      ~axioms:updated_axioms
      ~events:[]
      ()
  in
  let updated_check = { check with chk_body = false_; chk_assuming = true_ } in
  make ~model:updated_model ~check:updated_check
