open Ast
module SortBag = Name.Bag
module VarMap = Name.Map

let create_var s i =
  make_variable
    ~var_name:(Name.make_unloc ("_s" ^ Name.content s ^ string_of_int i))
    ~var_sort:s


let create_vars_up_to_k s k =
  assert (k > 0);
  let rec walk s k =
    if k = 1 then [ create_var s 1 ] else create_var s k :: walk s (k - 1)
  in
  List.rev @@ walk s k


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
      assert (i < List.length vl);
      List.nth vl i


(* Creates a formula (always [quantifier] x : s,y :s | ev1[x] or ev2[y]). Also returns the list of
variables bound by the said quantifier. 

This is a bit more than strictly necessary for the semantics, but it is also used for the abstract
semantics implemented by TEA.
*)
let quantify_events quantifier events =
  let sorts_exists_quantif = Ast.sort_bag_of_events events in
  (* maps each sort of an event argument to a list of fresh variables *)
  (* the map is used to generate each fresh variable only once *)
  let map_sort_fresh_vars =
    SortBag.fold sorts_exists_quantif VarMap.empty (fun cur_map cur_i cur_s ->
        VarMap.add cur_s (create_vars_up_to_k cur_s cur_i) cur_map)
  in
  let fml_events =
    List.map
      (fun ev ->
        let newvars =
          find_fresh_vars_from_occ_list map_sort_fresh_vars
          @@ occ_list_from_sortlist (List.map sort_of_var ev.ev_args)
        in
        substitute_list newvars ev.ev_args ev.ev_body)
      events
  in
  let vars_exists_quantif =
    List.flat_map snd (VarMap.to_list map_sort_fresh_vars)
  in
  ( always (List.fold_right quantifier vars_exists_quantif (disj fml_events)),
    vars_exists_quantif )


let semantics_of_events events = fst @@ quantify_events exists events

(* Put the formula of the semantics of events (always some x,y | ev1[x] or ev2[y]) in axioms. *)
(* Removes events. Does not handle modifies fields. *)
let cervino_semantics_model m =
  let updated_axioms = semantics_of_events m.events :: m.axioms in
  make_model
    ~sorts:m.sorts
    ~relations:m.relations
    ~constants:m.constants
    ~closures:m.closures
    ~axioms:updated_axioms
    ~events:[]
    ()


let convert m_with_check =
  Ast.make
    ~model:(cervino_semantics_model m_with_check.model)
    ~check:m_with_check.check
