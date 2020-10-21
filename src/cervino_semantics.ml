open Ast
module SortBag = CCMultiSet.Make (Name)

module VarMap = CCMap.Make (struct
  type t = sort

  let compare = compare_sort
end)

let bag_of_list l =
  List.fold_left
    (fun cur_bag cur_sort -> SortBag.add cur_bag cur_sort)
    SortBag.empty l

let create_var s i =
  make_variable
    ~var_name:(Name.make_unloc ("_sem_ev" ^ Name.content s ^ string_of_int i))
    ~var_sort:s

let rec create_vars_up_to_k s k =
  match k with
  | 1 -> [ create_var s 1 ]
  | _ -> List.rev @@ (create_var s k :: create_vars_up_to_k s (k - 1))

let nb_occ list elt = List.count (fun x -> equal_sort (fst x) elt) list

let rec occurence_list_from_sortlist acc sortlist =
  match sortlist with
  | [] -> acc
  | hd :: tl ->
      let n = nb_occ acc hd in
      occurence_list_from_sortlist (List.rev ((hd, n + 1) :: acc)) tl

let occ_list_from_sortlist sortlist = occurence_list_from_sortlist [] sortlist

let find_fresh_vars_from_occ_list map occlist =
  List.map
    (fun (s, i) ->
      let vars = VarMap.get s map in
      match vars with
      | None ->
          failwith
            "in function Cervino_semantics.find_fresh_vars_from_occ_list : \
             sort not found"
      | Some vl -> List.nth vl i)
    occlist

let semantics_of_events m =
  let sorts_exists_quantif =
    List.fold_left
      (fun cur_vars cur_ev ->
        let vars = SortBag.of_list @@ List.map sort_of_var cur_ev.ev_args in
        SortBag.meet vars cur_vars)
      SortBag.empty m.events
  in
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
      m.events
  in
  let vars_exists_quantif =
    List.flatten @@ List.map snd (VarMap.to_list map_sort_fresh_vars)
  in
  always
    (List.fold_right
       (fun cur_var cur_fml -> exists cur_var cur_fml)
       vars_exists_quantif (disj fml_events))

(* Put the formula of the semanctics of events (always some x,y | ev1[x] or ev2[y]) in axioms. *)
(* Removes events. Does not handle modifies fields. *)
let cervino_semantics_model m =
  let updated_axioms = semantics_of_events m :: m.axioms in
  make_model ~sorts:m.sorts ~relations:m.relations ~constants:m.constants
    ~closures:m.closures ~axioms:updated_axioms ~events:[] ()

let cervino_semantics_ast m_with_check =
  Ast.make
    ~model:(cervino_semantics_model m_with_check.model)
    ~check:m_with_check.check
