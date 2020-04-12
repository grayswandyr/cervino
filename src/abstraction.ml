open Containers
open Cst
module M = Messages
module AL = List.Assoc
module L = Location

(* For an event, tells the number of formal parameters for every sort in parameters.
   E.g. for: pred _e1[a:s, b:s, c:t, d:s, d:u] { ... }
   should return: [(u|->1), (t|->1), (s|->3)]
   (the order of pairs is unspecified)
*)
let sort_bag_of_event (Event { parameters; _ }) =
  let f = function None -> Some 1 | Some count -> Some (count + 1) in
  List.fold_left
    (fun acc (_, sort) -> AL.update ~eq:Symbol.equal ~f sort acc)
    []
    parameters
(* |> Fun.tap
   Format.(
    printf
      "%a@\n"
      ( within "[" "]"
        @@ list
        @@ pair ~sep:(const string "|->") Symbol.pp int )) *)


(* Computes the maximal number of variables needed for every sort in order to be able to call all events. *)
let sort_bag_of_events (Model { events; _ }) : (ident * int) list =
  (* take all lists for all events and group by sort *)
  let groups =
    List.flat_map sort_bag_of_event events
    (* |> Fun.tap
       Format.(
        printf
          "@\n%a@\n@\n"
          ( within "[" "]"
            @@ list
            @@ within "(" ")"
            @@ pair ~sep:(const string "|->") Symbol.pp int )) *)
    |> List.group_by
      ~hash:(fun (s, _) -> Symbol.hash s)
      ~eq:(fun (s1, _) (s2, _) -> Symbol.equal s1 s2)
      (* |> Fun.tap
         Format.(
          printf
            "%a@\n@\n"
            ( within "{" "}"
              @@ list
              @@ within "[" "]"
              @@ list
              @@ pair ~sep:(const string "|->") Symbol.pp int )) *)
  in
  (* for a sort, compute the maximum number of variables that will be needed *)
  let maximize = function
    | [] ->
      assert false
    | hd :: tl ->
      List.fold_left (fun (_, n_acc) (s, n) -> (s, Int.max n_acc n)) hd tl
  in
  (* apply to all sorts *)
  List.map maximize groups


type env_seed = (ident * (ident * ident)) list

(* for any sort and max number of variables, creates the said (fresh) variables and associated Ex predicate names, which is called a `env_seed` *)
let make_pred_env_seed sort_bag : env_seed =
  let fresh_var_and_ex =
    let c = ref ~-1 in
    fun (sort : Symbol.t) ->
      incr c;
      let s = string_of_int !c in
      (sort, (Symbol.make ("__y" ^ s), Symbol.make ("__E" ^ s)))
  in
  let fresh_vars_and_exs (sort, num) =
    List.init num (fun _ -> fresh_var_and_ex sort)
  in
  List.flat_map fresh_vars_and_exs sort_bag


(* 
  Returns for any event:
   - actual parameters to call it and their sort
   - an assoc-list that maps every formal parameter of the predicate to the adequate "E" predicate name
   - an assoc list that maps every sort to its "E" predicateS
*)
let env_for_event (env : env_seed) (Event { name; parameters; _ }) =
  let rec walk env acc_vars acc_par_ex acc_sort_ex = function
    | (v, s) :: ps ->
      let var, ex = AL.get_exn ~eq:Symbol.equal s env in
      let env' = AL.remove ~eq:Symbol.equal s env in
      walk env' 
        ((var, s) :: acc_vars) 
        ((v, ex) :: acc_par_ex) 
        ((s, ex) :: acc_sort_ex) 
        ps
    | [] ->
      (name, (List.rev acc_vars, List.rev acc_par_ex, acc_sort_ex))
  in
  walk env [] [] [] parameters
(* |> Fun.tap
   Format.(
    printf
      "@[%a@]@\n"
      ( pair 
          ~sep:(const string " ~~> ") 
          Symbol.pp
          (within "{" "}"
           @@ vbox
           @@ pair
             ( hbox 
               @@ within "[" "]"
               @@ list Symbol.pp )
             ( hbox 
               @@ within "[" "]"
               @@ list
               @@ within "(" ")"
               @@ pair Symbol.pp Symbol.pp )))) *)

(* Assoc list that maps to a pred name:
   - its actual parameters when it is called (and their sort)
   - an assoc list that maps its formal parameters to the adequate "E" predicate names
   - an assoc list that maps sorts to "E" predicates of the same sort
*)

type env = 
  (ident 
   * ((ident * ident) list 
      * (ident * ident) list
      * (ident * ident) list)) 
    list

let make_env (Model { events; _ } as model) : env = 
  let bag = sort_bag_of_events model in
  let seed = make_pred_env_seed bag in
  let env = List.map (env_for_event seed) events in 
  env

let make_ex exs i arg =
  let ex = List.assoc ~eq:Symbol.equal i exs in
  L.make_located (Compare_now (arg, In, ex)) L.dummy

let abstract_event (env : env) (Event ({ name; body; _} as e)) =
  let _, exs, _ = List.assoc ~eq:Symbol.equal name env in
  let _E = make_ex exs in 
  let rec walk_f L.{ data; _ } =
    walk_pf data
  and walk_pf f = match f with
    | Compare_now ([yi], Eq, yj) ->
      let left = implies (_E yi [yi]) (_E yj [yi]) in
      let right = implies (_E yj [yj]) (_E yi [yj]) in 
      and_ (left) (right)
    | Binop (p, And, q) -> and_ (walk_f p) (walk_f q)
    | If_then_else (_, _, _)
    | Quant (Some_, _, _)
    | Unop (_, _) -> M.fail "This connector should not appear in an event:"
    | _ -> assert false
  in 
  let body' = List.map walk_f body in 
  Event { e with body = body' }

let make_event_call (env : env) (Event { name; _}) : foltl =
  let actuals, _, _ = List.assoc ~eq:Symbol.equal name env in
  (* fst because actuals contains pairs (var, sort) *)
  L.make_located (Call (name, List.map fst actuals)) L.dummy

let add_all_prefix (env : env) (f : foltl) : foltl= 
  (* take list of sorted vars (with the same sort)
     and returns list of vars followed by the sort *)
  let fuse_sorted_vars svs = 
    let sort = match svs with
      | [] -> assert false
      | (_, sort)::_ -> sort
    in
    let vars = List.sort Symbol.compare @@ List.map fst svs in
    (vars, sort)
  in
  (* compute rangings by sort for the quantifier *)
  let rangings = 
    List.flat_map (fun (_, (sorted_vars, _, _)) -> sorted_vars) env 
    |> List.sort_uniq ~cmp:(Pair.compare Symbol.compare Symbol.compare)
    |> List.group_by 
      ~hash:Fun.(Symbol.hash % snd)
      ~eq:(fun (_,s1) (_,s2) -> Symbol.equal s1 s2)
    |> List.map fuse_sorted_vars
  in
  L.make_located (Quant (All, rangings, [f])) L.dummy


let make_axiom (env : env) = 
  let sorted_exs = 
    List.flat_map (fun (_, (_, _, sorted_exs)) -> sorted_exs) env 
    |> List.sort_uniq ~cmp:(Pair.compare Symbol.compare Symbol.compare)
  in
  let z1 = Symbol.make "__z1" in
  let z2 = Symbol.make "__z2" in 
  let make_all_fml (sort, ex) : foltl =
    let subf = 
      let ex1 = L.make_located (Compare_now ([z1], In, ex)) L.dummy in 
      let ex2 = L.make_located (Compare_now ([z2], In, ex)) L.dummy in
      let eq = L.make_located (Compare_now ([z1], Eq, z2)) L.dummy in
      implies (and_ ex1 ex2) eq
    in
    L.make_located (Quant (All, [ ([z1; z2], sort)], [subf])) L.dummy
  in
  let block = 
    L.make_located (Block (List.map make_all_fml sorted_exs)) L.dummy
  in 
  let g_block = L.make_located (Unop (Always, block)) L.dummy in
  Fact { name = None; body = [g_block] }


let abstract_model (Model ({ events; facts; _ } as m) as model) : Cst.t = 
  let env = make_env model in 
  let event_calls = match events with
    | [] -> M.fail "No event in the original model."
    | hd::tl ->
      List.fold_on_map
        ~f:(make_event_call env) 
        ~reduce:or_
        (make_event_call env hd)
        tl
  in
  let trace_formula = add_all_prefix env event_calls in 
  Model { 
    m with 
    events = List.map (abstract_event env) events;
    facts = 
      make_axiom env ::
      (Fact { name = None; body = [trace_formula] }) :: facts 
  }
