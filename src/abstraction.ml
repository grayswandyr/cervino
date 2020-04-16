open Containers
open Cst
module M = Messages
module AL = List.Assoc
module L = Location


let loc x = L.(make_located x dummy)

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
    let c = ref 0 in
    fun (sort : Symbol.t) ->
      incr c;
      let s = string_of_int !c in
      (sort, (Symbol.make ("__y" ^ s), Symbol.make ("__E" ^ s)))
  in
  let fresh_vars_and_exs (sort, num) =
    List.init num (fun _ -> fresh_var_and_ex sort)
  in
  List.flat_map fresh_vars_and_exs sort_bag

(* !!! supposes unicity of keys (= predicate names) *)
module Env : sig
  type ident_map = (ident, ident) AL.t

  (* ident: predicate name *)
  type t = (ident, info) AL.t

  and info = private {
    (* actual parameter |-> sort *)
    actuals_and_sorts: ident_map;
    (* formal parameter |-> "E" relation *)
    formals_and_exs: ident_map;
    (* sort |-> "E" relation *)
    sorts_and_exs: ident_map
  }

  val make_info : ident_map -> ident_map -> ident_map -> info
  val empty : t
  val add_info : ident -> info -> t -> t 

  val get_exn : ident -> t -> info

  val mem_ident_map : ident -> ident_map -> bool
end = struct
  type ident_map = (ident, ident) AL.t

  type t = (ident, info) AL.t
  and info = {
    actuals_and_sorts: ident_map;
    formals_and_exs: ident_map;
    sorts_and_exs: ident_map
  }

  let make_info actuals_and_sorts formals_and_exs sorts_and_exs = {
    actuals_and_sorts;
    formals_and_exs;
    sorts_and_exs
  }

  let empty = []

  let add_info id info env = 
    (id, info) :: env

  let get_exn id env = AL.get_exn ~eq:Symbol.equal id env

  let mem_ident_map id map = AL.mem ~eq:Symbol.equal id map
end

type env = Env.t 

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
      let acc_vars = List.rev acc_vars in
      let acc_par_ex = List.rev acc_par_ex in 
      let info = Env.make_info acc_vars acc_par_ex acc_sort_ex in
      (name, info)
  in
  walk env [] [] [] parameters

let make_env (Model { events; _ } as model) : env = 
  let bag = sort_bag_of_events model in
  let seed = make_pred_env_seed bag in
  let add env e = 
    let (name, info) = env_for_event seed e in
    Env.add_info name info env 
  in
  List.fold_left add Env.empty events



(* replaced: list (used as a set) of predicates called (possibly recusively by the event and therefore abstracted too) (= poor man' writer monad) *)
let abstract_event (Model m) (env : env) (replaced : pred list ref) (Event ({ name; body; _} as e)) =
  let Env.{ formals_and_exs; _ } = Env.get_exn name env in
  (* "E" predicate for variable "var" *)
  let _E var arg =
    let name = List.assoc ~eq:Symbol.equal var formals_and_exs in
    Lit { positive = true; prime = false; name; args = [arg] }
  in
  let prim_implies p q = Binop (p, Implies, q) in 
  let prim_and p q = Binop (p, And, q) in 
  let prim_or p q = Binop (p, Or, q) in 
  let rec walk_f pol L.{ data; _ } =
    loc (walk_pf pol data) 
  and walk_pf pol f = match f with
    | Unop (Not, { data = p; _ }) -> walk_pf (not pol) p
    | Quant (Some_, _, _) -> 
      M.fail "An existential quantifier should not appear in an event"
    | Unop ((After | Eventually | Always), _)-> 
      M.fail "A temporal connective should not appear in an event" 
    | Test (left, Eq, right) when not pol ->
      walk_pf true (Test (left, Not_eq, right))
    | Test (left, Eq, right) ->
      if Env.mem_ident_map left formals_and_exs 
      && Env.mem_ident_map right formals_and_exs 
      then
        prim_and 
          (implies (loc @@ _E left left) (loc @@ _E right left))
          (implies (loc @@ _E right right) (loc @@ _E left right))
      else if Env.mem_ident_map left formals_and_exs then
        _E left right
      else if Env.mem_ident_map right formals_and_exs then
        _E right left
      else f
    | Test (left, Not_eq, right) when not pol ->
      walk_pf true (Test (left, Eq, right))
    | Test (left, Not_eq, right) ->
      Unop (Not, walk_f true (loc @@ Test (left, Eq, right)))
    | Lit ({ positive; _ } as l) when not pol -> 
      walk_pf true (Lit { l with positive = not positive })
    | Lit { args; positive; _ } -> 
      (* get the ys that appear as free variables in args *)
      let ys = List.fold_left 
          (fun acc arg -> 
             if Env.mem_ident_map arg formals_and_exs 
             then arg :: acc else acc) [] args 
      in
      (match ys with
       | [] -> f
       | _ -> 
         let conj = loc @@ Block (List.map (fun y -> loc @@ _E y y) ys) in
         if positive then
           prim_implies conj (loc f)
         else 
           prim_and conj (loc @@ Unop (Not, loc f)))
    | Binop (p, And, q) -> 
      if pol then prim_and (walk_f pol p) (walk_f pol q)
      else prim_or (walk_f false p) (walk_f false q)
    | Binop (p, Or, q) ->
      if pol then prim_or (walk_f pol p) (walk_f pol q)
      else prim_and (walk_f false p) (walk_f false q)
    | Block b -> 
      if pol then Block (List.map (walk_f pol) b)
      else 
        (match b with
         | [] -> Unop (Not, loc @@ Block []) (* encoding false *)
         | hd::tl -> 
           (List.fold_left (fun acc fml -> or_ acc fml) hd tl).data )
    | Quant (All, _, _) when not pol -> 
      M.fail "A universal quantifier should not appear in negative position in an event"
    | Quant (All, rangings, b) -> 
      Quant (All, rangings, List.map (walk_f pol) b)
    | Binop (p, Implies, q) -> 
      walk_pf pol @@ prim_or (not_ p) q
    | Binop (p, Iff, q) -> 
      walk_pf pol @@ prim_and (implies p q) (implies q p)
    | If_then_else (p ,q, r) -> 
      walk_pf pol @@ prim_and (implies p q) (implies (not_ p) r)
    | Call (p, _) -> 
      (if 
        not 
        @@ List.exists (fun (Pred { name; _ }) -> Symbol.equal name p) !replaced 
       then
         match
           List.find_opt 
             (fun (Pred { name; _ }) -> Symbol.equal name p) 
             m.preds
         with
         | None -> 
           M.fail 
             Format.(sprintf "Cannot find definition of predicate `%a`" 
                       Symbol.pp p)
         | Some (Pred { name; parameters; body }) ->
           (* as we expect valid Electrum, we suppose no recursion between preds *)
           let body = List.map (walk_f pol) body in
           replaced := List.add_nodup 
               ~eq:(fun (Pred { name = n1; _ }) (Pred { name = n2; _ }) 
                     -> Symbol.equal n1 n2) 
               (Pred { name; parameters; body })
               !replaced
      );
      f
  in 
  let body' = List.map (walk_f true) body in 
  Event { e with body = body' }

let make_event_call (env : env) (Event { name; _}) : foltl =
  let Env.{ actuals_and_sorts; _ } = Env.get_exn name env in
  (* fst because actuals contains pairs (var, sort) *)
  loc (Call (name, List.map fst actuals_and_sorts)) 

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
    List.flat_map 
      (fun (_, Env.{ actuals_and_sorts; _ }) -> actuals_and_sorts) env 
    |> List.sort_uniq ~cmp:(Pair.compare Symbol.compare Symbol.compare)
    |> List.group_by 
      ~hash:Fun.(Symbol.hash % snd)
      ~eq:(fun (_,s1) (_,s2) -> Symbol.equal s1 s2)
    |> List.map fuse_sorted_vars
  in
  loc (Quant (All, rangings, [f])) 


let make_axiom (env : env) = 
  let sorted_exs = 
    List.flat_map (fun (_, Env.{ sorts_and_exs; _ }) -> sorts_and_exs) env 
    |> List.sort_uniq ~cmp:(Pair.compare Symbol.compare Symbol.compare)
  in
  let z1 = Symbol.make "__z1" in
  let z2 = Symbol.make "__z2" in 
  let make_all_fml (sort, ex) : foltl =
    let subf = 
      let ex1 = lit ~positive:true ~prime:false ex [z1] in
      let ex2 = lit ~positive:true ~prime:false ex [z2] in
      let eq = test z1 Eq z2 in
      implies (and_ ex1 ex2) eq
    in
    loc (Quant (All, [ ([z1; z2], sort)], [subf])) 
  in
  let block = 
    loc (Block (List.map make_all_fml sorted_exs)) 
  in 
  let g_block = loc (Unop (Always, block)) in
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
  (* keeps track of updated predicates (recursively called by event abstraction ) *)
  let replaced = ref [] in
  let events = List.map (abstract_event model env replaced) events in
  (* update preds with the changed ones (during event abstraction) *)
  let update ((Pred { name; _ }) as p) = 
    match 
      List.find_opt 
        (fun (Pred { name = n; _}) -> Symbol.equal name n)
        !replaced 
    with 
    | None -> p
    | Some p' -> p' 
  in
  Model { 
    m with 
    events;
    preds = List.map update m.preds;
    facts = 
      make_axiom env ::
      (Fact { name = None; body = [trace_formula] }) :: facts 
  }
