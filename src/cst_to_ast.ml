open Ast

let check idents ident =
  if List.mem ~eq:Ident.equal ident idents
  then ()
  else
    Msg.err
    @@ fun m ->
    m "Unknown identifier.@\n%a" Location.excerpt (Ident.positions ident)


(* 
- convert a Cst formula into an Ast one
- check at the same time that referenced identifiers have been declared
- convert Cst variable identifiers into Ast variables 
*)

module Env : sig
  type t

  type subst = (Ident.t * Ident.t) list

  val make : Cst.t -> t

  val get_relations : t -> Ident.t list

  val get_sorts : t -> Ident.t list

  val get_variables : t -> subst

  val get_constants : t -> Cst.constant list

  val get_events : t -> Cst.event list

  (* pre: seeked relation IS present *)
  val get_profile : t -> Ident.t -> Ident.t list

  val push_variables : t -> subst -> t

  val check_relation : t -> Ident.t -> unit

  val check_sort : t -> Ident.t -> unit
end = struct
  open Cst

  (* cst; list of pairs (var, sort) *)
  type t = Cst.t * (Ident.t * Ident.t) list

  type subst = (Ident.t * Ident.t) list

  let make cst = (cst, [])

  let get_relations ({ relations; _ }, _) =
    List.map (fun r -> r.r_name) relations


  let get_sorts ({ sorts; _ }, _) = sorts

  let get_events ({ events; _ }, _) = events

  let get_profile ({ relations; _ }, _) pred =
    match List.find_opt (fun p -> Ident.equal pred p.r_name) relations with
    | None ->
        assert false
    | Some p ->
        p.r_profile


  let get_variables (_, subst) = subst

  let get_constants ({ constants; _ }, _) = constants

  let push_variables (cst, subst) vars = (cst, vars @ subst)

  let check_relation env pred = check (get_relations env) pred

  let check_sort (cst, _) sort = check cst.sorts sort
end

let find_relation relations ident =
  List.find_opt (fun r -> Name.equal r.rel_name (Name.of_ident ident)) relations


let quantify q (x, s) b =
  let var_name = Name.of_ident x in
  let var_sort = Name.of_ident s in
  let var = make_variable ~var_name ~var_sort in
  match q with Cst.All -> all var b | Cst.Exists -> exists var b


(* converts [ ([x;y], s); ([w;z], t)] into (mind the reversal!):
[(z,t) (w,t) (y,s) (x,s)]*)
let flatten_telescope (env : Env.t) (ts : Cst.telescope) =
  let open List.Infix in
  let* xs, s = ts in
  let* x = xs in
  Env.check_sort env s;
  List.return (x, s)


let check_existence msg ident idents if_ok =
  if List.mem ~eq:Ident.equal ident idents
  then if_ok ()
  else
    Msg.err (fun m ->
        m
          "%a is not a %s:@\n%a"
          Ident.pp
          ident
          msg
          Location.excerpt
          (Ident.positions ident))


let check_sort ident sorts if_ok = check_existence "sort" ident sorts if_ok

let convert_relation sorts Cst.{ r_name; r_profile } =
  let rel_profile =
    List.map
      (fun column -> check_sort column sorts @@ fun () -> Name.of_ident column)
      r_profile
  in
  make_relation ~rel_name:(Name.of_ident r_name) ~rel_profile ()


let rec walk_formula env (f : Cst.formula) =
  let pf = Location.content f in
  walk_prim_formula env pf


and walk_prim_formula env (f : Cst.prim_formula) =
  match f with
  | False ->
      false_
  | True ->
      true_
  | Pred { pred; primed; args } ->
      Env.check_relation env pred;
      let profile = Env.get_profile env pred in
      let pred' =
        make_relation
          ~rel_name:(Name.of_ident pred)
          ~rel_profile:(List.map Name.of_ident profile)
          ()
      in
      let next = if primed then 1 else 0 in
      let args' = List.map2 (walk_term_sort env) args profile in
      lit (pos_app next pred' args')
  | Test (op, t1, t2) ->
      let s1, t1' = walk_term env t1 in
      let s2, t2' = walk_term env t2 in
      if Ident.equal s1 s2
      then
        let op' = match op with Neq -> neq | Eq -> eq in
        lit (op' t1' t2')
      else
        Msg.err (fun m ->
            m
              "Type error: %a has type %a while %a has type %a"
              Ident.pp
              t1
              Ident.pp
              s1
              Ident.pp
              t2
              Ident.pp
              s2)
  | Binary (op, f1, f2) ->
      let f1' = walk_formula env f1 in
      let f2' = walk_formula env f2 in
      let op' =
        match op with
        | And ->
            and_
        | Or ->
            or_
        | Iff ->
            iff
        | Implies ->
            implies
      in
      op' f1' f2'
  | Unary (op, f) ->
      let f' = walk_formula env f in
      let op' =
        match op with Not -> not_ | F -> eventually | G -> always | X -> next
      in
      op' f'
  | Ite (c, t, e) ->
      let c' = walk_formula env c in
      let t' = walk_formula env t in
      let e' = walk_formula env e in
      ite c' t' e'
  | Quant (_, [], _) ->
      assert false
  | Quant (q, ts, b) ->
      (* reverse to make stack-shaped substitution *)
      let ts' = flatten_telescope env ts in
      let env' = Env.push_variables env (List.rev ts') in
      let b' = walk_block env' b in
      List.fold_right (quantify q) ts' b'
  | Block b ->
      walk_block env b


and walk_block env b = conj (List.map (walk_formula env) b)

and check_type x s1 s2 =
  if Ident.equal s1 s2
  then ()
  else
    Msg.err (fun m ->
        m
          "Type error: %a (of type %a) is expected to have type %a@\n%a"
          Ident.pp
          x
          Ident.pp
          s1
          Ident.pp
          s2
          Location.excerpt
          (Ident.positions x))


and walk_term env t =
  let subst = Env.get_variables env in
  match List.find_opt (fun (v, _) -> Ident.equal v t) subst with
  | Some (x, s) ->
      let var_name = Name.of_ident x in
      let var_sort = Name.of_ident s in
      (s, var (make_variable ~var_name ~var_sort))
  | None ->
      let consts = Env.get_constants env in
      ( match List.find_opt (fun c -> Ident.equal c.Cst.c_name t) consts with
      | Some Cst.{ c_name; c_domain } ->
          let cst_name = Name.of_ident c_name in
          let cst_sort = Name.of_ident c_domain in
          (c_domain, cst (make_constant ~cst_name ~cst_sort))
      | None ->
          Msg.err
          @@ fun m ->
          m
            "Not a variable or constant: %a@\n%a"
            Ident.pp
            t
            Location.excerpt
            (Ident.positions t) )


and walk_term_sort env t sort =
  let s, term = walk_term env t in
  check_type t s sort;
  term


let convert_constant sorts Cst.{ c_name; c_domain } =
  check_sort c_domain sorts
  @@ fun () ->
  make_constant
    ~cst_name:(Name.of_ident c_name)
    ~cst_sort:(Name.of_ident c_domain)


let convert_path (relations : relation list) Cst.{ t_base; t_tc; t_between } =
  (* search base (Ast) relation *)
  match
    ( find_relation relations t_base,
      find_relation relations t_tc,
      Option.map (find_relation relations) t_between )
  with
  | None, _, _ ->
      Msg.err (fun m ->
          m
            "%a is not a relation:@\n%a"
            Ident.pp
            t_base
            Location.excerpt
            (Ident.positions t_base))
  | _, None, _ ->
      Msg.err (fun m ->
          m
            "%a is not a relation:@\n%a"
            Ident.pp
            t_tc
            Location.excerpt
            (Ident.positions t_tc))
  | _, _, Some None ->
      Msg.err (fun m ->
          m
            "%a is not a relation:@\n%a"
            (Option.pp Ident.pp)
            t_between
            (Option.pp Location.excerpt)
            (Option.map Ident.positions t_between))
  | ( Some ({ rel_profile = [ s1; s2 ]; _ } as base),
      Some ({ rel_profile = [ _; _ ] as tcp; _ } as tc),
      None )
    when Name.(equal s1 s2 && List.for_all (equal s1) tcp) ->
      make_path ~tc ~base ?between:None ()
  | ( Some ({ rel_profile = [ s1; s2 ]; _ } as base),
      Some ({ rel_profile = [ _; _ ] as tcp; _ } as tc),
      Some (Some ({ rel_profile = [ _; _; _ ] as btwp; _ } as between)) )
    when Name.(
           equal s1 s2
           && List.for_all (equal s1) tcp
           && List.for_all (equal s1) btwp) ->
      make_path ~tc ~base ~between ()
  | _ ->
      Msg.err (fun m ->
          m
            "Erroneous `paths` clause on %a: wrong typing for one of the \
             relations@\n\
             %a"
            Ident.pp
            t_base
            Location.excerpt
            (Ident.positions t_base))


let convert_axiom env Cst.{ a_body; _ } = walk_block env a_body

let convert_modifies env relations Cst.{ mod_field; mod_modifications } =
  match
    List.find_opt
      (fun r -> Name.equal (Name.of_ident mod_field) r.rel_name)
      relations
  with
  | None ->
      Msg.err (fun m ->
          m
            "Unknown relation in `modifies` clause: %a.@\n%a"
            Ident.pp
            mod_field
            Location.excerpt
            (Ident.positions mod_field))
  | Some mod_rel ->
      let open Mysc.List.Infix in
      let mod_mods =
        let profile = Env.get_profile env mod_field in
        let arity = List.length profile in
        let+ modif = mod_modifications in
        if List.length modif <> arity
        then
          Msg.err (fun m ->
              m
                "Wrong arity in `modifies` clause for %a (expected arity is \
                 %d).@\n\
                 %a"
                Ident.pp
                mod_field
                arity
                Location.excerpt
                ( fst @@ Ident.positions @@ List.hd modif,
                  snd @@ Ident.positions @@ List.hd @@ List.last 1 modif ))
        else
          (* let+/and+ provides a cartesian product while here we want a lock-step product (aka ziplist) *)
          let& t = modif
          and& s = profile in
          walk_term_sort env t s
      in
      make_ev_modify ~mod_rel ~mod_mods ()


let convert_event env relations Cst.{ e_name; e_args; e_modifies; e_body } =
  if not
     @@ Mysc.List.all_different
          ~eq:(fun f1 f2 -> Ident.equal f1.Cst.mod_field f2.Cst.mod_field)
          e_modifies
  then
    Msg.err (fun m ->
        m "Duplicates in `modifies` section of event %a" Ident.pp e_name)
  else
    let ev_name = Name.of_ident e_name in
    let flattened = flatten_telescope env e_args in
    let ev_args =
      List.map
        (fun (x, s) ->
          let var_name = Name.of_ident x in
          let var_sort = Name.of_ident s in
          make_variable ~var_name ~var_sort)
        flattened
    in
    (* args form a stack-shaped substitution => reverse *)
    let env' = Env.push_variables env (List.rev flattened) in
    (* handle modifies *)
    let ev_modifies = List.map (convert_modifies env' relations) e_modifies in
    (* handle body *)
    let ev_body = walk_block env' e_body in
    make_event ~ev_name ~ev_args ~ev_body ~ev_modifies ()


let convert_using env = function
  | Cst.TEA ->
      tea
  | Cst.TTC (rel_id, (x, s), ts, b) ->
      Env.check_relation env rel_id;
      let profile = Env.get_profile env rel_id in
      let rel =
        make_relation
          ~rel_name:(Name.of_ident rel_id)
          ~rel_profile:(List.map Name.of_ident profile)
          ()
      in
      let v =
        check_sort s (Env.get_sorts env)
        @@ fun () ->
        make_variable ~var_name:(Name.of_ident x) ~var_sort:(Name.of_ident s)
      in
      let ts' = flatten_telescope env ts in
      let vars =
        List.map
          (fun (x, s) ->
            make_variable
              ~var_name:(Name.of_ident x)
              ~var_sort:(Name.of_ident s))
          ts'
      in
      let env' = Env.push_variables env ((x, s) :: List.rev ts') in
      let f = walk_block env' b in
      ttc rel v vars f
  | Cst.TFC args ->
      assert (not @@ List.is_empty args);
      let open List.Infix in
      let events = Env.get_events env in
      if not
         @@ Mysc.List.all_different
              ~eq:(fun e1 e2 -> Ident.equal e1.Cst.e_name e2.Cst.e_name)
              events
      then Msg.err (fun m -> m "Non-unique event names in TFC parameters")
      else
        let assoc =
          let+ ev_id, ev_block = args in
          match
            List.find_opt (fun e -> Ident.equal ev_id e.Cst.e_name) events
          with
          | None ->
              Msg.err (fun m ->
                  m
                    "Unknown event: %a.@\n%a"
                    Ident.pp
                    ev_id
                    Location.excerpt
                    (Ident.positions ev_id))
          | Some Cst.{ e_args; _ } ->
              (* reverse to make stack-shaped substitution *)
              let subst = flatten_telescope env e_args |> List.rev in
              let env' = Env.push_variables env subst in
              let fml = walk_block env' ev_block in
              (Name.of_ident ev_id, fml)
        in
        tfc (fun event_name -> List.assoc_opt ~eq:Name.equal event_name assoc)


let convert_check env chk_id checks =
  match List.find_opt (fun c -> Ident.equal c.Cst.check_name chk_id) checks with
  | None ->
      Msg.err (fun m -> m "No check named %a" Ident.pp chk_id)
  | Some Cst.{ check_body; check_assuming; check_using; _ } ->
      let chk_name = Name.of_ident chk_id in
      let chk_body = walk_block env check_body in
      let chk_assuming = walk_block env check_assuming in
      match check_using with 
      | None -> make_check  ~chk_name ~chk_body ~chk_assuming ()
      | Some u -> 
        let chk_using = convert_using env u in
        make_check ~chk_name ~chk_body ~chk_assuming ~chk_using ()


let convert (cst : Cst.t) (check : string) =
  let map = List.map in
  let sorts = map Name.of_ident cst.sorts in
  let constants = map (convert_constant cst.sorts) cst.constants in
  let relations = map (convert_relation cst.sorts) cst.relations in
  let closures = map (convert_path relations) cst.closures in
  let env = Env.make cst in
  let axioms = map (convert_axiom env) cst.axioms in
  let events = map (convert_event env relations) cst.events in
  let check_id = Ident.of_string check in
  let check = convert_check env check_id cst.checks in
  let model =
    make_model ~sorts ~relations ~constants ~closures ~axioms ~events ()
  in
  make ~model ~check
