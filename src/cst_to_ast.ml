open Ast

let check idents ident =
  if List.mem ~eq:Ident.equal ident idents
  then ()
  else
    Msg.err
    @@ fun m ->
    m "Unknown identifier:@\n%a" Location.pp_location (Ident.positions ident)


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

  val get_variables : t -> subst

  val get_constants : t -> Cst.constant list

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


  let get_profile ({ relations; _ }, _) pred =
    match List.find_opt (fun p -> Ident.equal pred p.r_name) relations with
    | None ->
        assert false
    | Some p ->
        p.r_profile


  let get_variables (_, subst) = subst

  let get_constants ({ constants; _ }, _) = constants

  let push_variables (cst, subst) vars = (cst, List.rev vars @ subst)

  let check_relation env pred = check (get_relations env) pred

  let check_sort (cst, _) sort = check cst.sorts sort
end

let quantify q (x, s) b =
  let var_name = Name.of_ident x in
  let var_sort = Name.of_ident s in
  let var = make_variable ~var_name ~var_sort in
  match q with Cst.All -> all var b | Cst.Exists -> exists var b


(* converts [ ([x;y], s); ([w;z], t)] into [(x,s); (y,s); (w,t); (z,t)*)
let flatten_telescope (env : Env.t) (ts : Cst.telescope) : Env.subst =
  let open List.Infix in
  let* xs, s = ts in
  let* x = xs in
  Env.check_sort env s;
  List.return (x, s)


let rec walk_formula env (f : Cst.formula) =
  let pf = Location.content f in
  walk_prim_formula env pf


and walk_prim_formula env =
  let open Cst in
  function
  | False ->
      false_
  | True ->
      true_
  | Pred { pred; primed; args } ->
      Env.check_relation env pred;
      let profile = Env.get_profile env pred in
      let next = if primed then 1 else 0 in
      let args' = List.map2 (walk_term_sort env) args profile in
      lit (pos_app next (Name.of_ident pred) args')
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
      let ts' = flatten_telescope env ts in
      (* variables are pushed in reverse order (subst = stack) *)
      let env' = Env.push_variables env ts' in
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
          "Type error: %a (of type %a) is expected to have type %a"
          Location.pp_location
          (Ident.positions x)
          Ident.pp
          s1
          Ident.pp
          s2)


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
            "Not a variable or constant:@\n%a"
            Location.pp_location
            (Ident.positions t) )


and walk_term_sort env t sort =
  let s, term = walk_term env t in
  check_type t s sort;
  term


let check_existence msg ident idents todo =
  if List.mem ~eq:Ident.equal ident idents
  then todo ()
  else
    Msg.err (fun m ->
        m
          "%a is not a %s:@\n%a"
          Ident.pp
          ident
          msg
          Location.pp_location
          (Ident.positions ident))


let check_sort ident sorts todo = check_existence "sort" ident sorts todo

let convert_relation sorts Cst.{ r_name; r_profile } =
  let rel_profile =
    List.map
      (fun column -> check_sort column sorts @@ fun () -> Name.of_ident column)
      r_profile
  in
  make_relation ~rel_name:(Name.of_ident r_name) ~rel_profile ()


let convert_constant sorts Cst.{ c_name; c_domain } =
  check_sort c_domain sorts
  @@ fun () ->
  make_constant
    ~cst_name:(Name.of_ident c_name)
    ~cst_sort:(Name.of_ident c_domain)


(* TODO rewrite because now tc and between must be declared as relations, too *)
let convert_path (relations : relation list) Cst.{ t_tc; t_base; t_between } =
  match
    List.find_opt
      (fun r -> Name.equal r.rel_name (Name.of_ident t_base))
      relations
  with
  | None ->
      Msg.err (fun m ->
          m
            "%a is not a relation:@\n%a"
            Ident.pp
            t_base
            Location.pp_location
            (Ident.positions t_base))
  | Some ({ rel_profile; _ } as base) ->
    ( match rel_profile with
    | [ s1; s2 ] when Name.equal s1 s2 ->
        let tc = make_relation ~rel_name:(Name.of_ident t_tc) ~rel_profile () in
        let between =
          match t_between with
          | None ->
              None
          | Some btw ->
              (* TODO: handle between profile *)
              Some
                (make_relation ~rel_name:(Name.of_ident btw) ~rel_profile:[] ())
        in
        make_path ~tc ~base ?between ()
    | _ ->
        Msg.err (fun m ->
            m
              "%a is not a binary relation over one given sort:@\n%a"
              Ident.pp
              t_base
              Location.pp_location
              (Ident.positions t_base)) )


let convert_axiom env Cst.{ a_body; _ } = walk_block env a_body

(* let convert_event env Cst.{ e_name; e_args; e_modifies; e_body } = assert false *)
(* TODO *)
let convert_using _ _ = assert false

let convert_check env chk_id checks =
  match List.find_opt (fun c -> Ident.equal c.Cst.check_name chk_id) checks with
  | None ->
      Msg.err (fun m -> m "No check named: %a" Ident.pp chk_id)
  | Some Cst.{ check_body; check_assuming; check_using; _ } ->
      let chk_name = Name.of_ident chk_id in
      let chk_body = walk_block env check_body in
      let chk_assuming = walk_block env check_assuming in
      let chk_using = convert_using env check_using in
      make_check ~chk_name ~chk_body ~chk_assuming ~chk_using


(* TODO closures are relations too *)
let convert (cst : Cst.t) (check : string) =
  let map = List.map in
  let sorts = map Name.of_ident cst.sorts in
  let constants = map (convert_constant cst.sorts) cst.constants in
  let relations = map (convert_relation cst.sorts) cst.relations in
  let closures = map (convert_path relations) cst.closures in
  let env = Env.make cst in
  let axioms = map (convert_axiom env) cst.axioms in
  let check_id = Ident.of_string check in
  let check = convert_check env check_id cst.checks in
  (* TODO *)
  let events = [] in
  let model =
    make_model ~sorts ~relations ~constants ~closures ~axioms ~events ()
  in
  make ~model ~check
