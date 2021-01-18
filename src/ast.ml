open Sexplib.Std

type sort = Name.t [@@deriving eq, ord, sexp_of]

module SortMap = struct
  include Map.Make (struct
    type t = sort

    let compare = compare_sort
  end)

  let sexp_of_t _ _ = assert false
end

type scope = int SortMap.t [@@deriving eq, ord, sexp_of]

type variable =
  { var_name : Name.t;
    var_sort : sort
  }
[@@deriving make, eq, ord, sexp_of]

type constant =
  { cst_name : Name.t;
    cst_sort : sort
  }
[@@deriving make, eq, ord, sexp_of]

type relation =
  { rel_name : Name.t;
    rel_profile : sort list
  }
[@@deriving make, eq, ord, sexp_of]

type term =
  | Var of variable
  | Cst of constant
[@@deriving eq, ord, sexp_of]

type literal =
  | Pos_app of int * relation * term list (* int = number of X, is >= 0 *)
  | Neg_app of int * relation * term list (* int = number of X, is >= 0 *)
  | Eq of int * term * term (* int = number of X, is >= 0, also needed for = beacause of remove_equality *)
  | Not_eq of int * term * term (* int = number of X, is >= 0, also needed for = beacause of remove_equality *)
[@@deriving eq, ord, sexp_of]

type formula =
  | True
  | False
  | Lit of literal
  | And of formula * formula
  | Or of formula * formula
  | Exists of constant list option * variable * formula
  | All of constant list option * variable * formula
  | F of formula
  | G of formula
[@@deriving eq, ord, sexp_of]

type ev_modification = term list [@@deriving eq, ord, sexp_of]

type ev_modify =
  { mod_rel : relation;
    mod_mods : ev_modification list
  }
[@@deriving make, eq, ord, sexp_of]

type event =
  { ev_name : Name.t;
    ev_args : variable list; [@sexp.omit_nil]
    ev_body : formula;
    ev_modifies : ev_modify list [@sexp.omit_nil]
  }
[@@deriving make, eq, ord, sexp_of]

type transfo =
  | TEA
  | TTC of (relation * variable * variable list * formula) option
  | TFC of (Name.t -> formula option)
[@@deriving sexp_of]

type path =
  { tc : relation;
    base : relation;
    between : relation option [@sexp.omit_nil]
  }
[@@deriving make, eq, ord, sexp_of]

type check =
  { chk_name : Name.t;
    chk_body : formula;
    chk_assuming : formula;
    chk_bounds : (scope[@sexp.opaque]);
    chk_using : transfo option
  }
[@@deriving make, sexp_of]

type model =
  { sorts : sort list;
    relations : relation list; [@sexp.omit_nil]
    constants : constant list; [@sexp.omit_nil]
    closures : path list; [@sexp.omit_nil]
    axioms : formula list; [@sexp.omit_nil]
    events : event list
  }
[@@deriving make, sexp_of]

type t =
  { model : model;
    check : check
  }
[@@deriving make, sexp_of]

(* smart constructors *)
let var v = Var v

let cst c = Cst c

let sort_of_var { var_sort; _ } = var_sort

let sort_of_cst { cst_sort; _ } = cst_sort

let sort_of_term = function Var v -> sort_of_var v | Cst c -> sort_of_cst c

let name_of_term = function Var v -> v.var_name | Cst c -> c.cst_name

let pos_app nexts p args =
  assert (nexts >= 0);
  let ar = List.length p.rel_profile in
  assert (List.length args = ar);
  Pos_app (nexts, p, args)


let neg_app nexts p args =
  assert (nexts >= 0);
  let ar = List.length p.rel_profile in
  assert (List.length args = ar);
  Neg_app (nexts, p, args)


let eq i t1 t2 = Eq (i, t1, t2)

let neq i t1 t2 = Not_eq (i, t1, t2)

let rec true_ = True

and false_ = False

and lit l = Lit l

and not_ = function
  | True ->
      false_
  | False ->
      true_
  | Lit (Pos_app (nexts, p, args)) ->
      lit (neg_app nexts p args)
  | Lit (Neg_app (nexts, p, args)) ->
      lit (pos_app nexts p args)
  | Lit (Eq (nexts, t1, t2)) ->
      lit (neq nexts t1 t2)
  | Lit (Not_eq (nexts, t1, t2)) ->
      lit (eq nexts t1 t2)
  | And (f1, f2) ->
      or_ (not_ f1) (not_ f2)
  | Or (f1, f2) ->
      and_ (not_ f1) (not_ f2)
  | Exists (folding_csts, x, f) ->
      all ~folding_csts x (not_ f)
  | All (folding_csts, x, f) ->
      exists ~folding_csts x (not_ f)
  | F f ->
      always (not_ f)
  | G f ->
      eventually (not_ f)


and and_ f1 f2 = match (f1, f2) with True, f | f, True -> f | _ -> And (f1, f2)

and or_ f1 f2 = match (f1, f2) with False, f | f, False -> f | _ -> Or (f1, f2)

and eventually f = F f

and always f = G f

and all ?(folding_csts = None) x f = All (folding_csts, x, f)

and exists ?(folding_csts = None) x f = Exists (folding_csts, x, f)

let all_many ?(folding_csts = None) vars f =
  List.fold_right (all ~folding_csts) vars f


let exists_many ?(folding_csts = None) vars f =
  List.fold_right (exists ~folding_csts) vars f


let tea = TEA

let ttc_none = TTC None

let ttc_some rel var vars f = TTC (Some (rel, var, vars, f))

let tfc mapping = TFC mapping

let rec conj = function [] -> true_ | [ f ] -> f | f :: fs -> and_ f (conj fs)

let rec disj = function [] -> false_ | [ f ] -> f | f :: fs -> or_ f (disj fs)

let implies f1 f2 = or_ (not_ f1) f2

let iff f1 f2 = and_ (implies f1 f2) (implies f2 f1)

let ite c t e = and_ (implies c t) (implies (not_ c) e)

let rec next = function
  | True ->
      true_
  | False ->
      false_
  | Lit (Pos_app (nexts, p, args)) ->
      lit (pos_app (nexts + 1) p args)
  | Lit (Neg_app (nexts, p, args)) ->
      lit (neg_app (nexts + 1) p args)
  | Lit (Eq (nexts, t1, t2)) ->
      lit (eq (nexts + 1) t1 t2)
  | Lit (Not_eq (nexts, t1, t2)) ->
      lit (neq (nexts + 1) t1 t2)
  | And (f1, f2) ->
      and_ (next f1) (next f2)
  | Or (f1, f2) ->
      or_ (next f1) (next f2)
  | Exists (folding_csts, x, f) ->
      exists ~folding_csts x (next f)
  | All (folding_csts, x, f) ->
      all ~folding_csts x (next f)
  | F f ->
      eventually (next f)
  | G f ->
      always (next f)


let pp_formula fmt model = Sexplib.Sexp.pp_hum fmt (sexp_of_formula model)

let pp fmt model = Sexplib.Sexp.pp_hum fmt (sexp_of_t model)

let eq_term_list tl1 tl2 =
  conj (List.map2 (fun t1 t2 -> lit @@ eq 0 t1 t2) tl1 tl2)


let neq_term_list tl1 tl2 =
  disj (List.map2 (fun t1 t2 -> lit @@ neq 0 t1 t2) tl1 tl2)


let subst_in_term bound_vars x ~by t =
  if not @@ equal_sort x.var_sort (sort_of_term by)
  then
    Msg.err (fun m ->
        m
          "Try to substitute %a by %a whereas sorts are not the same."
          Name.pp
          x.var_name
          Name.pp
          (name_of_term by))
  else
    match t with
    | Cst _ ->
        t
    | Var v ->
        if equal_variable x v
           && (not @@ List.mem ~eq:equal_variable x bound_vars)
        then by
        else t


(* substitute variable x by variable y in fml*)
let substitute x ~by fml =
  (*Msg.debug (fun m ->
      m "Try to substitute %a by %a" Name.pp x.var_name Name.pp
        (name_of_term by));*)
  let rec subst_except_bound_vars bound_vars x ~by fml =
    match fml with
    | True ->
        true_
    | False ->
        false_
    | Lit (Pos_app (nexts, p, args)) ->
        let new_args = List.map (subst_in_term bound_vars x ~by) args in
        lit (pos_app nexts p new_args)
    | Lit (Neg_app (nexts, p, args)) ->
        let new_args = List.map (subst_in_term bound_vars x ~by) args in
        lit (neg_app nexts p new_args)
    | Lit (Eq (nexts, t1, t2)) ->
        lit
          (eq
             nexts
             (subst_in_term bound_vars x ~by t1)
             (subst_in_term bound_vars x ~by t2))
    | Lit (Not_eq (nexts, t1, t2)) ->
        lit
          (neq
             nexts
             (subst_in_term bound_vars x ~by t1)
             (subst_in_term bound_vars x ~by t2))
    | And (f1, f2) ->
        and_
          (subst_except_bound_vars bound_vars x ~by f1)
          (subst_except_bound_vars bound_vars x ~by f2)
    | Or (f1, f2) ->
        or_
          (subst_except_bound_vars bound_vars x ~by f1)
          (subst_except_bound_vars bound_vars x ~by f2)
    | Exists (folding_csts, varx, f) ->
        exists
          ~folding_csts
          varx
          (subst_except_bound_vars (varx :: bound_vars) x ~by f)
    | All (folding_csts, varx, f) ->
        all
          ~folding_csts
          varx
          (subst_except_bound_vars (varx :: bound_vars) x ~by f)
    | F f ->
        eventually (subst_except_bound_vars bound_vars x ~by f)
    | G f ->
        always (subst_except_bound_vars bound_vars x ~by f)
  in
  subst_except_bound_vars [] x ~by fml


let substitute_list xlist ~by fml =
  assert (List.(length xlist = length by));
  assert (Mysc.List.all_different ~eq:equal_term by);
  List.fold_left2
    (fun cur_fml varx termy -> substitute varx ~by:termy cur_fml)
    fml
    xlist
    by


let sort_bag_of_event { ev_args; _ } =
  Name.Bag.of_list @@ List.map sort_of_var ev_args


let sort_bag_of_events events =
  List.fold_left
    (fun cur_vars cur_ev ->
      let vars = sort_bag_of_event cur_ev in
      Name.Bag.meet vars cur_vars)
    Name.Bag.empty
    events


(* Returns (false, nb) if the formula is either not temporal or only refers to the instant in nb time steps. *)
(* Returns (true, _) otherwise. *)
let rec nb_next fml =
  match fml with
  | True | False ->
      (false, 0)
  | Lit (Pos_app (nexts, _, _)) ->
      (false, nexts)
  | Lit (Neg_app (nexts, _, _)) ->
      (false, nexts)
  | Lit (Eq (nexts, _, _)) ->
      (false, nexts)
  | Lit (Not_eq (nexts, _, _)) ->
      (false, nexts)
  | And (f1, f2) | Or (f1, f2) ->
      let is_tprl1, n1 = nb_next f1 in
      let is_tprl2, n2 = nb_next f2 in
      (is_tprl1 || is_tprl2 || (not @@ Int.equal n1 n2), n1)
  | Exists (_, _, f) | All (_, _, f) ->
      nb_next f
  | G _ | F _ ->
      (true, 0)


(* Returns true if the formula includes an eventually operator or a disjunction of formulas including either always or litterals not referring to the same exact instant. *)
(* Used to determine whether a universal quantifier is instantiate for this formula. *)
let rec is_temporal fml =
  match fml with
  | True | False | Lit _ ->
      false
  | And (f1, f2) ->
      is_temporal f1 || is_temporal f2
  | Or _ ->
      let is_tprl, _ = nb_next fml in
      is_tprl
  | Exists (_, _, f) | All (_, _, f) ->
      is_temporal f
  | G f ->
      is_temporal f
  | F _ ->
      true


let rec includes_exists fml =
  match fml with
  | True | False | Lit _ ->
      false
  | And (f1, f2) ->
      includes_exists f1 || includes_exists f2
  | Or (f1, f2) ->
      includes_exists f1 || includes_exists f2
  | Exists _ ->
      true
  | All (_, _, f) ->
      includes_exists f
  | G f | F f ->
      includes_exists f


(* Returns the number of existential quantifiers of variables of a given sort in a given formula.*)
let rec nb_exists s fml =
  match fml with
  | True | False | Lit _ ->
      0
  | And (f1, f2) | Or (f1, f2) ->
      if not (includes_exists f1 || includes_exists f2)
      then 0
      else nb_exists s f1 + nb_exists s f2
  | Exists (_, x, f) ->
      if equal_sort s (sort_of_var x) then 1 + nb_exists s f else nb_exists s f
  | All (_, _, f) ->
      if includes_exists f
      then
        failwith
          "Ast.nb_exists called for a formula having forall/exists nesting \
           quantifiers"
      else 0
  | G f | F f ->
      if includes_exists f
      then
        failwith
          "Ast.nb_exists called for a formula having G/exists of F/exists \
           nesting quantifiers"
      else 0


(* Computes the domain bound (for a given sort) due to existential quantifiers
 in the scope of a G operator. *)
let rec bound_computation_G_ex s fml =
  match fml with
  | True | False | Lit _ ->
      0
  | And (f1, f2) | Or (f1, f2) ->
      bound_computation_G_ex s f1 + bound_computation_G_ex s f2
  | Exists (_, x, f) ->
      let includes_dist_instants, _ = nb_next fml in
      if equal_sort s (sort_of_var x)
      then
        if includes_dist_instants
        then 2 + bound_computation_G_ex s f
        else 1 + bound_computation_G_ex s f
      else bound_computation_G_ex s f
  | All (_, _, f) ->
      if includes_exists f
      then
        failwith
          "Ast.bound_computation_G_ex is called for a formula having \
           forall/exists nesting in the scope of a G"
      else 0
  | G _ ->
      failwith
        "Ast.bound_computation_G_ex is called for a formula having 2 nested G \
         operators."
  | F _ ->
      failwith
        "Ast.bound_computation_G_ex is called for a formula having a G/F \
         nesting."


(* Computes the domain bound (obtained from existential quantifiers) for a given sort and a formula. *)
let rec bound_computation_ex s fml =
  match fml with
  | True | False | Lit _ ->
      0
  | And (f1, f2) | Or (f1, f2) ->
      bound_computation_ex s f1 + bound_computation_ex s f2
  | Exists _ ->
      nb_exists s fml
  | All (_, _, f) ->
      if includes_exists f
      then
        failwith
          "Ast.bound_computation_ex is called for a formula having \
           forall/exists nesting quantifiers"
      else 0
  | G f ->
      bound_computation_G_ex s f
  | F f ->
      if includes_exists f
      then
        failwith
          "Ast.bound_computation_ex is called for a formula having F/exists \
           nesting quantifiers"
      else 0


let nb_csts_of_sort s list_csts =
  List.fold_left
    (fun k cur_cst -> if equal_sort (sort_of_cst cur_cst) s then k + 1 else k)
    0
    list_csts


(* Computes the domain bound for a given sort due to both existential quantifiers in fml and to csts in list_csts *)
let bound_computation s list_csts fml =
  let result = nb_csts_of_sort s list_csts + bound_computation_ex s fml in
  if result = 0 then 1 else result


(* Computes the scope (a bound for every sort that is sufficiently large to
    make the verificaiton complete) and adds it to the ast *)
let compute_scope ast =
  let model = ast.model in
  let fml = conj model.axioms in
  let sorts = model.sorts in
  (*Bounds from existential quantifiers in axioms *)
  let bound_map =
    List.fold_left
      (fun cur_map cur_sort ->
        SortMap.add
          cur_sort
          (bound_computation cur_sort model.constants fml)
          cur_map)
      SortMap.empty
      sorts
  in
  let updated_chk = { ast.check with chk_bounds = bound_map } in
  { ast with check = updated_chk }


(* For some transformations (TFC, TTC), constants can be disjoint while they cannot for others
(TEA). The following functor pretty-prints to Electrum, with a constant pretty-printer as parameter
to account for this difference. *)
module MakeElectrum (Ppc : sig
  val pp_constant : constant Fmt.t
end) =
struct
  open Fmt

  let _global = "_M"

  let _true fmt = string fmt "({})"

  let _false fmt = string fmt "(!{})"

  let rec pp_formula fmt = function
    | True ->
        _true fmt
    | False ->
        _false fmt
    | Lit (Pos_app (nexts, p, args)) ->
        assert (nexts >= 0);
        pp_app fmt "in" p args nexts
    | Lit (Neg_app (nexts, p, args)) ->
        assert (nexts >= 0);
        pp_app fmt "!in" p args nexts
    | Lit (Eq (nexts, t1, t2)) ->
        assert (nexts >= 0);
        pf fmt "%a = %a" pp_term t1 pp_term t2
    | Lit (Not_eq (nexts, t1, t2)) ->
        assert (nexts >= 0);
        pf fmt "%a != %a" pp_term t1 pp_term t2
    | And (f1, f2) ->
        pf fmt "@[<1>(%a@ &&@ %a)@]" pp_formula f1 pp_formula f2
    | Or (f1, f2) ->
        pf fmt "@[<1>(%a@ ||@ %a)@]" pp_formula f1 pp_formula f2
    | Exists (_, { var_name; var_sort }, f) ->
        pp_quantified fmt "some" var_name var_sort f
    | All (_, { var_name; var_sort }, f) ->
        pp_quantified fmt "all" var_name var_sort f
    | F f ->
        pf fmt "@[<1>eventually@ %a@]" pp_formula f
    | G f ->
        pf fmt "@[<1>always@ %a@]" pp_formula f


  and pp_app fmt rel p args nexts =
    pf
      fmt
      "%a %s %a%s"
      pp_terms
      args
      rel
      pp_relation
      p
      (String.repeat "'" nexts)


  and pp_quantified fmt q x s f =
    pf fmt "(%s %a: %a |@ %a)" q Name.pp x Name.pp s pp_formula f


  and pp_relation fmt { rel_name; _ } = pf fmt "%s.%a" _global Name.pp rel_name

  and pp_terms fmt terms =
    pf fmt "%a" (list ~sep:(const string "->") pp_term) terms


  and pp_term fmt = function
    | Var { var_name = n; _ } | Cst { cst_name = n; _ } ->
        Name.pp fmt n


  let rec pp fmt { model; check } =
    pf fmt "@[<v>%a@,%a@]@." pp_model model pp_check check


  and pp_model fmt { sorts; relations; constants; axioms; _ } =
    pf
      fmt
      "@[<v>%a@,%a@,%a@,%a@]"
      (vbox @@ list pp_sort)
      sorts
      (vbox @@ list Ppc.pp_constant)
      constants
      pp_relations
      relations
      (vbox @@ list pp_axiom)
      axioms


  and pp_sort fmt sort = pf fmt "sig %a {}" Name.pp sort

  and pp_relations fmt relations =
    pf
      fmt
      "@[<v2>one sig %s {@ %a@]@,}"
      _global
      (list pp_relation_decl)
      relations


  and pp_relation_decl fmt { rel_name; rel_profile } =
    pf
      fmt
      "@[<h>var %a : %s%a,@]"
      Name.pp
      rel_name
      (if List.length rel_profile = 1 then "set " else "")
      (list ~sep:(const string " -> ") Name.pp)
      rel_profile


  and pp_axiom fmt f = pf fmt "@[<hov2>fact {@ %a@ }@]" pp_formula f

  and pp_check fmt { chk_name; chk_assuming; chk_body; chk_using; chk_bounds } =
    pf fmt "@[<hov2>fact /* assuming */ {@ %a@ @]}@\n" pp_formula chk_assuming;
    pf fmt "@[<hov2>check %a {@ %a@ @]}" Name.pp chk_name pp_formula chk_body;
    pf fmt "%a" pp_using chk_using;
    if not @@ SortMap.is_empty chk_bounds
    then pf fmt "@[<hov2> for %a @]" pp_scope (chk_bounds, chk_using)


  and pp_using fmt _ = pf fmt ""

  and pp_scope fmt (chk_bounds, chk_using) =
    let list_chk_bounds = SortMap.bindings chk_bounds in
    match chk_using with
    | Some (TFC _) | Some (TTC _) ->
        pf fmt "%a" (vbox @@ list ~sep:comma pp_bound_exactly) list_chk_bounds
    | _ ->
        pf fmt "%a" (vbox @@ list ~sep:comma pp_bound) list_chk_bounds


  and pp_bound fmt bound =
    match bound with s, i -> pf fmt "%a %a" pp_int i Name.pp s


  and pp_bound_exactly fmt bound =
    match bound with s, i -> pf fmt "exactly %a %a" pp_int i Name.pp s


  and pp_int fmt i = pf fmt "%d" i
end

module Electrum_one_sig_in = MakeElectrum (struct
  let pp_constant fmt { cst_name; cst_sort } =
    Fmt.pf fmt "one sig %a in %a {}" Name.pp cst_name Name.pp cst_sort
end)

module Electrum_one_sig_extends = MakeElectrum (struct
  let pp_constant fmt { cst_name; cst_sort } =
    Fmt.pf fmt "one sig %a extends %a {}" Name.pp cst_name Name.pp cst_sort
end)

let pp_electrum transfo fmt model =
  match transfo with
  | Some TEA ->
      Electrum_one_sig_in.pp fmt model
  | Some (TFC _) | Some (TTC _) | None ->
      Electrum_one_sig_extends.pp fmt model


module Cervino = struct
  open Fmt

  let _true fmt = string fmt "true"

  let _false fmt = string fmt "false"

  let comma = const string ","

  let rec pp_formula fmt = function
    | True ->
        _true fmt
    | False ->
        _false fmt
    | Lit (Pos_app (nexts, p, args)) ->
        assert (nexts >= 0);
        pp_app fmt true p args nexts
    | Lit (Neg_app (nexts, p, args)) ->
        assert (nexts >= 0);
        pp_app fmt false p args nexts
    | Lit (Eq (_, t1, t2)) ->
        pf fmt "%a = %a" pp_term t1 pp_term t2
    | Lit (Not_eq (_, t1, t2)) ->
        pf fmt "%a != %a" pp_term t1 pp_term t2
    | And (f1, f2) ->
        pf fmt "@[<1>(%a@ &&@ %a)@]" pp_formula f1 pp_formula f2
    | Or (f1, f2) ->
        pf fmt "@[<1>(%a@ ||@ %a)@]" pp_formula f1 pp_formula f2
    | Exists (_, { var_name; var_sort }, f) ->
        pp_quantified fmt "some" var_name var_sort f
    | All (_, { var_name; var_sort }, f) ->
        pp_quantified fmt "all" var_name var_sort f
    | F f ->
        pf fmt "@[<1>F@ %a@]" pp_formula f
    | G f ->
        pf fmt "@[<1>G@ %a@]" pp_formula f


  and pp_app fmt pos p args nexts =
    pf
      fmt
      "%s%a%s(%a)"
      (if pos then "" else "!")
      pp_relation
      p
      (String.repeat "'" nexts)
      pp_terms
      args


  and pp_quantified fmt q x s f =
    pf fmt "(%s %a: %a |@ %a)" q Name.pp x Name.pp s pp_formula f


  and pp_relation fmt { rel_name; _ } = pf fmt "%a" Name.pp rel_name

  and pp_terms fmt terms = pf fmt "%a" (list ~sep:comma pp_term) terms

  and pp_term fmt = function
    | Var { var_name = n; _ } | Cst { cst_name = n; _ } ->
        Name.pp fmt n


  let rec pp fmt { model; check } =
    pf fmt "@[<v>%a@,%a@]@." pp_model model pp_check check


  and pp_model fmt { sorts; relations; constants; axioms; _ } =
    pf
      fmt
      "@[<v>%a@,%a@,%a@,%a@]"
      (vbox @@ list pp_sort)
      sorts
      (vbox @@ list pp_constant)
      constants
      pp_relations
      relations
      (vbox @@ list pp_axiom)
      axioms


  and pp_sort fmt sort = pf fmt "sort %a" Name.pp sort

  and pp_constant fmt { cst_name; cst_sort } =
    pf fmt "constant %a in %a" Name.pp cst_name Name.pp cst_sort


  and pp_relations fmt relations =
    pf fmt "@[<v>%a@]" (list pp_relation_decl) relations


  and pp_relation_decl fmt { rel_name; rel_profile } =
    pf
      fmt
      "@[<h>relation %a in %a@]"
      Name.pp
      rel_name
      (list ~sep:(const string " * ") Name.pp)
      rel_profile


  and pp_axiom fmt f = pf fmt "@[<hov2>axiom {@ %a@ }@]" pp_formula f

  and pp_check fmt { chk_name; chk_assuming; chk_body; chk_using; _ } =
    pf
      fmt
      "@[<hov2>check %a {@ %a@ @]}@\n@[<hov2>assuming {@ %a@ @]} %a"
      Name.pp
      chk_name
      pp_formula
      chk_body
      pp_formula
      chk_assuming
      pp_using
      chk_using


  and pp_using fmt = function
    | None ->
        nop fmt ()
    | Some TEA ->
        pf fmt "using TEA"
    | Some (TTC _) ->
        pf fmt "using TTC[]"
    | Some (TFC _) ->
        pf fmt "using TFC[]"
end
