open Sexplib.Std

type sort = Name.t [@@deriving eq, ord, sexp_of]

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
  | Eq of term * term
  | Not_eq of term * term
[@@deriving eq, ord, sexp_of]

type formula =
  | True
  | False
  | Lit of literal
  | And of formula * formula
  | Or of formula * formula
  | Exists of variable * formula
  | All of variable * formula
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
  | TTC of relation * variable * variable list * formula
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
    chk_using : transfo
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


let eq t1 t2 = Eq (t1, t2)

let neq t1 t2 = Not_eq (t1, t2)

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
  | Lit (Eq (t1, t2)) ->
      lit (neq t1 t2)
  | Lit (Not_eq (t1, t2)) ->
      lit (eq t1 t2)
  | And (f1, f2) ->
      or_ (not_ f1) (not_ f2)
  | Or (f1, f2) ->
      and_ (not_ f1) (not_ f2)
  | Exists (x, f) ->
      all x (not_ f)
  | All (x, f) ->
      exists x (not_ f)
  | F f ->
      always (not_ f)
  | G f ->
      eventually (not_ f)


and and_ f1 f2 = And (f1, f2)

and or_ f1 f2 = Or (f1, f2)

and all x f = All (x, f)

and exists x f = Exists (x, f)

and eventually f = F f

and always f = G f

let tea = TEA

let ttc rel var vars f = TTC (rel, var, vars, f)

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
  | Lit (Eq (t1, t2)) ->
      lit (eq t1 t2)
  | Lit (Not_eq (t1, t2)) ->
      lit (neq t1 t2)
  | And (f1, f2) ->
      and_ (next f1) (next f2)
  | Or (f1, f2) ->
      or_ (next f1) (next f2)
  | Exists (x, f) ->
      exists x (next f)
  | All (x, f) ->
      all x (next f)
  | F f ->
      eventually (next f)
  | G f ->
      always (next f)


let pp_formula fmt model = Sexplib.Sexp.pp_hum fmt (sexp_of_formula model)

let pp fmt model = Sexplib.Sexp.pp_hum fmt (sexp_of_t model)

let eq_term_list tl1 tl2 =
  conj (List.map2 (fun t1 t2 -> lit @@ eq t1 t2) tl1 tl2)


let neq_term_list tl1 tl2 =
  disj (List.map2 (fun t1 t2 -> lit @@ neq t1 t2) tl1 tl2)


let subst_in_term x y t =
  match t with Cst _ -> t | Var v -> if equal_variable x v then Var y else t


(* substitute variable x by variable y in fml*)
let rec substitute x ~by fml =
  match fml with
  | True ->
      true_
  | False ->
      false_
  | Lit (Pos_app (nexts, p, args)) ->
      let new_args = List.map (subst_in_term x by) args in
      lit (pos_app nexts p new_args)
  | Lit (Neg_app (nexts, p, args)) ->
      let new_args = List.map (subst_in_term x by) args in
      lit (neg_app nexts p new_args)
  | Lit (Eq (t1, t2)) ->
      lit (eq (subst_in_term x by t1) (subst_in_term x by t2))
  | Lit (Not_eq (t1, t2)) ->
      lit (neq (subst_in_term x by t1) (subst_in_term x by t2))
  | And (f1, f2) ->
      and_ (substitute x ~by f1) (substitute x ~by f2)
  | Or (f1, f2) ->
      or_ (substitute x ~by f1) (substitute x ~by f2)
  | Exists (varx, f) ->
      exists varx (substitute x ~by f)
  | All (varx, f) ->
      all varx (substitute x ~by f)
  | F f ->
      eventually (substitute x ~by f)
  | G f ->
      always (substitute x ~by f)


let substitute_list xlist ~by fml =
  assert (List.(length xlist = length by));
  assert (Mysc.List.all_different ~eq:equal_variable by);
  List.fold_left2
    (fun cur_fml varx vary -> substitute varx ~by:vary cur_fml)
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


module Electrum = struct
  open Fmt

  let _global = "_M"

  let _true fmt = string fmt "{}"

  let _false fmt = string fmt "!{}"

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
    | Lit (Eq (t1, t2)) ->
        pf fmt "%a = %a" pp_term t1 pp_term t2
    | Lit (Not_eq (t1, t2)) ->
        pf fmt "%a != %a" pp_term t1 pp_term t2
    | And (f1, f2) ->
        pf fmt "@[<1>(%a@ &&@ %a)@]" pp_formula f1 pp_formula f2
    | Or (f1, f2) ->
        pf fmt "@[<1>(%a@ ||@ %a)@]" pp_formula f1 pp_formula f2
    | Exists ({ var_name; var_sort }, f) ->
        pp_quantified fmt "some" var_name var_sort f
    | All ({ var_name; var_sort }, f) ->
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
      (vbox @@ list pp_constant)
      constants
      pp_relations
      relations
      (vbox @@ list pp_axiom)
      axioms


  and pp_sort fmt sort = pf fmt "sig %a {}" Name.pp sort

  and pp_constant fmt { cst_name; cst_sort } =
    pf fmt "one sig %a in %a {}" Name.pp cst_name Name.pp cst_sort


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
      "@[<h>var %a : %a,@]"
      Name.pp
      rel_name
      (list ~sep:(const string " -> ") Name.pp)
      rel_profile


  and pp_axiom fmt f = pf fmt "@[<hov2>fact {@ %a@ }@]" pp_formula f

  and pp_check fmt { chk_name; chk_assuming; chk_body; _ } =
    pf fmt "@[<hov2>fact /* assuming */ {@ %a@ @]}@\n" pp_formula chk_assuming;
    pf fmt "@[<hov2>check %a {@ %a@ @]}" Name.pp chk_name pp_formula chk_body
end
