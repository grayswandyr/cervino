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
  assert (List.length args > 0);
  Pos_app (nexts, p, args)


let neg_app nexts p args =
  assert (nexts >= 0);
  assert (List.length args > 0);
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
      false_
  | False ->
      true_
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


let pp fmt model = Sexplib.Sexp.pp_hum fmt (sexp_of_t model)

let eq_term_list tl1 tl2 =
  conj (List.map2 (fun t1 t2 -> lit @@ eq t1 t2) tl1 tl2)


let neq_term_list tl1 tl2 =
  disj (List.map2 (fun t1 t2 -> lit @@ neq t1 t2) tl1 tl2)
