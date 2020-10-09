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
  | Pos_app of int * Name.t * term list (* int = number of X, is >= 0 *)
  | Neg_app of int * Name.t * term list (* int = number of X, is >= 0 *)
  | Eq of term * term
  | Not_eq of term * term
[@@deriving eq, ord, sexp_of]

type formula =
  | True
  | False
  | Lit of literal
  | And of formula * formula
  | Or of formula * formula
  | Ex of variable * formula
  | All of variable * formula
  | F of formula
  | G of formula
[@@deriving eq, ord, sexp_of]

type ev_modication = term list [@@deriving eq, ord, sexp_of]

type ev_modify =
  { mod_rel : relation;
    mod_mods : ev_modication list
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
  | TTC of relation * variable * formula
  | TFC of (event -> formula)
[@@deriving sexp_of]

type check =
  { chk_name : Name.t;
    chk_body : formula;
    chk_assuming : formula;
    chk_using : transfo
  }
[@@deriving make, sexp_of]

type path =
  { tc : relation;
    base : relation
  }
[@@deriving make, eq, ord, sexp_of]

type model =
  { sorts : sort list;
    relations : relation list; [@sexp.omit_nil]
    constants : constant list; [@sexp.omit_nil]
    axioms : formula list; [@sexp.omit_nil]
    events : event list;
    closures : path list [@sexp.omit_nil]
  }
[@@deriving make, sexp_of]

(* smart constructors *)
let var v = Var v

let cst c = Cst c

let pos_app nexts p args =
  assert (nexts >= 0);
  assert (List.length args >= 0);
  Pos_app (nexts, p, args)


let neg_app nexts p args =
  assert (nexts >= 0);
  assert (List.length args >= 0);
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
  | Ex (x, f) ->
      all_ x (not_ f)
  | All (x, f) ->
      ex_ x (not_ f)
  | F f ->
      g_ (not_ f)
  | G f ->
      f_ (not_ f)


and and_ f1 f2 = And (f1, f2)

and or_ f1 f2 = Or (f1, f2)

and all_ x f = All (x, f)

and ex_ x f = Ex (x, f)

and f_ f = F f

and g_ f = G f

let conjunction fs = List.fold_left and_ true_ fs

let disjunction fs = List.fold_left or_ false_ fs

let tea = TEA

let ttc rel var f = TTC (rel, var, f)

let tfc mapping = TFC mapping
