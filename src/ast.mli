type sort = Name.t [@@deriving eq, ord, sexp_of]

type variable = private
  { var_name : Name.t;
    var_sort : sort
  }
[@@deriving make, eq, ord, sexp_of]

type constant = private
  { cst_name : Name.t;
    cst_sort : sort
  }
[@@deriving make, eq, ord, sexp_of]

type relation = private
  { rel_name : Name.t;
    rel_profile : sort list
  }
[@@deriving make, eq, ord, sexp_of]

type term = private
  | Var of variable
  | Cst of constant
[@@deriving eq, ord, sexp_of]

type literal = private
  | Pos_app of int * relation * term list (* int = number of X, is >= 0 *)
  | Neg_app of int * relation * term list (* int = number of X, is >= 0 *)
  | Eq of term * term
  | Not_eq of term * term
[@@deriving eq, ord, sexp_of]

type formula = private
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

type ev_modify = private
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

type transfo = private
  | TEA
  | TTC of relation * variable * variable list * formula
  | TFC of (Name.t -> formula option)
[@@deriving sexp_of]

type check =
  { chk_name : Name.t;
    chk_body : formula;
    chk_assuming : formula;
    chk_using : transfo option
  }
[@@deriving make, sexp_of]

type path = private
  { tc : relation;
    base : relation;
    between : relation option [@sexp.omit_nil]
  }
[@@deriving make, eq, ord, sexp_of]

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

val var : variable -> term

val cst : constant -> term

val sort_of_var : variable -> sort

val sort_of_cst : constant -> sort

val sort_of_term : term -> sort

val pos_app : int -> relation -> term list -> literal
(** pre: int >= 0 && |list| >= 0 *)

val neg_app : int -> relation -> term list -> literal
(** pre: int >= 0 && |list| >= 0 *)

val eq : term -> term -> literal

val neq : term -> term -> literal

val true_ : formula

val false_ : formula

val lit : literal -> formula

val not_ : formula -> formula

val and_ : formula -> formula -> formula

val or_ : formula -> formula -> formula

val all : ?folding_constants:constant list -> variable -> formula -> formula

val exists : ?folding_constants:constant list -> variable -> formula -> formula

val eventually : formula -> formula

val always : formula -> formula

val conj : formula list -> formula

val disj : formula list -> formula

val all_many : variable list -> formula -> formula
(** quantification maintains the order of variables *)

val exists_many : variable list -> formula -> formula
(** quantification maintains the order of variables *)

val implies : formula -> formula -> formula

val iff : formula -> formula -> formula

val ite : formula -> formula -> formula -> formula

val next : formula -> formula

val tea : transfo

val ttc : relation -> variable -> variable list -> formula -> transfo

val tfc : (Name.t -> formula option) -> transfo

val eq_term_list : term list -> term list -> formula

val neq_term_list : term list -> term list -> formula

val pp_formula : Format.formatter -> formula -> unit

val pp : Format.formatter -> t -> unit

val subst_in_term : variable list -> variable -> by:term -> term -> term

val substitute : variable -> by:term -> formula -> formula

val substitute_list : variable list -> by:term list -> formula -> formula

val sort_bag_of_event : event -> Name.Bag.t

val sort_bag_of_events : event list -> Name.Bag.t

val nb_next : formula -> bool * int option

val is_temporal : formula -> bool

val includes_exists : formula -> bool

module Electrum : sig
  val pp : t Fmt.t
  (** does not print the events and closures fields, they must have been handled by prior transformations  *)

  val pp_formula : Format.formatter -> formula -> unit
end

module Cervino : sig
  val pp : t Fmt.t
  (** does not print the events and closures fields, they must have been handled by prior transformations  *)

  val pp_formula : Format.formatter -> formula -> unit
end
