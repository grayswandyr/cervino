open Sexplib.Std

type pred =
  { pred : Ident.t;
    primed : bool; [@sexp.bool]
    args : Ident.t list (* non empty *)
  }
[@@deriving make, eq, ord, sexp_of]

type sort = Ident.t [@@deriving eq, ord, sexp_of]

type formula = prim_formula Location.t

and prim_formula =
  | False
  | True
  | Pred of pred
  | Test of compop * Ident.t * Ident.t
  | Binary of binop * formula * formula
  | Unary of unop * formula
  | Ite of formula * formula * formula
  | Quant of quantifier * Ident.t list option * telescope * block
  | Block of block

and compop =
  | Eq
  | Neq

and binop =
  | And
  | Or
  | Iff
  | Implies

and unop =
  | Not
  | F
  | G
  | X

and quantifier =
  | All
  | Exists

and telescope = ranging list

(* non empty list *)

(* non empty list *)
and ranging = Ident.t list * sort

(* non empty list *)

(* list may be empty*)
and block = formula list [@@deriving eq, ord, sexp_of]

type transfo =
  | TEA
  | TFC of (Ident.t * block) list
  | TTC of (Ident.t * (Ident.t * sort) * telescope * block) option
[@@deriving eq, ord, sexp_of]

type modification = Ident.t list [@@deriving eq, ord, sexp_of]

type t =
  { sorts : sort list;
    relations : relation list;
    constants : constant list; [@sexp.omit_nil]
    closures : paths list; [@sexp.omit_nil]
    axioms : axiom list; [@sexp.omit_nil]
    events : event list;
    checks : check list
  }

and relation =
  { r_name : Ident.t;
    r_profile : Ident.t list (* non empty list *)
  }

and constant =
  { c_name : Ident.t;
    c_domain : Ident.t
  }

and paths =
  { t_base : Ident.t;
    (* name of the base relation *)
    t_tc : Ident.t;
    (* name of the closure relation *)
    t_between : Ident.t option [@sexp.omit_nil]
  }

and axiom =
  { a_name : Ident.t option; [@sexp.omit_nil]
    a_body : block
  }

and event =
  { e_name : Ident.t;
    e_args : telescope; [@sexp.omit_nil] (* may be emtpy *)
    e_modifies : modified_field list; [@sexp.omit_nil] (* may be empty *)
    e_body : block
  }

and modified_field =
  { mod_field : Ident.t;
    mod_modifications : modification list (* may be empty *)
  }

(* non empty *)
and check =
  { check_name : Ident.t;
    check_body : block;
    check_assuming : block; [@sexp.omit_nil]
    check_using : transfo option
  }
[@@deriving eq, ord, make, sexp_of]

let empty =
  { sorts = [];
    relations = [];
    constants = [];
    closures = [];
    axioms = [];
    events = [];
    checks = []
  }


let pp fmt model = Sexplib.Sexp.pp_hum fmt (sexp_of_t model)
