open Sexplib.Std

type ident = string Location.t [@@deriving eq, ord, sexp_of]

type call =
  { callee : ident;
    primed : bool; [@sexp.bool]
    args : ident list [@sexp.omit_nil] (* list may be empty *)
  }
[@@deriving make, eq, ord, sexp_of]

type formula = prim_formula Location.t

and prim_formula =
  | Call of call
  | Test of compop * ident * ident
  | Binary of binop * formula * formula
  | Unary of unop * formula
  | Ite of formula * formula * formula
  | Quant of quantifier * telescope * block (* non empty list *)
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
and ranging = ident list * ident

(* non empty list *)

(* list may be empty*)
and block = formula list [@@deriving eq, ord, sexp_of]

type sort = ident [@@deriving eq, ord, sexp_of]

type modification = ident list [@@deriving eq, ord, sexp_of]

type t =
  { sorts : sort list;
    relations : relation list;
    constants : constant list; [@sexp.omit_nil]
    closures : paths list; [@sexp.omit_nil]
    macros : macro list; [@sexp.omit_nil]
    axioms : axiom list; [@sexp.omit_nil]
    events : event list;
    checks : check list
  }

and relation =
  { r_name : ident;
    r_profile : ident list (* non empty list *)
  }

and constant =
  { c_name : ident;
    c_domain : ident
  }

and paths =
  { t_base : ident;
    (* name of the base relation *)
    t_tc : ident;
    (* name of the closure relation *)
    t_between : ident option [@sexp.omit_nil]
  }

and macro =
  { m_name : ident;
    m_args : ranging list; [@sexp.omit_nil] (*  may be empty *)
    m_body : block
  }

and axiom =
  { a_name : ident option; [@sexp.omit_nil]
    a_body : block
  }

and event =
  { e_name : ident;
    e_args : ranging list; [@sexp.omit_nil] (* may be emtpy *)
    e_modifies : modified_field list; [@sexp.omit_nil] (* may be empty *)
    e_body : block
  }

and modified_field =
  { mod_field : ident;
    mod_modifications : modification list (* may be empty *)
  }

(* non empty *)
and check =
  { check_name : ident;
    check_body : block;
    check_assuming : block; [@sexp.omit_nil]
    check_using : using
  }

and using =
  { u_name : ident;
    u_args : (ident * block) list (* may be empty *)
  }
[@@deriving eq, ord, make, sexp_of]

let empty =
  { sorts = [];
    relations = [];
    constants = [];
    closures = [];
    macros = [];
    axioms = [];
    events = [];
    checks = []
  }


let pp fmt model = Sexplib.Sexp.pp_hum fmt (sexp_of_t model)
