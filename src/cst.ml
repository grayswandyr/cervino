type ident = string Location.t [@@deriving eq, ord, show { with_path = false }]

type call =
  { callee : ident
  ; args : ident list (* list may be empty *)
  ; primed : bool
  }
[@@deriving make, eq, ord, show { with_path = false }]

type formula = prim_formula Location.t

and prim_formula =
  | Call of call
  | Test of compop * ident * ident
  | Binary of binop * formula * formula
  | Unary of unop * formula
  | Ite of formula * formula * formula
  | Quant of quantifier * ranging list * block (* non empty list *)
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

(* non empty list *)
and ranging = ident list * ident

(* list may be empty*)
and block = formula list [@@deriving eq, ord, show { with_path = false }]

type sort = ident [@@deriving eq, ord, show { with_path = false }]

type modification = ident list [@@deriving eq, ord, show { with_path = false }]

type t =
  { sorts : sort list
  ; relations : relation list
  ; constants : constant list
  ; closures : paths list
  ; macros : macro list
  ; axioms : axiom list
  ; events : event list
  ; checks : check list
  }

and relation =
  { r_name : ident
  ; r_profile : ident list (* non empty list *)
  }

and constant =
  { c_name : ident
  ; c_domain : ident
  }

and paths =
  { t_base : ident (* name of the base relation *)
  ; t_tc : ident (* name of the closure relation *)
  ; t_between : ident option
  }

and macro =
  { m_name : ident
  ; m_args : ranging list (* list may be empty *)
  ; m_body : block
  }

and axiom =
  { a_name : ident option
  ; a_body : block
  }

and event =
  { e_name : ident
  ; e_args : ranging list (* may be emtpy *)
  ; e_modifies : modified_field list (* may be empty *)
  ; e_body : block
  }

and modified_field =
  { mod_field : ident
  ; mod_modifications : modification list (* non empty *)
  }

(* non empty *)
and check =
  { check_name : ident
  ; check_body : block
  ; check_assuming : block
  ; check_using : using
  }

and using =
  { u_name : ident
  ; u_args : (ident * block) list (* may be empty *)
  }
[@@deriving eq, ord, make, show { with_path = false }]

let empty =
  { sorts = []
  ; relations = []
  ; constants = []
  ; closures = []
  ; macros = []
  ; axioms = []
  ; events = []
  ; checks = []
  }
