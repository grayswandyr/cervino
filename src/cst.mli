type ident = Symbol.t

type t =
  | Model of
      { module_ : module_ option
      ; opens : open_ list
      ; fields : field list
      ; sigs : signature list
      ; facts : fact list
      ; preds : pred list
      ; events : event list
      ; assertions : assertion list
      ; commands : command list
      } [@unboxed]

and module_ = Module of ident [@unboxed]

and open_ =
  | Open of
      { name : ident
      ; parameters : ident list
      ; alias : ident option
      } [@unboxed]

and field =
  | Field of
      { name : ident
      ; profile : profile
      ; is_var : bool
      } [@unboxed]

and profile =
  | Partial_function of ident * ident
  | Relation of ident list

(* non empty *)
and signature =
  | Sort of ident
  | One_sig of
      { name : ident
      ; parent : ident
      }
  | Set of
      { name : ident
      ; parent : ident
      ; is_var : bool
      }

and fact =
  | Fact of
      { name : ident option
      ; body : block
      } [@unboxed]

and pred =
  | Pred of
      { name : ident
      ; parameters : (ident * ident) list
      ; body : block
      } [@unboxed]

and event =
  | Event of
      { name : ident
      ; parameters : (ident * ident) list
      ; body : block
      } [@unboxed]

and assertion =
  | Assert of
      { name : ident
      ; body : block
      } [@unboxed]

and command =
  | Run of
      { name : ident
      ; scope : scope option
      }
  | Check of
      { name : ident
      ; scope : scope option
      }

and scope =
  | With_default of int * typescope list
  | Without_default of typescope list

(* non empty *)
and typescope =
  { exactly : bool
  ; number : int
  ; sort : ident
  }

and foltl = prim_foltl Location.located

and prim_foltl =
  | Compare_now of ident list * comparator * ident (* non empty term list *)
  | Compare_next of ident list * comparator * ident (* non empty term list *)
  | Unop of lunary * foltl
  | Binop of foltl * lbinary * foltl
  | If_then_else of foltl * foltl * foltl
  | Call of ident * ident list
  | Quant of quantifier * (ident list * ident) list * block
  | Block of block

and block = foltl list

and lunary =
  | Not
  | After
  | Eventually
  | Always

and lbinary =
  | And
  | Or
  | Implies
  | Iff

and quantifier =
  | Some_
  | All

and comparator =
  | In
  | Not_in
  | Eq
  | Not_eq

val print_quant : Format.formatter -> quantifier -> unit

val print_foltl : Format.formatter -> foltl -> unit

val print : Format.formatter -> t -> unit
