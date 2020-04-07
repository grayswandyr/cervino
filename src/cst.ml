
type ident = string
type t = Model of {
    module_ : module_ option;
    opens : open_ list;
    fields : field list;
    sigs : signature list;
    facts : fact list;
    preds : pred list;
    events : event list;
    assertions : assertion list;
    commands : command list;
  } [@unboxed]
and module_ = Module of ident
and open_ = Open of {
    name : ident;
    parameters : ident list;
    alias : ident option;
  }
and field = Field of {
    name : ident;
    profile : profile;
    is_var : bool;
  }
and profile =
  | Partial_function of ident * ident
  | Relation of ident list (* non empty *)
and signature =
  | Sort of ident
  | One_sig of {
      name : ident;
      parent : ident
    }
  | Set of {
      name : ident;
      parent : ident;
      is_var : bool;
    }
and fact = Fact of {
    name : ident option;
    body : block;
  }
and pred = Pred of {
    name : ident;
    parameters : (ident * ident) list;
    body : block;
  }
and event = Event of {
    name : ident;
    parameters : (ident * ident) list;
    body : block;
  }
and assertion = Assert of {
    name : ident;
    body : block;
  }
and command = 
  | Run of command_spec
  | Check of command_spec
and command_spec = 
  | Named_command of { name : ident; scope : scope option }
  | Block_command of { body : block; scope : scope option }
and scope =
  | With_default of int * typescope list
  | Without_default of typescope list (* non empty *)
and typescope = {
  exactly : bool;
  number : int;
  sort : ident
}     
and foltl =
  | Compare_now of ident list * comparator * ident (* non empty term list *)
  | Compare_next of ident list * comparator * ident (* non empty term list *)
  | Unop of lunary * foltl
  | Binop of foltl * lbinary * foltl
  | If_then_else of foltl * foltl * foltl
  | Call of ident * ident list 
  | Quant of quantifier * ident * ident * block (* non empty list *)
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

let multi_quant q vars range block =
  let f var fml = 
    [Quant (q, var, range, fml)]
  in
  Block (List.fold_right f vars block)