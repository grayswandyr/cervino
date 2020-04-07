
%token IMPLIES ELSE ALL SOME COLON EOF EQ ARROW PRIME AS OPEN
%token BAR AND OR IFF EVENTUALLY ALWAYS AFTER NOT ONE IN SIG 
%token LPAREN RPAREN LBRACE RBRACE LBRACKET RBRACKET COMMA VAR
%token PRED RUN CHECK ASSERT FACT BUT FOR EXACTLY SET MODULE LONE
%token <string> IDENT 
%token <string> EVENT_IDENT
%token <int> NUMBER

%nonassoc BAR
%left OR
%left IFF
%right IMPLIES ELSE
%left AND
%nonassoc NOT AFTER ALWAYS EVENTUALLY 


%start <Cst.t>parse

%{
  open Cst
  module M = Messages

  type constituent = 
    | CSig_and_fields of signature * field list
    | CFact of fact
    | CPred of pred
    | CEvent of event
    | CAssert of assertion
    | CCommand of command

  let make_model module_ opens (cs : constituent list) : t = 
    let rec walk (Model m as model) = function
      | [] -> model
      | c::cs ->
        let m' = match c with
          | CSig_and_fields (sig_, fs) ->
            Model { m with fields = fs @ m.fields; sigs = sig_ :: m.sigs }
          | CFact x -> Model { m with facts = x :: m.facts }
          | CPred x -> Model { m with preds = x :: m.preds }
          | CEvent x -> Model { m with events = x :: m.events }
          | CAssert x -> Model { m with assertions = x :: m.assertions }
          | CCommand x -> Model { m with commands = x :: m.commands }
        in 
        walk m' cs
    in 
    let model = 
      Model { 
        module_; 
        opens; 
        fields = [];
        sigs = [];
        facts = [];
        preds = [];
        events = [];
        assertions = [];
        commands = []
      }
    in 
    walk model cs
  
%}

%%

%public parse: 
  m = moduleDecl? os = open_* ps = paragraph+ EOF 
  { make_model m os ps }

moduleDecl:
  MODULE m = ident
  { Module m }  

open_:
  OPEN 
  name = ident 
  parameters = loption(brackets(comma_sep1(ident)))
  alias = preceded(AS, ident)?
  { Open { name; parameters; alias } }

paragraph:
  x = signature
  | x = predicate
  | x = fact
  | x = assertion
  | x = command
  { x }

signature:
  is_var = boption(VAR) 
  one = boption(ONE) 
  SIG 
  name = ident 
  in_ = preceded(IN, ident)? 
  fs = braces(comma_sep(field)) 
  {
    let sig_ = match is_var, one, in_ with
      | false, false, None -> 
          Sort name
      | _, _, None -> 
          M.fail "Variable and/or `one` toplevel signatures are unhandled."
      | false, true, Some parent -> 
          One_sig { name; parent }
      | _, _, Some parent ->
          Set { name; parent; is_var }
    in
    let make_field = function
    | `Partial_function_missing_domain (is_var, fname, cod) ->
      Field { name = fname; is_var; profile = Partial_function (name, cod)}
    | `Relation_missing_domain (is_var, fname, cod) ->
      Field { name = fname; is_var; profile = Relation (name :: cod)}
    in 
    let fs' = List.map make_field fs in 
    CSig_and_fields (sig_, fs')
  }

field: 
  var = boption(VAR) 
  name = ident 
  COLON 
  mult = set_or_lone
  cod = ident
  {
    match mult with
    | `Lone -> `Partial_function_missing_domain (var, name, cod)
    | `Set -> `Relation_missing_domain (var, name, [cod])
  }
  | 
  var = boption(VAR) 
  name = ident COLON 
  first_cod = ident ARROW
  other_cods = separated_nonempty_list(ARROW, ident)
  {
    `Relation_missing_domain (var, name, first_cod::other_cods)
  }

%inline set_or_lone :
  SET
  { `Set }
  | LONE
  { `Lone }

predicate:
  PRED 
  name = ident 
  parameters = loption(brackets(comma_sep(separated_pair(ident, COLON, ident)))) 
  body = block
  {
    CPred (Pred { name; parameters; body })
  }
  | PRED 
  name = EVENT_IDENT
  parameters = loption(brackets(comma_sep(separated_pair(ident, COLON, ident)))) 
  body = epr_block
  {
    CEvent (Event { name; parameters; body })
  }

fact:
  FACT name = ident? body = block
  { CFact (Fact { name; body }) }

assertion:
  ASSERT name = ident body = block
  { CAssert (Assert { name; body }) }

command:
  c_o_r = check_or_run 
  i_o_b = ident_or_block 
  scope = scope? 
  {
    match c_o_r, i_o_b with
    | `Check, `Ident name -> CCommand (Check (Named_command { name; scope }))
    | `Run, `Ident name -> CCommand (Run (Named_command { name; scope }))
    | `Check, `Block body -> CCommand (Check (Block_command { body; scope }))
    | `Run, `Block body -> CCommand (Run (Block_command { body; scope }))
  }

%inline check_or_run:
  CHECK 
  { `Check } 
  | RUN
  { `Run }  

%inline ident_or_block:
  id = ident 
  { `Ident id }
  | b = block
  { `Block b }

%inline scope:
  FOR num = NUMBER typescopes = loption(preceded(BUT, comma_sep1(typescope)))
  { With_default (num, typescopes) }
  | FOR typescopes = comma_sep1(typescope)
  { Without_default typescopes }

%inline typescope:
  exactly = iboption(EXACTLY) number = NUMBER sort = ident
  {
    { exactly; number; sort }
  }


%inline block:
  fs = braces(formula*)
  { fs }
  
formula:
  r = applied_relation
  { r }
  | f1 = formula op = lbinop f2 = formula 
	{ Binop (f1, op, f2) }
	| q = quant vars = comma_sep1(ident) COLON range = ident b = block_or_bar
  { multi_quant q vars range b }
	| f1 = formula IMPLIES f2 = formula ELSE f3 = formula 
  { If_then_else (f1, f2, f3) }
	| f1 = formula IMPLIES f2 = formula 
  { Binop (f1, Implies, f2) }
  | op = lunop f = formula 
  { Unop (op, f) }
  | p = ident args = brackets(comma_sep(ident)) 
  { Call (p, args) }
	| b = block
  { Block b }
	| f = parens(formula)
  { f }

epr_block: 
  b = braces(epr_formula*)
  { b }

epr_formula:
  ALL vars = comma_sep1(ident) COLON range = ident b = epr_or_bar
  { multi_quant All vars range b}
  | f1 = epr_formula AND f2 = epr_formula
  { Binop(f1, And, f2) }
  | f1 = epr_formula OR f2 = epr_formula
  { Binop(f1, Or, f2) }
  | f = parens(epr_formula)
  { f }
  | f = epr_basic
  { f }

epr_or_bar: 
  b = epr_block 
  { b }
  | BAR f = epr_formula  
  { [f] }

epr_basic:
  f = applied_relation 
  { f }
  | NOT f = epr_basic
  { Unop (Not, f) }

applied_relation:
  tuple = tuple comp = comparator rel = ident prime = boption(PRIME)
  {
    if prime then
      Compare_now (tuple, comp, rel)
    else
      Compare_next (tuple, comp, rel)
  }

tuple:
  t = separated_nonempty_list(ARROW, ident)
  | t = parens(tuple)
  { t }

%inline comparator:
  IN
  { In }
  | NOT IN
  { Not_in }
  | EQ
  { Eq }
  | NOT EQ
  { Not_eq }  
  
%inline quant:
	ALL
  { All }
	| SOME
  { Some_ }

%inline ident:
  id = IDENT
  { id }
  
%inline block_or_bar:
 	BAR f = formula
  { [f] }
	| b = block
  { b }

%inline lbinop:
	AND { And }
	| OR { Or }
	| IFF { Iff }

%inline lunop:
	EVENTUALLY { Eventually }
	| ALWAYS { Always }
	| NOT { Not }
	| AFTER { After }



    ////////////////////////////////////////////////////////////////////////
    // MENHIR MACROS
    ////////////////////////////////////////////////////////////////////////
      
%public %inline comma_sep(X) :
  xs = separated_list(COMMA, X)
    { xs }

      
%public %inline comma_sep1(X) :
  xs = separated_nonempty_list(COMMA, X)
    { xs }


    
%public %inline braces(X):
  x = delimited(LBRACE, X, RBRACE)
    { x }

    
%public %inline brackets(X):
  x = delimited(LBRACKET, X, RBRACKET)
    { x }

%public %inline parens(X):
  x = delimited(LPAREN, X, RPAREN)
    { x }


%public %inline iboption(X):
 (* empty *)
 { false }
 | X
 { true }

