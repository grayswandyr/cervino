
%token IMPLIES ELSE ALL SOME COLON EOF EQ ARROW PRIME AS OPEN
%token BAR AND OR IFF EVENTUALLY ALWAYS AFTER NOT ONE IN SIG TRACE
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
    | CTrace_fact 
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
          | CTrace_fact -> 
              begin
                M.info "Found `_events` fact as expected, ignoring it.";
                model (* ignore this fact *)
              end
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
    if not @@ CCList.is_empty opens then
      M.warning "`open` statement(s) present in the model: it/they will be preserved but ignored otherwise.";
    walk model cs
  
  let loc x (l, c) = Location.(make_located x (Location.from_positions (l,c)))

  let pos loc = 
    Location.(string_of_position (from_positions loc))

  let negate_lit_or_test_pf = function 
    | Test (prime, id, Eq, id2) -> Test (prime, id, Not_eq, id2)
    | Test (prime, id, Not_eq, id2) -> Test (prime, id, Eq, id2)
    | Lit { name; args; positive = p; prime} -> 
        Lit { name; args; positive = not p; prime} 
    | _ -> assert false

  let negate_lit_or_test_f Location.{ data; _ } =
    Location.make_located (negate_lit_or_test_pf data) Location.dummy
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
  | x = trace_fact
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
    CEvent (Event { name = Symbol.make name; parameters; body })
  }

fact:
  FACT name = ident? body = block
  { CFact (Fact { name; body }) }

trace_fact:
  FACT TRACE block
  { CTrace_fact }

assertion:
  ASSERT name = ident body = block
  { CAssert (Assert { name; body }) }

command:
  c_o_r = check_or_run 
  name = ident 
  scope = scope? 
  {
    match c_o_r with
    | `Check -> CCommand (Check { name; scope })
    | `Run -> CCommand (Run { name; scope })
  }

%inline check_or_run:
  CHECK 
  { `Check } 
  | RUN
  { `Run }  


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
  f = prim_formula
  { loc f $loc(f) }    

prim_formula:
  r = test_or_literal
  { r }
  | f1 = formula op = lbinop f2 = formula 
	{ Binop (f1, op, f2) }
	| q = quant rangings = comma_sep1(quant_ranging) b = block_or_bar
  { Quant (q, rangings, b) }
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
	| f = parens(prim_formula)
  { f }

quant_ranging:
  vars = comma_sep1(ident) COLON range = ident
  { (vars, range) }

epr_block: 
  b = braces(epr_formula*)
  { b }

epr_formula:
  f = epr_prim_formula
  { loc f $loc(f) }

epr_prim_formula:
	| ALL rangings = comma_sep1(quant_ranging) b = epr_or_bar
  { Quant (All, rangings, b) }
  | f1 = epr_formula AND f2 = epr_formula
  { Binop(f1, And, f2) }
  | f1 = epr_formula OR f2 = epr_formula
  { Binop(f1, Or, f2) }
  | f1 = epr_basic IFF f2 = epr_basic
  { 
    let left = and_ f1 f2 in 
    let right = and_ (negate_lit_or_test_f f1) (negate_lit_or_test_f f2) in
    Binop (left, And, right)
  }
	| c = epr_basic IMPLIES t = epr_formula ELSE e = epr_formula 
  { 
    let left = or_ (negate_lit_or_test_f c) t in
    let right = or_ c e in
    Binop (left, And, right)
  }
	| f1 = epr_basic IMPLIES f2 = epr_formula 
  { Binop (negate_lit_or_test_f f1, Or, f2) }
  | f = parens(epr_prim_formula)
  { f }
  | f = epr_prim_basic
  { f }

epr_or_bar: 
  b = epr_block 
  { b }
  | BAR f = epr_formula  
  { [f] }

epr_basic:
  f = epr_prim_basic
  { loc f $loc(f)}

epr_prim_basic:
  | f = test_or_literal
  { f }
  | NOT f = epr_basic
  {  
    let Location.{ data; _ } = f in
    match data with
      | Lit ({ positive = p; _} as l) -> Lit { l with positive = not p }
      | Test (prime, id1, c, id2) ->
        let c' = match c with
          | Eq -> Not_eq
          | Not_eq -> Eq
        in
        Test (prime, id1, c', id2)
      | _ -> assert false
  }

test_or_literal:
  left = tuple lprime = boption(PRIME) 
  c = comparator 
  right = ident rprime = boption(PRIME)
  {
    if c = `In || c = `Not_in then
      (* literal *)
      if lprime then
        M.fail 
          Format.(sprintf "Cannot have `'` (prime) here: %s" 
                  (pos $loc(lprime)))
      else if c = `Eq || c = `Not_eq then
        M.fail Format.(sprintf "Cannot have `=` or `!=` here: %s" (pos $loc(c)))
      else 
        Lit { name = right; args = left; positive = (c = `In); prime = rprime }
    else 
      match lprime, rprime, c with
      | true, true, _ ->
        M.fail "Cannot have `'` (prime) on both sides of an equality"
      | false, true, `Test c -> Test (true, right, c, List.hd left)
      | _, false, `Test c -> Test (lprime, List.hd left, c, right) 
      | _, _, _ ->
        M.fail Format.(sprintf "Cannot have `in` or `not in` here: %s" (pos $loc(c)))
  }

tuple:
  t = separated_nonempty_list(ARROW, ident)
  | t = parens(tuple)
  { t }


%inline comparator: 
  IN 
  { `In }
  | NOT IN 
  { `Not_in }
  | EQ
  { `Test Eq }
  | NOT EQ
  { `Test Not_eq }  
  
%inline quant:
	ALL
  { All }
	| SOME
  { Some_ }

%inline ident:
  id = IDENT
  { Symbol.make id }
  
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

