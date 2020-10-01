
%token ASSUMING PATHS AT SORT RELATION USING AXIOM CONSTANT EVENT
%token MODIFIES NEQ ELSE IMPLIES
%token ALL SOME COLON EOF EQ PRIME CART
%token BAR AND OR IFF EVENTUALLY ALWAYS AFTER NOT IN 
%token LPAREN RPAREN LBRACE RBRACE LBRACKET RBRACKET COMMA 
%token CHECK 
%token <string> IDENT 

%nonassoc BAR
%left OR
%left IFF
%right IMPLIES ELSE 
%left AND
%nonassoc NOT AFTER ALWAYS EVENTUALLY 


%start <Cst.t>parse

%{
 
  open Cst

  module L = Location

(* Dispatches the paragraphs (read in arbitrary order) into a CST. *)
(* Also checks that the name (of a paragraph to dispatch) has not already
   been used in another declaration or definition. *)
(* - p: accumulator containing the currently dispatched paragraphs *)
(* - paragraphs: remaining paragraphs to diasptch in p's fields *)
let rec dispatch_aux p (names: Ident.t list) paragraphs = match paragraphs with
| [] -> p
| hd::tl ->
    let p', new_names = match hd with 
      | `Sort x -> 
        ({ p with sorts = x :: p.sorts }, [x])
      | `Relation x -> 
        ({ p with relations = x :: p.relations }, [x.r_name])
      | `Constant x -> 
        ({ p with constants = x :: p.constants }, [x.c_name])
      | `Transclos x -> 
        ({ p with closures = x :: p.closures }, x.t_tc :: Option.to_list x.t_between)      
      | `Event x -> 
        ({ p with events = x :: p.events }, [x.e_name])
      | `Axiom x -> 
        ({ p with axioms = x :: p.axioms }, Option.to_list x.a_name)
      | `Check x -> 
        ({ p with checks = x :: p.checks }, [x.check_name])
    in 
    (* check if there are common idents in new_names and names *)
    let common = 
      let open List.Infix in
      (* we define a list by comprehension: *)
      (* for any nn in new_names... *)
      let* nn = new_names in (* start by new_names as it's the shortest list *)
      (* for any n in names... *)
      let* n = names in
      (* such that name(nn) = name(n) *)
      if L.equal_content String.equal nn n then 
        (* return their respective positions *)
        [ L.positions n; L.positions nn ] 
      else 
        (* or ignore these ones and loop to the next ones *)
        []
    in
    if List.is_empty common then
      dispatch_aux p' (new_names @ names) tl
    else
      Msg.err (fun m -> 
        m "Same name(s) used in multiple paragraphs:@\n%a" 
          (List.pp L.pp_location) common)

let dispatch ps = dispatch_aux Cst.empty [] ps
%}

%%

%public parse: 
  ps = paragraph+ EOF 
  { dispatch ps }

%inline ident:
  id = IDENT 
  { Ident.make id $loc(id) } 

%inline ranging: 
  ids = comma_sep1(ident) COLON sort = ident 
  { (ids, sort) }

paragraph:
  x = sort
  { `Sort x }
  | x = relation
  { `Relation x }
  | x = constant 
  { `Constant x }
  | x = paths
  { `Transclos x }
  | x = axiom
  { `Axiom x }
  | x = event
  { `Event x }
  | x = check
  { `Check x }

sort: 
  SORT name = ident 
  { name }

relation: 
  RELATION r_name = ident IN r_profile = separated_nonempty_list(CART, ident) 
  { make_relation ~r_name ~r_profile () }

constant: 
  CONSTANT c_name = ident IN c_domain = ident 
  { make_constant ~c_name ~c_domain }

paths: 
  PATHS pair = brackets(pair_or_triple) 
  { let (t_base, t_tc, t_between) = pair in 
    make_paths ~t_base ~t_tc ?t_between () }

%inline pair_or_triple: 
  t_base = ident COMMA t_tc = ident btw_name = preceded(COMMA, ident)?
  { (t_base, t_tc, btw_name) }

axiom: 
  AXIOM a_name = ident? a_body = block 
  { make_axiom ?a_name ~a_body () } 

event: 
  EVENT e_name = ident e_args = loption(brackets(comma_sep(ranging)))
  e_modifies = loption(preceded(MODIFIES, comma_sep1(modified_field))) e_body = block 
  { make_event ~e_name ~e_args ~e_modifies ~e_body () }

modified_field: 
  mod_field = ident mod_modifications = loption(preceded(AT, braces(comma_sep1(modification)) ))
  { make_modified_field ~mod_field ~mod_modifications () }

%inline modification: 
  id = ident 
  { [id] } 
  | ids = parens(comma_sep1(ident)) 
  { ids }

check: 
  CHECK check_name = ident check_body = block 
  check_assuming = loption(preceded(ASSUMING, block)) check_using = using 
  { make_check ~check_name ~check_body ~check_assuming ~check_using }

using:
  USING u_name = ident u_args = loption(brackets(comma_sep1(separated_pair(ident, COMMA, block))))
  { { u_name; u_args } }
  
%inline block:
  fs = braces(formula*)
  { fs }
  
%inline formula:
  f = prim_formula
  { L.make f $loc(f) }    

prim_formula:
  r = atom
  { Atom r }
  | r = test
  { r }
  | f1 = formula op = lbinop f2 = formula 
  { Binary (op, f1, f2) }
	| q = quant rangings = comma_sep1(ranging) b = block_or_bar
  { Quant (q, rangings, b) }
	| f1 = formula IMPLIES f2 = formula ELSE f3 = formula 
  { Ite (f1, f2, f3) }
	| f1 = formula IMPLIES f2 = formula 
  { Binary (Implies, f1, f2) }
  | op = lunop f = formula 
  { Unary (op, f) }
	| b = block
  { Block b }
	| f = parens(prim_formula)
  { f }

%inline atom: 
  pred = ident primed = iboption(PRIME) args = parens(comma_sep1(ident)) 
  { make_atom ~pred ~args ~primed () }

%inline test:
  l = ident EQ r = ident 
  { Test (Eq, l, r) }
  | l = ident NEQ r = ident 
  { Test (Neq, l, r) }

%inline quant:
	ALL
  { All }
	| SOME
  { Exists }
  
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
	EVENTUALLY { F }
	| ALWAYS { G }
	| NOT { Not }
	| AFTER { X }



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
