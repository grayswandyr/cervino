
%token IMPLIES ELSE ALL SOME LONE COLON EOF EQ ARROW PRIME
%token BAR AND OR IFF EVENTUALLY ALWAYS AFTER NOT ONE IN SIG EXPECT
%token LPAREN RPAREN LBRACE RBRACE LBRACKET RBRACKET COMMA VAR
%token PRED RUN CHECK ASSERT FACT BUT FOR EXACTLY SET MODULE
%token <string> IDENT 
%token <string> EVENT_IDENT 
%token <int> NUMBER

%nonassoc BAR
%left OR
%left IFF
%right IMPLIES ELSE
%left AND
%nonassoc NOT AFTER ALWAYS EVENTUALLY 


%start <unit>parse

%%

%public parse: 
  moduleDecl? paragraph+ EOF 
  {}

moduleDecl:
  MODULE IDENT
  {}  

paragraph:
  signature
  | predicate
  | fact
  | assertion
  | command
  {}

%inline signature:
  sort_sig | one_constant_sig | var_sig
  {}

sort_sig:
  SIG IDENT braces(field*)
  {}

one_constant_sig:
  ONE SIG IDENT IN IDENT LBRACE RBRACE
  {}

var_sig:
  VAR ONE? SIG IDENT IN IDENT LBRACE RBRACE
  {}

field: 
  IDENT COLON multiplicity? IDENT
  {}

multiplicity:
  LONE | SET  
  {}

predicate:
  PRED IDENT option(brackets(separated_list(COMMA, arg))) block
  | PRED EVENT_IDENT option(brackets(separated_list(COMMA, arg))) epr_block
  {}

%inline arg:
  IDENT COLON IDENT
  {}

fact:
  FACT IDENT? block
  {}

assertion:
  ASSERT IDENT block
  {}

%inline command:
  check_or_run ident_or_block scope? expect?
  {}

%inline check_or_run:
  CHECK | RUN
  {}  

ident_or_block:
  IDENT | block
  {}

scope:
  FOR NUMBER option(pair(BUT, comma_sep1(typescope)))
  | FOR comma_sep1(typescope)
  {}

%inline typescope:
  ioption(EXACTLY) NUMBER IDENT
  {}

expect:
  EXPECT NUMBER
  {}

formula :
  applied_relation
  
  | formula lbinop formula
	
	| quant comma_sep1(range_decl) block_or_bar
      
	| formula IMPLIES formula ELSE formula 
      
	| formula IMPLIES formula 

  | lunop formula 
      
	| block
  
	| parens(formula)
  {}

epr_block: 
  braces(epr_formula*)
  {}

epr_formula:
  ALL comma_sep1(range_decl) epr_or_bar
  | epr_formula AND epr_formula
  | epr_formula OR epr_formula
  | parens(epr_formula)
  | epr_basic
  {}

epr_or_bar: 
  epr_block | BAR epr_formula  
  {}

epr_basic:
  applied_relation 
  | NOT epr_basic
  {}

applied_relation:
  tuple comparator IDENT PRIME?
  {}

tuple:
  separated_nonempty_list(ARROW, IDENT)
  {}

%inline comparator:
  IN
  | NOT IN
  | EQ
  | NOT EQ
  {}  
  
%inline quant:
	ALL
	| SOME
  {}

%inline range_decl:
	comma_sep1(ident) COLON IDENT
  {}

%inline ident:
  IDENT
  {}
 	//{ Raw_ident.ident id $startpos(id) $endpos(id) }
  
%inline block_or_bar:
 	BAR formula
	| block
   {}

%inline block:
	 braces(formula*)
   {}

%inline lbinop:
	AND
	| OR
	| IFF
  {}

%inline lunop:
	EVENTUALLY
	| ALWAYS
	| NOT
	| AFTER 
  {}



    ////////////////////////////////////////////////////////////////////////
    // MENHIR MACROS
    ////////////////////////////////////////////////////////////////////////
        
      
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

