
{  (* BEGIN HEADER *)
open Lexing
open Parser

let update_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <- { pos with
    pos_lnum = pos.pos_lnum + 1;
    pos_bol = pos.pos_cnum;
  }

let error = Messages.located_error

} (* END HEADER *)


let newline = ('\010' | '\013' | "\013\010")

let whitespace = [ ' ' '\t' ]

let digit = [ '0'-'9' ]

let number = (digit | [ '1'-'9'] digit*)
                           
let letter = [ 'A'-'Z' 'a'-'z' ]

let ident = letter (letter | digit | '_')*

let event_ident = '_' ident

let comment_line = ("//" | "--")

rule main = parse
| newline
    { update_line lexbuf; main lexbuf }
| whitespace+
    { main lexbuf }
| number as i
    {
      try
        (NUMBER (int_of_string i))
      with Failure _ ->
        error lexbuf ("Invalid integer constant '" ^ i ^ "'")
    }  
| "|" { BAR }
| "." { DOT } 
| "-" { MINUS } 
| "+" { PLUS } 
| "&" { INTER } 
| "~" { TILDE } 
| ":" { COLON } 
| "=" { EQ } 
| "->" { ARROW } 
| "'" { PRIME }
| "|" { BAR }  
| "(" { LPAREN } 
| ")" { RPAREN } 
| "{" { LBRACE } 
| "}" { RBRACE } 
| "[" { LBRACKET } 
| "]" { RBRACKET } 
| "," { COMMA } 
| ("!" | "not") { NOT } 
| ("=>" | "implies") { IMPLIES } 
| ("&&" | "and") { AND } 
| ("||" | "or") { OR } 
| ("<=>" | "iff") { IFF } 
| "else" { ELSE } 
| "all" { ALL } 
| "some" { SOME } 
| "no" { NO } 
| "lone" { LONE } 
| "eventually" { EVENTUALLY } 
| "always" { ALWAYS } 
| "after" { AFTER } 
| "one" { ONE } 
| "in" { IN } 
| "sig" { SIG } 
| "expect" { EXPECT }
| "var" { VAR }
| "pred" { PRED } 
| "run" { RUN } 
| "check" { CHECK } 
| "assert" { ASSERT } 
| "fact" { FACT } 
| "but" { BUT } 
| "for" { FOR } 
| "exactly" { EXACTLY } 
| "set" { SET } 
| "module" { MODULE }
| "none" { NONE } 
| "univ" { UNIV } 
| "iden" { IDEN } 
| event_ident as x { EVENT_IDENT x }
| ident as x { IDENT x }
| comment_line 
    { line_comment lexbuf }
| "/*"
    { comment 1 lexbuf }
 | eof 
     { EOF } 
| _ as c
    { error lexbuf ("Unexpected character(s): " ^ (String.make 1 c)) }

and line_comment = parse
| newline
    { new_line lexbuf; main lexbuf }
| eof  
     { EOF } 
| _
    { line_comment lexbuf }
  

and comment opened = parse
| "(*"
    { comment (opened + 1) lexbuf }
| "*)"
    { let nb = opened - 1 in
      if nb < 1 then main lexbuf
      else comment nb lexbuf }
| newline
    { new_line lexbuf; comment opened lexbuf }
| eof
    { error lexbuf "End of file reached unterminated comment" }
| _
    { comment opened lexbuf }
