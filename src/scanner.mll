
{  (* BEGIN HEADER *)
open Parser

module L = Location

let keywords =
    Hashtbl.of_list
    [ ("F", EVENTUALLY)
    ; ("G", ALWAYS)
    ; ("X", AFTER)
    ; ("all", ALL)
    ; ("assuming", ASSUMING)
    ; ("at", AT)
    ; ("axiom", AXIOM)
    ; ("check", CHECK)
    ; ("constant", CONSTANT)
    ; ("else", ELSE)
    ; ("event", EVENT)
    ; ("in", IN)
    ; ("macro", MACRO)
    ; ("modifies", MODIFIES)
    ; ("relation", RELATION)
    ; ("some", SOME)
    ; ("sort", SORT)
    ; ("paths", PATHS)
    ; ("using", USING)
    ]

let error lexbuf msg  =
    Msg.err @@ fun m -> 
    m "%a@ %s" L.pp_positions (L.positions_of_lexbuf lexbuf) msg


} (* END HEADER *)


let newline = ('\010' | '\013' | "\013\010")

let whitespace = [ ' ' '\t' ]

let digit = [ '0'-'9' ]

let number = (digit | [ '1'-'9'] digit*)
                           
let letter = [ 'A'-'Z' 'a'-'z' ]

let ident = letter (letter | digit | '_')*

let comment_line = "//"
let comment_beg = "/*"
let comment_end = "*/"

rule main = parse
| newline
    { Lexing.new_line lexbuf; main lexbuf }
| whitespace+
    { main lexbuf }
| "'" { PRIME }
| ":" { COLON }
| "," { COMMA }
| "*" { CART }
| "|" { BAR }
| "(" { LPAREN }
| ")" { RPAREN }
| "[" { LBRACKET }
| "]" { RBRACKET }
| "{" { LBRACE }
| "}" { RBRACE }
| "!" { NOT }
| "=" { EQ }
| "!=" { NEQ }
| "=>" { IMPLIES }
| "&&" { AND }
| "||" { OR }
| "<=>" { IFF }
| ident as s { 
    try Hashtbl.find keywords s 
    with Not_found -> IDENT s
    }
| comment_line 
    { line_comment lexbuf }
| comment_beg
    { comment 1 lexbuf }
| eof  
     { EOF } 
| _ as c
    { error lexbuf ("unexpected character(s): " ^ (String.make 1 c)) }

and line_comment = parse
| newline
    { Lexing.new_line lexbuf; main lexbuf }
| eof  
     { EOF } 
| _
    { line_comment lexbuf }
  

and comment opened = parse
| comment_beg
    { comment (opened + 1) lexbuf }
| comment_end
    { let nb = opened - 1 in
      if nb < 1 then main lexbuf
      else comment nb lexbuf }
| newline
    { Lexing.new_line lexbuf; comment opened lexbuf }
| eof
    { error lexbuf "nterminated comment" }
| _
    { comment opened lexbuf }
