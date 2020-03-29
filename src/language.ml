open Containers
open Sexplib.Std

type model = {
  sorts : sort list;
  relations : relation list;
  facts : block list;
  events : event list; 
}
and sort = string
and relation = string
and block = foltl list
and foltl =
  | FPred of string 
  | FNot of foltl
  | FAnd of foltl * foltl
  | FOr of foltl * foltl
  | FImplies of foltl * foltl
  | FIff of foltl * foltl
  | FNext of foltl
  | FAlways of foltl
  | FEventually of foltl
and event = {
  args : string list;
  body : univ_fml;
}
and univ_fml =
  | UPrime_fml of prime_fml
  | UAll of string * sort * univ_fml
  | UAnd of univ_fml * univ_fml
  | UOr of univ_fml * univ_fml
and prime_fml =
  | PPred of string
  | PPrime_pred of string
  | PNot of prime_fml
  | PAnd of prime_fml * prime_fml
  | POr of prime_fml * prime_fml
[@@deriving sexp]


let to_sexp (f : foltl) = sexp_of_foltl f 

let to_string f = 
  String.lowercase_ascii (Sexplib.Sexp.to_string_hum (to_sexp f))

let print f = 
  print_endline (to_string f)

let from_string s = 
  foltl_of_sexp (Sexplib.Sexp.of_string s)

let ( !! ) s = from_string s
