open Containers
module F = Format
module L = Location

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
  | Lit of { name: ident; args: ident list; positive: bool; prime: bool }
  | Test of ident * comparator * ident 
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
  | Eq
  | Not_eq

let and_ p q = L.make_located (Binop (p, And, q)) L.dummy
let or_ p q = L.make_located (Binop (p, Or, q)) L.dummy
let implies p q = L.make_located (Binop (p, Implies, q)) L.dummy
let not_ p =  L.make_located (Unop (Not, p)) L.dummy

let lit ~positive ~prime name args = 
  L.make_located (Lit { name; args; positive; prime }) L.dummy

let test left op right = 
  L.make_located (Test (left, op, right)) L.dummy

let sig_name = function
  | Sort name | One_sig { name; _ } | Set { name; _ } ->
    name


let domain_name (Field { profile; _ }) =
  match profile with
  | Relation [] ->
    assert false
  | Partial_function (dom, _) | Relation (dom :: _) ->
    dom

let brackets x = F.within "[" "]" x

(* regroups fields [f1; f2...] into an association list [ (s1, [f1;...]); ...] such that every `s_i` is the domain of all fields appearing in the associated sub-list. *)
let fields_by_signatures (Model { fields; _ }) =
  let eq f1 f2 = Symbol.equal (domain_name f1) (domain_name f2) in
  let partition = List.group_by ~hash:(fun f -> Symbol.hash @@ domain_name f) ~eq fields in
  List.map
    (function [] -> assert false | hd :: _ as l -> (domain_name hd, l))
    partition


let rec print fmt model =
  let (Model { module_; opens; facts; preds; events; assertions; commands; _ })
    =
    model
  in
  ( match module_ with
    | Some (Module m) ->
      F.fprintf fmt "module %a@\n" Symbol.pp m
    | None ->
      () );
  List.iter (print_open fmt) opens;
  print_sigs_and_fields fmt model;
  List.iter (print_fact fmt) facts;
  List.iter (print_pred fmt) preds;
  List.iter (print_event fmt) events;
  List.iter (print_assertion fmt) assertions;
  List.iter (print_command fmt) commands


and print_open fmt (Open { name; parameters; alias }) =
  F.fprintf fmt "open %a" Symbol.pp name;
  ( if not @@ List.is_empty parameters
    then
      let ps = List.intersperse ", " @@ List.map Symbol.to_string parameters in
      F.fprintf fmt "[%a]" F.(list string) ps );
  match alias with
  | Some a ->
    F.fprintf fmt " as %a@\n" Symbol.pp a
  | None ->
    F.fprintf fmt "@\n"


and print_sigs_and_fields fmt (Model { sigs; _ } as model) =
  let fs = fields_by_signatures model in
  List.iter (print_sig fmt fs) sigs


and print_parent fmt = function
  | One_sig { parent; _ } | Set { parent; _ } ->
    F.fprintf fmt "in %a " print_ident parent
  | _ ->
    ()


and print_sig fmt fields_by_sigs sig_ =
  let prefix =
    match sig_ with
    | One_sig _ ->
      "one "
    | Set { is_var; _ } when is_var ->
      "var "
    | _ ->
      ""
  in
  let name = sig_name sig_ in
  let fields = List.assoc_opt ~eq:Symbol.equal name fields_by_sigs in
  F.fprintf fmt "%ssig %a %a{@[<hv2>" prefix print_ident name print_parent sig_;
  ( match fields with
    | None ->
      ()
    | Some fs ->
      F.fprintf fmt "@ %a " F.(list ~sep:(return ",@ ") print_field) fs
  );
  F.fprintf fmt "@]}@\n"


and print_field fmt (Field { name; profile; is_var }) =
  if is_var then F.fprintf fmt "var ";
  F.fprintf fmt "%a : %a" print_ident name print_profile profile


and print_profile fmt = function
  | Partial_function (_, cod) ->
    F.fprintf fmt "lone %a" print_ident cod
  | Relation ([] | [ _ ]) ->
    assert false
  | Relation [ _; cod ] ->
    F.fprintf fmt "set %a" print_ident cod
  | Relation (_ :: cods) ->
    F.fprintf fmt "%a" F.(list ~sep:(const string "->") print_ident) cods


and print_fact fmt (Fact { name; body }) =
  let n = Option.map_or ~default:"" Symbol.to_string name in
  F.fprintf fmt "fact %s%a@\n" n print_block body


and print_assertion fmt (Assert { name; body }) =
  F.fprintf fmt "assert %a%a@\n" print_ident name print_block body


and print_pred fmt (Pred { name; parameters; body }) =
  F.fprintf
    fmt
    "pred %a%a %a@\n"
    print_ident
    name
    F.(
      brackets
      @@ list ~sep:(const string ", ")
      @@ pair ~sep:(const string ": ") print_ident print_ident)
    parameters
    print_block
    body


and print_event fmt (Event { name; parameters; body }) =
  F.fprintf
    fmt
    "pred %a%a %a@\n"
    print_ident
    name
    F.(
      brackets
      @@ list ~sep:(const string ", ")
      @@ pair ~sep:(const string ": ") print_ident print_ident)
    parameters
    print_block
    body


and print_command fmt = function
  | Run { name; scope = None } ->
    F.fprintf fmt "run %a" print_ident name
  | Run { name; scope = Some s } ->
    F.fprintf fmt "run %a %a" print_ident name print_scope s
  | Check { name; scope = None } ->
    F.fprintf fmt "check %a" print_ident name
  | Check { name; scope = Some s } ->
    F.fprintf fmt "check %a %a" print_ident name print_scope s


and print_scope fmt = function
  | With_default (num, []) ->
    F.fprintf fmt "for %d@\n" num
  | With_default (num, tss) ->
    F.fprintf
      fmt
      "for %d but %a"
      num
      F.(list ~sep:(return ",@ ") print_typescope)
      tss
  | Without_default [] ->
    assert false
  | Without_default tss ->
    F.fprintf
      fmt
      "for %a"
      F.(list ~sep:(return ",@ ") print_typescope)
      tss


and print_typescope fmt { exactly; number; sort } =
  F.fprintf
    fmt
    "%s%d %a"
    (if exactly then "exactly " else " ")
    number
    print_ident
    sort


and print_foltl fmt L.{ data; _ } = print_prim_foltl fmt data

and print_prim_foltl fmt =
  let open F in
  function
  | Lit { name; args; positive; prime } ->
    fprintf
      fmt
      "%a %s %a%s"
      print_tuple
      args
      (if positive then "in" else "!in")
      print_ident
      name
      (if prime then "'" else "")
  | Test (id1, op, id2) ->
    fprintf
      fmt
      "%a %a %a"
      print_ident
      id1 
      print_comparator
      op
      print_ident
      id2
  | Unop (op, f) ->
    fprintf fmt "(%a %a)" print_unop op print_foltl f
  | Binop (f1, op, f2) ->
    fprintf
      fmt
      "(@[<hv2>%a %a@ %a@])"
      print_foltl
      f1
      print_binop
      op
      print_foltl
      f2
  | If_then_else (c, t, e) ->
    fprintf fmt "(%a@ %a@ %a)" print_foltl c print_foltl t print_foltl e
  | Call (p, args) ->
    fprintf
      fmt
      "%a%a"
      print_ident
      p
      (brackets @@ list ~sep:(const string ", ") print_ident)
      args
  | Quant (_, _, []) ->
    assert false
  | Quant (q, rangings, [ f ]) ->
    fprintf
      fmt
      "%a %a | %a"
      print_quant
      q
      (list ~sep:(const string ", ") print_ranging)
      rangings
      print_foltl
      f
  | Quant (q, rangings, block) ->
    fprintf
      fmt
      "%a %a@ %a"
      print_quant
      q
      (list ~sep:(const string ", ") print_ranging)
      rangings
      print_block
      block
  | Block b ->
    print_block fmt b


and print_ranging fmt (vars, sort) =
  F.fprintf
    fmt
    "%a: %a"
    F.(list ~sep:(const string ", ") print_ident)
    vars
    print_ident
    sort


and print_block fmt b =
  F.fprintf fmt "@[<hov2>{@ %a@ }@]" F.(list ~sep:(return "@ ") print_foltl) b


and print_tuple fmt ids =
  let ids' = List.map Symbol.to_string ids in
  F.fprintf fmt "%a" F.(list ~sep:(const string "->") string) ids'


and print_quant fmt q =
  let s = match q with Some_ -> "some" | All -> "all" in
  F.fprintf fmt "%s" s


and print_comparator fmt op =
  let s_op =
    match op with Eq -> "=" | Not_eq -> "!="
  in
  F.fprintf fmt "%s" s_op


and print_ident fmt id = F.fprintf fmt "%a" Symbol.pp id

and print_unop fmt op =
  let s_op =
    match op with
    | Not ->
      "!"
    | After ->
      "after"
    | Eventually ->
      "eventually"
    | Always ->
      "always"
  in
  F.fprintf fmt "%s" s_op


and print_binop fmt op =
  let s_op =
    match op with
    | And ->
      "&&"
    | Or ->
      "||"
    | Implies ->
      "=>"
    | Iff ->
      "<=>"
  in
  F.fprintf fmt "%s" s_op
