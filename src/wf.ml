open Containers
open Cst
module L = Location
module M = Messages

let find_pred_body (Model { preds; _ }) name =
  match List.find_opt (fun (Pred p) -> Symbol.equal p.name name) preds with
  | None ->
    M.fail
      (Format.sprintf "Definition of predicate %a not found" Symbol.pp name)
  | Some (Pred { body; _ }) ->
    body


let find_assert_body (Model { assertions; _ }) name =
  match
    List.find_opt (fun (Assert p) -> Symbol.equal p.name name) assertions
  with
  | None ->
    M.fail
      (Format.sprintf "Definition of assertion %a not found" Symbol.pp name)
  | Some (Assert { body; _ }) ->
    body


(* 
     Returns: () if well-formed, raises (Some_under_always info) otherwise, where info contains information about the culprit subformula (formula, location, polarity).*)

exception Not_in_ufop of foltl

let rec check_ufo_prime_inner
    (model : Cst.t) (L.{ data = f; _ } as f_loc : foltl) : unit = 
  match f with
  | Unop ((Always | After | Eventually), _) 
  | Quant _ -> raise (Not_in_ufop f_loc)
  | Lit _ | Test _ -> ()
  | Unop (Not, f') -> check_ufo_prime_inner model f'
  | Binop (f1, _, f2) -> 
    check_ufo_prime_inner model f1;
    check_ufo_prime_inner model f2
  | If_then_else (f1, f2, f3) -> 
    check_ufo_prime_inner model f1;
    check_ufo_prime_inner model f2;
    check_ufo_prime_inner model f3
  | Block b -> check_ufo_block check_ufo_prime_inner model b
  | Call (name, _) -> 
    let body = find_pred_body model name in 
    check_ufo_block check_ufo_prime_inner model body

and check_ufo_prime model (L.{ data = f; _ } as f_loc)  = match f with
  | Quant (Some_, _, _) 
  | Unop ((Always | After | Eventually), _) -> raise (Not_in_ufop f_loc)
  | Lit _ | Test _ -> ()
  | Unop (Not, f') -> check_ufo_prime_inner model f'
  | Binop (f1, (And | Or), f2) -> 
    check_ufo_prime model f1;
    check_ufo_prime model f2
  | Binop (f1, Implies, f2) -> 
    check_ufo_prime_inner model f1;
    check_ufo_prime model f2;
  | Binop (f1, Iff, f2) -> 
    check_ufo_prime_inner model f1;
    check_ufo_prime_inner model f2
  | If_then_else (f1, f2, f3) -> 
    check_ufo_prime_inner model f1;
    check_ufo_prime model f2;
    check_ufo_prime model f3
  | Quant (All, _, b) 
  | Block b -> check_ufo_block check_ufo_prime model b
  | Call (name, _) -> 
    let body = find_pred_body model name in 
    check_ufo_block check_ufo_prime model body

and check_ufo_block proc model block = 
  List.iter (proc model) block

let check_event model (Event { body; _}) = 
  List.iter (check_ufo_prime model) body 


(* Checks whether a [some] appears under an [always]. As formulas are not in NNF, we must take the polarity of subformulas into account (e.g. an [all] in negative position amounts to an [always]). The function goes top down.
   parameters:
   - m : the containing model (needed to check_foltl in preds)
   - saw_g : already met an [always] at Some position (type option)
   - polarity : current polarity (true = positive)
   - f : checked subformula
     Returns: () if well-formed, raises (Some_under_always info) otherwise, where info contains information about the culprit subformula (formula, location, polarity).
*)
exception Some_under_always of (foltl * bool) * (bool * foltl)

let rec check_foltl model saw_g pol (L.{ data = f; loc } as f_loc) =
  match (saw_g, pol, f) with
  | Some occ, true, Quant (Some_, _, _) | Some occ, false, Quant (All, _, _)
    ->
    raise (Some_under_always (occ, (pol, L.(make_located f loc))))
  | _, _, Quant ((Some_ | All), _, b) ->
    check_foltl model saw_g pol { data = Block b; loc }
  | None, true, Unop (Always, f')
  | None, false, Unop (Eventually, f')
  | Some _, _, Unop ((Always | Eventually), f') ->
    check_foltl model (Some (f_loc, pol)) pol f'
  | None, false, Unop (Always, f')
  | None, true, Unop (Eventually, f')
  | _, _, Unop (After, f') ->
    check_foltl model saw_g pol f'
  | _, _, Unop (Not, f') ->
    check_foltl model saw_g (not pol) f'
  | _, _, Binop (f1, (And | Or), f2) ->
    check_foltl model saw_g pol f1;
    check_foltl model saw_g pol f2
  | _, _, Binop (f1, Implies, f2) ->
    check_foltl model saw_g (not pol) f1;
    check_foltl model saw_g pol f2
  | _, _, Binop (f1, Iff, f2) ->
    check_foltl model saw_g pol f1;
    check_foltl model saw_g pol f2;
    check_foltl model saw_g (not pol) f1;
    check_foltl model saw_g (not pol) f2
  | _, _, If_then_else (c, t, e) ->
    check_foltl model saw_g (not pol) c;
    check_foltl model saw_g pol t;
    check_foltl model saw_g pol c;
    check_foltl model saw_g pol e
  | _, _, Block fs ->
    check_block model saw_g pol fs
  | _, _, Lit _ 
  | _, _, Test _->
    ()
  | _, _, Call (pred, _) ->
    check_pred model saw_g pol pred

and check_block model saw_g polarity fs = 
  List.iter (check_foltl model saw_g polarity) fs


and check_pred model saw_g polarity pred =
  let body = find_pred_body model pred in
  check_foltl model saw_g polarity { data = Block body; loc = L.dummy }


let check_model (Model { facts; commands; events; _ } as model) =
  let fact_bodies =
    List.map
      (fun (Fact { body; _ }) -> L.{ data = Block body; loc = L.dummy })
      facts
  in
  let run_bodies, check_bodies =
    List.partition_map
      (function
        | Run { name; _ } ->
          `Left L.{ data = Block (find_pred_body model name); loc = L.dummy }
        | Check { name; _ } ->
          `Right
            L.{ data = Block (find_assert_body model name); loc = L.dummy })
      commands
  in
  check_block model None true fact_bodies;
  check_block model None true run_bodies;
  check_block model None false check_bodies;
  List.iter (check_event model) events

let check_and_report model =
  try 
    check_model model;
    M.info "Model is well-formed."
  with
  | Some_under_always
      ( ((L.{ loc = g_loc; _ } as g), g_pol)
      , (pol, (L.{ data = Quant (q, _, _); loc } as f)) ) ->
    let g_polarity = if g_pol then "n" else " negated" in
    let f_polarity = if pol then "" else "negatively " in
    let msg =
      Format.(
        sprintf
          "`%a` appears %sunder a%s `always` connective:@\n\
           %d:%d-...: %a@\n\
           %d:%d-...: %a"
          Cst.print_quant
          q
          f_polarity
          g_polarity
          (L.begl g_loc)
          (L.begc g_loc)
          Cst.print_foltl
          g
          (L.begl loc)
          (L.begc loc)
          Cst.print_foltl
          f)
    in
    M.fail msg
  | Not_in_ufop (L.{ loc; _ } as f) -> 
    let msg = 
      Format.(
        sprintf 
          "%d:%d-...: formula forbidden in an event or predicate \
           called from an event@\n%a"
          (L.begl loc)
          (L.begc loc)
          Cst.print_foltl f
      )
    in
    M.fail msg

