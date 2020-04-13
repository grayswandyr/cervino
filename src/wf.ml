open Containers
open Cst
module L = Location

(* "or" on options *)
let ( <+> ) = Option.Infix.( <+> )

let find_pred_body (Model { preds; _ }) name =
  match List.find_opt (fun (Pred p) -> Symbol.equal p.name name) preds with
  | None ->
    Messages.fail
      (Format.sprintf "Definition of predicate %a not found" Symbol.pp name)
  | Some (Pred { body; _ }) ->
    body


let find_assert_body (Model { assertions; _ }) name =
  match
    List.find_opt (fun (Assert p) -> Symbol.equal p.name name) assertions
  with
  | None ->
    Messages.fail
      (Format.sprintf "Definition of assertion %a not found" Symbol.pp name)
  | Some (Assert { body; _ }) ->
    body


(* Checks whether a [some] appears under an [always]. As formulas are not in NNF, we must take the polarity of subformulas into account (e.g. an [all] in negative position amounts to an [always]). The function goes top down.
   parameters:
   - m : the containing model (needed to walk in preds)
   - saw_g : already met an [always] at Some position (type option)
   - polarity : current polarity (true = positive)
   - f : analyzed subformula
     Returns: None if well-formed, Some info otherwise, where info contains information about the culprit subformula (formula, location, polarity).
*)
let rec analyze_foltl model saw_g polarity f =
  let rec walk saw_g pol (L.{ data = f; loc } as f_loc) =
    match (saw_g, pol, f) with
    | Some occ, true, Quant (Some_, _, _) | Some occ, false, Quant (All, _, _)
      ->
      Some L.(occ, (pol, make_located f loc))
    | _, _, Quant ((Some_ | All), _, b) ->
      walk saw_g pol { data = Block b; loc }
    | None, true, Unop (Always, f')
    | None, false, Unop (Eventually, f')
    | Some _, _, Unop ((Always | Eventually), f') ->
      walk (Some (f_loc, pol)) pol f'
    | None, false, Unop (Always, f')
    | None, true, Unop (Eventually, f')
    | _, _, Unop (After, f') ->
      walk saw_g pol f'
    | _, _, Unop (Not, f') ->
      walk saw_g (not pol) f'
    | _, _, Binop (f1, (And | Or), f2) ->
      walk saw_g pol f1 <+> walk saw_g pol f2
    | _, _, Binop (f1, Implies, f2) ->
      walk saw_g (not pol) f1 <+> walk saw_g pol f2
    | _, _, Binop (f1, Iff, f2) ->
      walk saw_g pol f1
      <+> walk saw_g pol f2
      <+> walk saw_g (not pol) f1
      <+> walk saw_g (not pol) f2
    | _, _, If_then_else (c, t, e) ->
      walk saw_g (not pol) c
      <+> walk saw_g pol t
      <+> walk saw_g pol c
      <+> walk saw_g pol e
    | _, _, Block fs ->
      List.fold_left (fun res f -> res <+> walk saw_g pol f) None fs
    | _, _, Lit _ 
    | _, _, Test _->
      None
    | _, _, Call (pred, _) ->
      analyze_pred model saw_g pol pred
  in
  walk saw_g polarity f


and analyze_pred model saw_g polarity pred =
  let body = find_pred_body model pred in
  analyze_foltl model saw_g polarity { data = Block body; loc = L.dummy }


let analyze_model (Model { facts; commands; _ } as model) =
  let analyze_formulas model polarity fs =
    List.fold_left
      (fun res f -> res <+> analyze_foltl model None polarity f)
      None
      fs
  in
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
  analyze_formulas model true fact_bodies
  <+> analyze_formulas model true run_bodies
  <+> analyze_formulas model false check_bodies
