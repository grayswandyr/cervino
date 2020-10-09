open Ast

(* expansion of quantified formulas featuring telescopes *)
let quantify q var_name var_sort b =
  let var = make_variable ~var_name ~var_sort in
  match q with Cst.All -> all var b | Cst.Exists -> exists var b


let rec expand_range q range b =
  match range with
  | [] ->
      assert false
  | [ (x, s) ] ->
      quantify q x s b
  | (x, s) :: rs ->
      quantify q x s (expand_range q rs b)


let rec expand_telescope q telescope block =
  match telescope with
  | [] ->
      assert false
  | [ range ] ->
      expand_range q range block
  | range :: ts ->
      expand_range q range (expand_telescope q ts block)


(* smart constructors *)
let all telescope block = expand_telescope Cst.All telescope block

let exists telescope block = expand_telescope Cst.All telescope block
