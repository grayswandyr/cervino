Require Import List.
Require Import String.

Definition mlSort := string.

Record variable :=make_variable {
  var_name: string;
  var_sort: mlSort;
}.

Record constant := make_constant {
  cst_name: string;
  cst_sort: mlSort;
}.

Record relation := make_relation {
  rel_name: string;
  rel_profile : list mlSort;
}.

Inductive mlIdent :=
| MLS (s: mlSort)
| MLV (v: variable)
| MLC (c: constant)
| MLR (r: relation).

Definition isMLSort id := match id with MLS _ => True | _ => False end.
Definition isVar id := match id with MLV _ => True | _ => False end.
Definition isCst id := match id with MLC _ => True | _ => False end.
Definition isMLRel id := match id with MLR _ => True | _ => False end.
Definition getMLSort id : isMLSort id -> _ :=
  match id return isMLSort id -> _ with MLS s => fun h => s | _ => fun h => match h with end end.
Definition getVar id : isVar id -> _ :=
  match id return isVar id -> _ with MLV v => fun h => v | _ => fun h => match h with end end.
Definition getCst id : isCst id -> _ :=
  match id return isCst id -> _ with MLC c => fun h => c | _ => fun h => match h with end end.
Definition getMLRel id : isMLRel id -> _ :=
  match id return isMLRel id -> _ with MLR r => fun h => r | _ => fun h => match h with end end.
  
Lemma isMLSortDec id : { isMLSort id } + { not (isMLSort id) }.
Proof.
  destruct id; simpl; try (left; simpl; now auto); right; intro; tauto.
Defined.
Lemma isVarDec id : { isVar id } + { not (isVar id) }.
Proof.
  destruct id; simpl; try (left; simpl; now auto); right; intro; tauto.
Defined.
Lemma isCstDec id : { isCst id } + { not (isCst id) }.
Proof.
  destruct id; simpl; try (left; simpl; now auto); right; intro; tauto.
Defined.
Lemma isMLRelDec id : { isMLRel id } + { not (isMLRel id) }.
Proof.
  destruct id; simpl; try (left; simpl; now auto); right; intro; tauto.
Defined.

Inductive term : Type :=
  Var (v: variable)
| Cst (c: constant).

Definition termSort (tm: term): mlSort :=
  match tm with
    Var v => var_sort v
  | Cst c => cst_sort c
  end.

Definition isMLLit (r: relation) (args: list term): Prop := 
  rel_profile r = List.map termSort args.

Inductive literal: Type :=
| Pos_app (nx: nat) (r: string) (args: list term)
| Neg_app (nx: nat) (r: string) (args: list term)
| Eq (t1: term) (t2: term)
| Not_eq (t1: term) (t2: term).

Inductive formula: Type :=
  True: formula
| False: formula
| Lit: literal -> formula
| And: formula -> formula -> formula 
| Or: formula -> formula -> formula
| Exists: variable -> formula -> formula
| All: variable -> formula -> formula
| F: formula -> formula
| G: formula -> formula.

Definition ev_modification := list term.

Record ev_modify := make_ev_modify {
  mod_rel: relation;
  mod_mods : list ev_modification;
}.

Record event := make_event {
  ev_name : string;
  ev_args : list variable;
  ev_body : formula;
  ev_modificationifies : list ev_modify;
}.

Inductive transfo :=
  TEA: transfo (* transfo Ex -> Alll avec intro E *)
| TTC: relation -> variable -> formula -> transfo (* transitive closure *)
| TFC: (event -> formula) -> transfo. (* frame condition *)

Record check := make_check {
  chk_name: string;
  chk_body: formula;
  chk_assuming: formula;
  chk_using: transfo;
}.

Record path := make_path {
  tc : relation;
  base : relation;
  between : option relation
}.

Record model := make_model {
  axioms : list formula;
  events : list event;
  closures : list path;
  checkWith : check;
}.
