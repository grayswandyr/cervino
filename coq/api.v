Require Import List.
Require Import String.

Definition mlSort := string.

Record mlVariable := {
  mlVarName: string;
  mlVarSort: mlSort;
}.

Record mlConstant := {
  mlCstName: string;
  mlCstSort: mlSort;
}.

Record mlRelation := {
  mlRelName: string;
  mlRelArity : list mlSort;
}.

Inductive mlIdent :=
| MLS (s: mlSort)
| MLV (v: mlVariable)
| MLC (c: mlConstant)
| MLR (r: mlRelation).

Definition isMLSort id := match id with MLS _ => True | _ => False end.
Definition isMLVar id := match id with MLV _ => True | _ => False end.
Definition isMLCst id := match id with MLC _ => True | _ => False end.
Definition isMLRel id := match id with MLR _ => True | _ => False end.
Definition getMLSort id : isMLSort id -> _ :=
  match id return isMLSort id -> _ with MLS s => fun h => s | _ => fun h => match h with end end.
Definition getMLVar id : isMLVar id -> _ :=
  match id return isMLVar id -> _ with MLV v => fun h => v | _ => fun h => match h with end end.
Definition getMLCst id : isMLCst id -> _ :=
  match id return isMLCst id -> _ with MLC c => fun h => c | _ => fun h => match h with end end.
Definition getMLRel id : isMLRel id -> _ :=
  match id return isMLRel id -> _ with MLR r => fun h => r | _ => fun h => match h with end end.
  
Lemma isMLSortDec id : { isMLSort id } + { not (isMLSort id) }.
Proof.
  destruct id; simpl; try (left; simpl; now auto); right; intro; tauto.
Defined.
Lemma isMLVarDec id : { isMLVar id } + { not (isMLVar id) }.
Proof.
  destruct id; simpl; try (left; simpl; now auto); right; intro; tauto.
Defined.
Lemma isMLCstDec id : { isMLCst id } + { not (isMLCst id) }.
Proof.
  destruct id; simpl; try (left; simpl; now auto); right; intro; tauto.
Defined.
Lemma isMLRelDec id : { isMLRel id } + { not (isMLRel id) }.
Proof.
  destruct id; simpl; try (left; simpl; now auto); right; intro; tauto.
Defined.

Inductive mlTerm : Type :=
  MLVar (v: mlVariable)
| MLCst (c: mlConstant).

Definition mlTermSort (tm: mlTerm): mlSort :=
  match tm with
    MLVar v => mlVarSort v
  | MLCst c => mlCstSort c
  end.

Definition isMLLit (r: mlRelation) (args: list mlTerm): Prop := 
  mlRelArity r = List.map mlTermSort args.

Inductive mlLiteral: Type :=
  MLPApp (nx: nat) (r: string) (args: list mlTerm).

Inductive mlAtom: Type :=
| MLLiteral (lt: mlLiteral)
| MLNLiteral (lt: mlLiteral)
| MLEq (t1: mlTerm) (t2: mlTerm)
| MLNEq (t1: mlTerm) (t2: mlTerm).

Inductive mlFormula: Type :=
  MLFTrue: mlFormula
| MLFFalse: mlFormula
| MLAtom: mlAtom -> mlFormula
| MLAnd: mlFormula -> mlFormula -> mlFormula 
| MLOr: mlFormula -> mlFormula -> mlFormula
| MLEx: mlVariable -> mlFormula -> mlFormula
| MLAll: mlVariable -> mlFormula -> mlFormula
| MLF: mlFormula -> mlFormula
| MLG: mlFormula -> mlFormula.

Definition mlEvMod := list mlTerm.

Record mlEvModify := {
  mlModRel: mlRelation;
  mlModMods : list mlEvMod;
}.

Record mlEvent := {
  mlEvName : string;
  mlEvArgs : list mlVariable;
  mlEvBody : mlFormula;
  mlEvModifies : list mlEvModify;
}.

Inductive mlUsing :=
  TEA: mlUsing (* transfo Ex -> Alll avec intro E *)
| TTC: mlRelation -> mlVariable -> mlFormula -> mlUsing (* transitive closure *)
| TFC: (mlEvent -> mlFormula) -> mlUsing. (* frame condition *)

Record mlCheck := {
  mlChkName: string;
  mlChkBody: mlFormula;
  mlChkAssumes: mlFormula;
  mlChkUsing: mlUsing;
}.

Record mlPath := {
  mlTC : mlRelation;
  mlBase : mlRelation;
}.

Record mlModel := {
  mlAxioms : list mlFormula;
  mlEvents : list mlEvent;
  mlClosures : list mlPath;
  mlCheckWith : mlCheck;
}.
