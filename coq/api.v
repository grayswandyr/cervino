
Require Import List.
Require Import String.

Require Import utils.

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

(*
Require Import Extraction.
Require Import Coq.extraction.ExtrOcamlBasic.

Require Import extraction.ExtrOcamlString.
Extract Inlined Constant String.append => "(^)".
Extract Inlined Constant String.string_dec => "(=)".
Extract Inductive string => "string" [ """""" "(fun (a, b) -> (String.make 1 a) ^ b)"] "(fun e c s -> if s = """" then e else c s.[0] (String.sub s 1 (String.length s - 1)))".

Extract Inductive nat => int [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Extract Inductive sigT => "( * )" [ "" ].
Extract Inlined Constant projT1 => "fst".
Extract Inlined Constant projT2 => "snd".

Extraction "/tmp/api.ml" mlCheck mlModel.
*)

(**************************************************************************)

Definition mlVarIds v := MLV v :: MLS (mlVarSort v) :: nil.

Definition mlCstIds c := MLC c :: MLS (mlCstSort c) :: nil.

Definition mlRelIds r := MLR r :: (List.map MLS (mlRelArity r)).

Definition mlTermIds tm: list mlIdent :=
  match tm with
   MLVar v => mlVarIds v
  | MLCst c => mlCstIds c
  end.

Definition mlLitIds l : list mlIdent :=
  match l with
    MLPApp nx r args => 
      mlRelIds {| mlRelName := r; mlRelArity := List.map mlTermSort args |} ++
        List.concat (List.map mlTermIds args)
  end.

Definition mlAtomIds a : list mlIdent :=
  match a with
  | MLLiteral l => mlLitIds l
  | MLNLiteral l => mlLitIds l
  | MLEq t1 t2 => mlTermIds t1 ++ mlTermIds t2
  | MLNEq t1 t2 => mlTermIds t1 ++ mlTermIds t2
  end.

Fixpoint mlFormulaIds f :=
  match f with
    MLFTrue | MLFFalse => nil
  | MLAtom a => mlAtomIds a
  | MLAnd f1 f2 | MLOr f1 f2 => mlFormulaIds f1 ++ mlFormulaIds f2
  | MLEx v f' | MLAll v f' => MLS (mlVarSort v) :: MLV v :: mlFormulaIds f'
  | MLF f' | MLG f' => mlFormulaIds f'
  end.

Definition mlEventIds ev :=
  List.map MLV (mlEvArgs ev) ++ 
  List.map MLS (List.map mlVarSort (mlEvArgs ev)) ++
  mlFormulaIds (mlEvBody ev).

Definition mlPathIds p := mlRelIds (mlTC p) ++ mlRelIds (mlBase p).

Definition mlUsingIds u evts :=
  match u with
    TEA => nil
  | TTC r v f => MLR r :: MLV v :: (mlFormulaIds f)
  | TFC ef => List.concat (List.map (fun e => mlFormulaIds (ef e)) evts) 
  end.

Definition mlCheckIds chk evts :=
  mlFormulaIds (mlChkBody chk) ++
  mlFormulaIds (mlChkAssumes chk) ++
  mlUsingIds (mlChkUsing chk) evts.

Definition mlModelIds m :=
  List.concat (List.map mlFormulaIds (mlAxioms m)) ++
  List.concat (List.map mlEventIds (mlEvents m)) ++
  List.concat (List.map mlPathIds (mlClosures m)) ++
  (mlCheckIds (mlCheckWith m) (mlEvents m)).

Definition mlSorts m := 
  imap_filter isMLSortDec
    (mlModelIds m)
    (fun v h1 h2 => getMLSort v h1).

Definition mlAllVariables m: list mlVariable :=
  imap_filter isMLVarDec
    (mlModelIds m)
    (fun v h1 h2 => getMLVar v h1).

Definition mlVariables m s :=
  List.filter (fun v => if string_dec (mlVarSort v) s then true else false) (mlAllVariables m).

Definition mlAllConstants m: list mlConstant :=
  imap_filter isMLCstDec
    (mlModelIds m)
    (fun v h1 h2 => getMLCst v h1).

Definition mlConstants m s :=
  List.filter (fun v => if string_dec (mlCstSort v) s then true else false) (mlAllConstants m).

Definition mlRelations m: list mlRelation :=
  imap_filter isMLRelDec
    (mlModelIds m)
    (fun v h1 h2 => getMLRel v h1).

Lemma mlSortOfVar: forall m v,
  In v (mlAllVariables m) -> In (mlVarSort v) (mlSorts m).
Admitted.

Lemma mlSortOfCst: forall m c,
  In c (mlAllConstants m) -> In (mlCstSort c) (mlSorts m).
Admitted.

Lemma mlSortOfRel: forall m r,
  In r (mlRelations m) -> forall s, In s (mlRelArity r) -> In s (mlSorts m).
Admitted.

