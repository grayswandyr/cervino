
Require Import List.
Require Import String.

Require Import utils.

Definition mlSort := string.

Record mlPath := {
  mlTC : string;
  mlBase : string;
}.

Inductive mlKind : Type :=
  MSort
| MVar (s: mlSort)
| MCst (s: mlSort)
| MRel (al: list mlSort)
| MError.

Definition isMLSort k := match k with MSort => True | _ => False end.
Definition isMLRel k := match k with MRel _ => True | _ => False end.
Definition isMLVar k := match k with MVar _ => True | _ => False end.
Definition isMLCst k := match k with MCst _ => True | _ => False end.

Definition isMLSortDec k : {isMLSort k}+{not(isMLSort k)} :=
  match k return {isMLSort k}+{not(isMLSort k)} with MSort => left I | _ => right (fun h => match h:False with end) end.

Definition isMLVarDec k : {isMLVar k}+{not(isMLVar k)} :=
  match k return {isMLVar k}+{not(isMLVar k)} with MVar _ => left I | _ => right (fun h => match h:False with end) end.

Definition isMLCstDec k : {isMLCst k}+{not(isMLCst k)} :=
  match k return {isMLCst k}+{not(isMLCst k)} with MCst _ => left I | _ => right (fun h => match h:False with end) end.

Definition isMLRelDec k : {isMLRel k}+{not(isMLRel k)} :=
  match k return {isMLRel k}+{not(isMLRel k)} with MRel _ => left I | _ => right (fun h => match h:False with end) end.

Record mlSig := {
  mlIdents : list string;
  mlKinds : string -> mlKind;
  mlClosures: list mlPath;
(* auxiliairy *)
  isMLSortB s := if isMLSortDec (mlKinds s) then true else false;
  isMLVarB s := if isMLVarDec (mlKinds s) then true else false;
  isMLCstB s := if isMLCstDec (mlKinds s) then true else false;
(* WF *)
  mlSorts: list mlSort := List.filter isMLSortB mlIdents;
  mlVwf: forall v s, mlKinds v = MVar s -> List.In s mlSorts;
  mlCwf: forall v s, mlKinds v = MCst s -> List.In s mlSorts;
  mlRwf: forall v sl, mlKinds v = MRel sl -> forall s, List.In s sl -> List.In s mlSorts;
}.

Module Type MLSignature.
  Parameter sg: mlSig.
End MLSignature.

Module MLCervino(Sg: MLSignature).

Record mlVariable := {
  mlVarName: string;
  mlVar_dcl : isMLVar (mlKinds Sg.sg mlVarName);
  mlVar_in : List.In mlVarName (mlIdents Sg.sg)
}.

Definition mlVarSort (r: mlVariable): mlSort :=
  match mlKinds Sg.sg (mlVarName r) as k return isMLVar k -> _ with
    MVar s => fun h => s
  | _ => fun h => match h with end
  end (mlVar_dcl r).

Lemma mlVariableWF: forall v, mlKinds Sg.sg (mlVarName v) = MVar (mlVarSort v).
Proof.
  intros.
  destruct v as [n d].
  unfold mlVarSort; simpl.
  destruct (mlKinds Sg.sg n); simpl in *; tauto.
Qed.

Definition mlAllVariables :=
  imap_filter (fun id => isMLVarDec (mlKinds Sg.sg id))
    (mlIdents Sg.sg)
    (fun v h1 h2 => {| mlVarName := v; mlVar_dcl := h1; mlVar_in := h2 |}).

Definition mlVariables s :=
  List.filter (fun v => if string_dec (mlVarSort v) s then true else false) mlAllVariables.

Record mlConstant := {
  mlCstName: string;
  mlCst_dcl : isMLCst (mlKinds Sg.sg mlCstName);
  mlCst_in : List.In mlCstName (mlIdents Sg.sg)
}.

Definition mlCstSort (r: mlConstant): mlSort :=
  match mlKinds Sg.sg (mlCstName r) as k return isMLCst k -> _ with
    MCst s => fun h => s
  | _ => fun h => match h with end
  end (mlCst_dcl r).

Lemma mlConstantWF: forall v, mlKinds Sg.sg (mlCstName v) = MCst (mlCstSort v).
Proof.
  intros.
  destruct v as [n d].
  unfold mlCstSort; simpl.
  destruct (mlKinds Sg.sg n); simpl in *; tauto.
Qed.

Definition mlAllConstants :=
  imap_filter (fun id => isMLCstDec (mlKinds Sg.sg id))
    (mlIdents Sg.sg)
    (fun v h1 h2 => {| mlCstName := v; mlCst_dcl := h1; mlCst_in := h2 |}).

Definition mlConstants s :=
  List.filter (fun v => if string_dec (mlCstSort v) s then true else false) mlAllConstants.

Record mlRelation := {
  mlRelName: string;
  mlRel_dcl : isMLRel (mlKinds Sg.sg mlRelName);
  mlRel_in : List.In mlRelName (mlIdents Sg.sg);
}.

Definition mlRelArity (r: mlRelation) :=
  match mlKinds Sg.sg (mlRelName r) as k return isMLRel k -> _ with
    MRel al => fun h => al
  | _ => fun h => match h with end
  end (mlRel_dcl r).

Lemma mlRelationWF: forall r, mlKinds Sg.sg (mlRelName r) = MRel (mlRelArity r).
Proof.
  intros.
  destruct r as [n d]; simpl.
  unfold mlRelArity; simpl.
  destruct (mlKinds Sg.sg n); simpl in *; tauto.
Qed.

Definition mlRelations :=
  imap_filter (fun id => isMLRelDec (mlKinds Sg.sg id))
    (mlIdents Sg.sg)
    (fun v h1 h2 => {| mlRelName := v; mlRel_dcl := h1; mlRel_in := h2 |}).

Inductive mlTerm : Type :=
  MLVar (v: mlVariable)
| MLCst (c: mlConstant).

Definition mlTermSort (tm: mlTerm): mlSort :=
  match tm with
    MLVar v => mlVarSort v
  | MLCst c => mlCstSort c
  end.

Lemma mlTwf: forall t, List.In (mlTermSort t) (mlSorts Sg.sg).
Proof.
  intros.
  destruct t; simpl.
  apply mlVwf with (v:=mlVarName v); simpl.
  generalize (mlVar_dcl v); intro.
  destruct v as [n d]; simpl in *.
  unfold mlVarSort; simpl.
  destruct (mlKinds Sg.sg n); simpl in *; tauto.

  apply mlCwf with (v:=mlCstName c); simpl.
  generalize (mlCst_dcl c); intro.
  destruct c as [n d]; simpl in *.
  unfold mlCstSort; simpl.
  destruct (mlKinds Sg.sg n); simpl in *; tauto.
Qed.

Definition isMLLit (r: mlRelation) (args: list mlTerm): Prop := 
  mlRelArity r = List.map mlTermSort args.

Inductive mlLiteral: Type :=
  MLPApp (nx: nat) (r: mlRelation) (args: list mlTerm) (wf: isMLLit r args).

Inductive mlAtom: Type :=
| MLLiteral (lt: mlLiteral)
| MLNLiteral (lt: mlLiteral)
| MLEq (s: mlSort) (t1: mlTerm) (t2: mlTerm) (hs1: mlTermSort t1 = s) (hs2: mlTermSort t2 = s)
| MLNEq (s: mlSort) (t1: mlTerm) (t2: mlTerm) (hs1: mlTermSort t1 = s) (hs2: mlTermSort t2 = s).

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

Record mlModel := {
  mlAxioms: list mlFormula;
  mlEvents: list mlEvent;
}.

(***
Record mlSignedFormula := { (* A REVOIR: changement de signature *)
  mlSfForm : mlFormula;
}.

Definition mlTransform (m: mlModel) (chk: mlCheck) : option mlSignedFormula.
Admitted.
***)
End MLCervino.

Require Extraction.

Require Import Coq.extraction.ExtrOcamlBasic.

Require Import extraction.ExtrOcamlString.
Extract Inlined Constant String.append => "(^)".
Extract Inlined Constant String.string_dec => "(=)".
Extract Inductive string => "string" [ """""" "(fun (a, b) -> (String.make 1 a) ^ b)"] "(fun e c s -> if s = """" then e else c s.[0] (String.sub s 1 (String.length s - 1)))".

Extract Inductive nat => int [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Extraction "api.ml" MLCervino.
