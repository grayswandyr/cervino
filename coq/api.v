(* Add LoadPath "$HOME/COQ/FO-LTL" as Top. *)

Require Import List.
Require Import String.

Definition mlSort := string.

Record mlRelation := {
  mlRelName : string;
  mlRelProfile : list mlSort;
  mlRelArity := List.length mlRelProfile;
}.

Record mlConstant := {
  mlCstName : string;
  mlCstSort : mlSort;
}.

Record mlVar := {
  mlVarId : nat;
  mlVarName: string;
  mlVarSort : mlSort;
}.

Record mlPath := {
  mlTC : mlRelation;
  mlBase : mlRelation;
}.

Record mlSig := {
  mlSorts : list mlSort;
  mlRelations : list mlRelation;
  mlConstants: list mlConstant;
  mlClosures: list mlPath;
}.

Inductive mlTerm : Type :=
  MLVar: mlVar -> mlTerm
| MLCst: mlConstant -> mlTerm.

Inductive mlLiteral: Type :=
  MLPApp: nat -> mlRelation -> list mlTerm -> mlLiteral.

Inductive mlAtom: Type :=
| MLLiteral: mlLiteral -> mlAtom
| MLNLiteral: mlLiteral -> mlAtom
| MLEq: mlSort -> mlTerm -> mlTerm -> mlAtom
| MLNEq: mlSort -> mlTerm -> mlTerm -> mlAtom.

Inductive mlFormula: Type :=
  FTrue: mlFormula
| FFalse: mlFormula
| Atom: mlAtom -> mlFormula
| And: mlFormula -> mlFormula -> mlFormula 
| Or: mlFormula -> mlFormula -> mlFormula
| Ex: mlVar -> mlFormula -> mlFormula
| All: mlVar -> mlFormula -> mlFormula
| F: mlFormula -> mlFormula
| G: mlFormula -> mlFormula.

Definition mlEvMod := list mlTerm.

Record mlEvModify := {
  mlModRel: mlRelation;
  mlModMods : list mlEvMod;
}.

Record mlEvent := {
  mlEvName : string;
  mlEvArgs : list mlVar;
  mlEvBody : mlFormula;
  mlEvModifies : list mlEvModify;
}.

Inductive mlUsing :=
  TEA: mlUsing (* transfo Ex -> Alll avec intro E *)
| TTC: mlRelation -> mlVar -> mlFormula -> mlUsing (* transitive closure *)
| TFC: (mlEvent -> mlFormula) -> mlUsing. (* frame condition *)

Record mlCheck := {
  mlChkName: string;
  mlChkBody: mlFormula;
  mlChkAssumes: mlFormula;
  mlChkUsing: mlUsing;
}.

Record mlModel := {
  mlMySig : mlSig;
  mlAxioms: list mlFormula;
  mlEvents: list mlEvent;
}.

Record mlSignedFormula := {
  mlSfSig : mlSig;
  mlSfForm : mlFormula;
}.

Definition mlTransform (m: mlModel) (chk: mlCheck) : option mlSignedFormula := None.

Require Extraction.

Require Import Coq.extraction.ExtrOcamlBasic.

Require Import extraction.ExtrOcamlString.
Extract Inlined Constant String.append => "(^)".
Extract Inductive string => "string" [ """""" "(fun (a, b) -> (String.make 1 a) ^ b)"] "(fun e c s -> if s = """" then e else c s.[0] (String.sub s 1 (String.length s - 1)))".

Extract Inductive nat => int [ "0" "succ" ] "(fun fO fS n -> if n = 0 then fO () else fS (n - 1))".

Extraction "api.ml" mlTransform.
