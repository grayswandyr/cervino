
Require Import Coq.Logic.FunctionalExtensionality.

Require Import dec.
Require Import finite.
Require Import set.
Require Import foltl.

Definition pEnv `{Sg:Sig} (D: Dom Sg) (vs: forall s, SV.set (variable s)) :=
  forall s v, SV.set_In v (vs s) -> ssem s.
    
Definition pAdd `{Sg:Sig} {D: Dom Sg} (env: Env Sg D) {vs: forall s, SV.set (variable s)} (pe: pEnv D vs): Env Sg D :=
 fun s v => match SV.set_In_dec v (vs s) with
                left h => pe s v h
              | right _ => env s v
              end.
  
Lemma pAdd2: forall `{Sg:Sig} {D: Dom Sg} (env: Env Sg D) {vs: forall s, SV.set (variable s)} (pe: pEnv D vs),
    pAdd (pAdd env pe) pe = pAdd env pe.
Proof.
  intros.
  apply functional_extensionality_dep; intro s.
  apply functional_extensionality_dep; intro v.
  unfold pAdd.
  destruct (SV.set_In_dec v (vs s)); auto.
Qed.
