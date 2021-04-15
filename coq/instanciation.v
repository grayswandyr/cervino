Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.

Require Import Arith.
Require Import Eqdep_dec.
Require Import Fin.
Import EqNotations.

Require Import foltl.
Require Import dec.
Require Import finite.
Require Import set.
Require Import varset.
Require Import vars.
Require Import fosem.

Ltac psemTac :=
    match goal with
      H:psem _ _ ?sa |- psem _ _ ?sa' => assert (sa' = sa) as ae;
          try (rewrite ae; assumption); (apply functional_extensionality_dep; intros)
    end.
    
Section Instanciation.
  Context {Ts: Type} {Tv: Ts->Type} {Tc: Ts->Type} {Tp: Type}.
  Variable srcSg: @Sig Ts Tv Tc Tp.
  Variable D: Dom srcSg.
  Variable srcItp : Interp D.
  
  Fixpoint tfrFormula (V: VarSet srcSg) (f: formula srcSg): formula srcSg :=
  match f with
  | FTrue _ => FTrue srcSg
  | FFalse _ => FFalse srcSg
  | Atom _ a => Atom srcSg a
  | And _ f1 f2 => And srcSg (tfrFormula V f1) (tfrFormula V f2)
  | Or _ f1 f2 => Or srcSg (tfrFormula V f1) (tfrFormula V f2)
  | Ex _ s v f => Ex srcSg s v (tfrFormula (vsAdd srcSg v V) f)
  | All _ s v f => 
    if isFO_dec srcSg f then All srcSg s v f
    else 
      And srcSg
        (IAnd srcSg (asFinite (V s)) (fun w => vsubst srcSg v (proj1_sig w) f))
        (IAnd srcSg (constant s) (fun w => csubst srcSg v w f))
  | F _ f => F srcSg (tfrFormula V f)
  | G _ f => G srcSg (tfrFormula V f)
  end.

  Lemma tfr_sem: forall f V env t, fm_sem srcSg env f t -> 
    fm_sem srcSg env (tfrFormula V f) t.
  Proof.
    induction f; simpl; intros; auto; try tauto.
    - destruct H as [H1 H2].
      apply IHf1 with (V:=V) in H1; apply IHf2 with (V:=V) in H2; now auto.
    - destruct H as [H|H]; [apply IHf1 with (V:=V) in H | apply IHf2 with (V:=V) in H]; now auto.
    - destruct H as [d H].
      exists d.
      apply IHf with (V:=(vsAdd srcSg e V)) in H; now auto.
    - destruct (isFO_dec srcSg f).
      apply All_sem; intro.
      apply H.
      apply And_sem; split.
      apply IAnd_sem; intro.
      apply vsubst_sem.
      apply H.
      apply IAnd_sem; intro.
      apply csubst_sem.
      apply H.
    - destruct H as [t' [h H]].
      exists t'; split; now auto.
  Qed.
  
End Instanciation.

(** PaperLemma 3 **)
Lemma Instanciation_sat: forall `(srcSg: Sig) V (f: formula srcSg),
  isSat srcSg f -> isSat srcSg (tfrFormula srcSg V f).
Proof.
  intros.
  destruct H as [D [srcItp [env [t H]]]].
  apply tfr_sem with (V0:=V) in H.
  exists D.
  exists srcItp.
  exists env.
  exists t.
  apply H.
Qed.

