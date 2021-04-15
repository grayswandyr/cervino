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
Require Import cextension.

Ltac psemTac :=
    match goal with
      H:psem _ _ ?sa |- psem _ _ ?sa' => assert (sa' = sa) as ae;
          try (rewrite ae; assumption); (apply functional_extensionality_dep; intros)
    end.

Section Skolem.
  Context {Ts: Type} {Tv: Ts->Type} {Tc: Ts->Type} {Tp: Type}.
  Variable Sg: @Sig Ts Tv Tc Tp.
  
  Fixpoint newVarType f : Sort -> Type := 
  match f with
    And _ f1 f2 => fun s => (newVarType f1 s + newVarType f2 s)%type
  | Or _ f1 f2 => fun s => (newVarType f1 s + newVarType f2 s)%type
  | Ex _ s v f' => fun s' => ((if eq_dec s s' then One else Empty) + newVarType  f' s')%type
  | F _ f' => newVarType f'
  | _ => fun s => Empty
  end.

  Fixpoint newVar f : forall s, @Finite (newVarType f s) := 
  match f return forall s, @Finite (newVarType f s) with
    And _ f1 f2 => fun s => SumFin (newVar f1 s) (newVar f2 s)
  | Or _ f1 f2 => fun s => SumFin (newVar f1 s) (newVar f2 s)
  | Ex _ s v f' => fun s' => SumFin (if eq_dec s s' as e return @Finite (if e then One else Empty) then OneFin else EmptyFin) (newVar  f' s')
  | F _ f' => newVar f'
  | _ => fun s => EmptyFin
  end.
  
  Definition sk_sg f := cextSig Sg (newVar f).
  
  Fixpoint sk_fm f : formula (sk_sg f) :=
  match f return formula (sk_sg f) with
    And _ f1 f2 => And (cext2Sig Sg (newVar f1) (newVar f2)) 
      (cinj1_fm Sg (newVar f1) (newVar f2) (sk_fm f1)) 
      (cinj2_fm Sg (newVar f1) (newVar f2) (sk_fm f2)) 
  | Or _ f1 f2 => Or (cext2Sig Sg (newVar f1) (newVar f2)) 
      (cinj1_fm Sg (newVar f1) (newVar f2) (sk_fm f1)) 
      (cinj2_fm Sg (newVar f1) (newVar f2) (sk_fm f2))
  | Ex _ s v f' =>
    let xF' s' := if eq_dec s s' as e return @Finite (if e then One else Empty) then OneFin else EmptyFin in
    let f'' := cinj2_fm Sg xF' (newVar f') (sk_fm f') in 
    let c := match eq_dec s s as e return if e then OneFin else EmptyFin with
        left e => one
      | right n => match n eq_refl with end
      end in
    csubst (cextSig Sg (fun s' => SumFin (xF' s') (newVar f' s'))) v (inr (inl c))  f''
  | F _ f' => F _ (sk_fm f')
  | _ => cext_fm _ f
  end.

  Lemma sk_fm_sem: forall f (D: Dom Sg) (itp: Interp D) (env: Env Sg D) t,
          fm_sem Sg (Itp:=itp) env f t ->
            exists (xD: forall s, newVar f s -> ssem s), fm_sem (cextSig Sg (newVar f)) (Itp:=cext_itp Sg itp (newVar f) xD) (cext_env Sg (newVar f) env) (sk_fm f) t.
  Proof.
    induction f; intros; try (exists (fun s x => match x in Empty with end); auto; revert H; apply cext_sem).
    - destruct H as [H1 H2].
      apply IHf1 in H1; clear IHf1; apply IHf2 in H2; clear IHf2.
      destruct H1 as [xD1 H1]; destruct H2 as [xD2 H2].
      exists (fun s c => match c with inl c1 => xD1 s c1 | inr c2 => xD2 s c2 end).
      apply And_sem; split.
      now apply cinj1_sem.
      now apply cinj2_sem.
    - destruct H as [H1|H2].
      apply IHf1 in H1; clear IHf1.
      destruct H1 as [xD1 H1].
      exists (fun s c => match c with inl c1 => xD1 s c1 | inr c2 => neDom s end).
      left; revert H1; now apply cinj1_sem.
      apply IHf2 in H2; clear IHf2.
      destruct H2 as [xD2 H2].
      exists (fun s c => match c with inr c1 => xD2 s c1 | inl c2 => neDom s end).
      right; revert H2; now apply cinj2_sem.
    - destruct H as [d H].
      apply IHf in H; clear IHf.
      destruct H as [xD H].
      set (xD' := fun s' => match eq_dec s' s return (if eq_dec s s' return Type then One else Empty) -> ssem s' with 
        left e => fun c' => rew <-[ssem] e in d 
      | right n => fun c' => neDom s'
      end).
      exists (fun s' c => match c return ssem s' with inl c1 => xD' s' c1 | inr c2 => xD s' c2 end).
      simpl.
      apply csubst_sem.
      apply cinj2_sem.
      revert H; apply fm_sem_equiv; intros.
      unfold xD'; simpl.
      destruct (eq_dec s s); try tauto.
      rewrite (proof_irrelevance _ e0 eq_refl).
      reflexivity.
    - destruct H as [t' [ht H]].
      apply IHf in H; clear IHf.
      destruct H as [xD H].
      exists xD.
      exists t'; split; auto.
  Qed.
  
End Skolem.

(** PaperLemma 2 **)
Lemma skolem_sat: forall `(Sg: Sig) (f: formula Sg),
  isSat Sg f -> isSat (sk_sg Sg f) (sk_fm Sg f).
Proof.
  intros.
  destruct H as [D [itp [env [t H]]]].
  apply sk_fm_sem in H.
  destruct H as [xD H].
  exists (cext_dom _ _ D).
  exists (cext_itp Sg itp _ xD).
  exists env.
  exists t.
  apply H.
Qed.
