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
  
  Lemma tfr_spec: forall f,
      { xT : Sort (Sig:=Sg) -> Type & { xF : forall (s: Sort (Sig:=Sg)), @Finite (xT s) & {f' : formula (cextSig Sg xF) | 
        forall (D: Dom Sg) (itp: Interp D) (env: Env Sg D) t,
          fm_sem Sg (Itp:=itp) env f t ->
            exists (xD: forall s, xT s -> ssem s), fm_sem (cextSig Sg xF) (Itp:=cext_itp Sg itp xF xD) (cext_env Sg xF env) f' t
       }}}.
  Proof.
    induction f; intros; auto.
    - exists (fun s => Empty); exists (fun s => EmptyFin).
      exists (cext_fm (fun s => EmptyFin) (FTrue Sg)).
      intros.
      exists (fun s x => match x in Empty with end).
      revert H; apply cext_sem.
    - exists (fun s => Empty); exists (fun s => EmptyFin).
      exists (cext_fm (fun s => EmptyFin) (FFalse Sg)).
      intros.
      inversion H.
    - exists (fun s => Empty); exists (fun s => EmptyFin).
      exists (cext_fm (fun s => EmptyFin) (Atom Sg a)).
      intros.
      exists (fun s x => match x in Empty with end).
      revert H; apply cext_sem.
    - destruct IHf1 as [xT1 [xF1 [f'1 h1]]].
      destruct IHf2 as [xT2 [xF2 [f'2 h2]]].
      exists (fun s => (xT1 s + xT2 s)%type).
      exists (fun s => SumFin (xF1 s) (xF2 s)).
      exists (And (cext2Sig Sg xF1 xF2) (cinj1_fm Sg xF1 xF2 f'1) (cinj2_fm Sg xF1 xF2 f'2)).
      intros.
      destruct H as [H1 H2].
      apply h1 in H1; clear h1.
      apply h2 in H2; clear h2.
      destruct H1 as [xD1 H1].
      destruct H2 as [xD2 H2].
      exists (fun s c => match c with inl c1 => xD1 s c1 | inr c2 => xD2 s c2 end).
      apply And_sem; split.
      now apply cinj1_sem.
      now apply cinj2_sem.
    - destruct IHf1 as [xT1 [xF1 [f'1 h1]]].
      destruct IHf2 as [xT2 [xF2 [f'2 h2]]].
      exists (fun s => (xT1 s + xT2 s)%type).
      exists (fun s => SumFin (xF1 s) (xF2 s)).
      exists (Or (cext2Sig Sg xF1 xF2) (cinj1_fm Sg xF1 xF2 f'1) (cinj2_fm Sg xF1 xF2 f'2)).
      intros.
      destruct H as [H|H].
      apply h1 in H; destruct H as [xD1 H].
      exists (fun s c => match c with inl c1 => xD1 s c1 | inr c2 => neDom s end).      
      apply Or_sem; left.
      apply cinj1_sem; now apply H.
      apply h2 in H; destruct H as [xD2 H].
      exists (fun s c => match c with inr c2 => xD2 s c2 | inl c1 => neDom s end).
      apply Or_sem; right.
      apply cinj2_sem; now apply H.
    - destruct IHf as [xT [xF [f' H]]].
      set (xT' s' := if eq_dec s s' return Type then One else Empty).
      exists (fun s => (xT' s + xT s)%type).
      set (xF' s' := if eq_dec s s' as e return @Finite (if e then One else Empty) then OneFin else EmptyFin).
      exists (fun s => SumFin (xF' s) (xF s)).
      set (f'' := cinj2_fm Sg xF' xF f').
      set (c := match eq_dec s s as e return if e then OneFin else EmptyFin with
        left e => one
      | right n => match n eq_refl with end
      end).
      exists (csubst (cextSig Sg (fun s => SumFin (xF' s) (xF s))) e (inr (inl c)) f'').
      intros.
      generalize (proj1 (Ex_sem _ _ _ _ s e f t) H0); clear H0; intro.
      destruct H0 as [d H0].
      apply H in H0; clear H.
      destruct H0 as [xD H0].
      set (xD' := fun s' => match eq_dec s' s return xT' s' -> ssem s' with 
        left e => fun c' => rew <-[ssem] e in d 
      | right n => fun c' => neDom s'
      end).
      exists (fun s c => match c with inl c1 => xD' s c1 | inr c2 => xD s c2 end).
      apply csubst_sem.
      apply cinj2_sem with (xF1:=xF') (xD1:=xD') in H0.
      simpl in H0|-*.
      change (cext_env Sg (fun s0 : Sort => SumFin (xF' s0) (xF s0)) env) with env.
      change (cext_env Sg xF (add Sg e d env)) with (add Sg e d env) in H0.
      change (cextSig Sg (fun s0 : Sort => SumFin (xF' s0) (xF s0))) with (cext2Sig Sg xF' xF).
      assert (xD' s c = d).
      unfold xD'; clear H0 xD'.
      unfold xT'.
      destruct (eq_dec s s); try (exfalso; now auto).
      rewrite (proof_irrelevance _ e0 eq_refl); simpl.
      unfold eq_rect_r; reflexivity.
      rewrite H.
      unfold f''.
      revert H0; apply fm_sem_equiv; intros.
      reflexivity.
    - clear IHf.
      exists (fun s => Empty); exists (fun s => EmptyFin).
      exists (cext_fm (fun s => EmptyFin) (All Sg s e f)); intros.
      exists (fun s c => match c in Empty with end).
      revert H; apply cext_sem.
    - destruct IHf as [xT [xF [f' H]]].
      exists xT; exists xF; exists (F _ f'); intros.
      destruct H0 as [t' [ht H0]].
      apply H in H0; clear H.
      destruct H0 as [xD H0].
      exists xD.
      apply F_sem.
      exists t'; split; auto.
    - clear IHf.
      exists (fun s => Empty); exists (fun s => EmptyFin).
      exists (cext_fm (fun s => EmptyFin) (G _ f)); intros.
      exists (fun s c => match c in Empty with end).
      revert H; apply cext_sem.
  Qed.

  Definition sk_Tc (f: formula Sg) : Ts -> Type :=
    fun s => match tfr_spec f with
      existT _ xT _ => (constant s + xT s)%type
    end.

  Definition sk_Fc (f: formula Sg) : forall s, Finite (T:=sk_Tc f s).
  Proof.
    intros.
    unfold sk_Tc.
    destruct (tfr_spec f).
    destruct s0 as [xF _].
    exact (SumFin (constant s) (xF s)).
  Defined.
  
  Definition sk_sg (f: formula Sg): Sig (Ts := Ts) (Tv:=Tv) (Tc:=sk_Fc f) (Tp:=Tp).
  Proof.
    unfold sk_Fc, sk_Tc.
    destruct (tfr_spec f).
    destruct s as [xF _].
    exact (cextSig Sg xF).
  Defined.

  Definition sk_fm (f:formula Sg): formula (sk_sg f).
  Proof.
    unfold sk_sg, sk_Fc, sk_Tc.
    destruct (tfr_spec f) as [xT [xF [f' _]]].
    exact f'.
  Defined.
End Skolem.

(** PaperLemma 2 **)
Lemma skolem_sat: forall `(Sg: Sig) (f: formula Sg),
  isSat Sg f -> isSat (sk_sg Sg f) (sk_fm Sg f).
Proof.
  intros.
  destruct H as [D [itp [env [t h]]]].
  unfold sk_fm, sk_sg, sk_Fc, sk_Tc.
  destruct (tfr_spec Sg f) as [xT [xF [f' H]]].
  specialize (H D itp env t h).
  destruct H as [xD H].
  exists (cext_dom _ _ D).
  exists (cext_itp Sg itp xF xD).
  exists env.
  exists t.
  apply H.
Qed.
