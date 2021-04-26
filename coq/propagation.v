Require Import dec.
Require Import finite.
Require Import foltl.
Require Import fosem.
Require Import vars.
Require Import varset.

Require Import Arith.
Require Import Eqdep_dec.
Include EqNotations.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.

Inductive Closure {T} (R: T -> T -> Prop): T -> T -> Prop :=
  Cl0: forall d1 d2, d1=d2 -> Closure R d1 d2
| ClS: forall d1 d2 d3, R d1 d2 -> Closure R d2 d3 -> Closure R d1 d3.

Section Propagation.

  Context {Ts: Type} {Tv: Ts->Type} {Tc: Ts->Type} {Tp: Type}.
  Variable Sg: @Sig Ts Tv Tc Tp.
  Variable s : Sort.
  Variables u v: variable s.
  Variable uv_ne: v <> u.
  Variable P: formula Sg.
  Variable Pu: not (vsIn Sg u (free Sg P)).
  Variable Pv: not (vsIn Sg v (free Sg P)).

  Lemma neq_uv: (~ isEq2 (U:=variable) s u s v).
  Proof.
    intro.
    inversion H; clear H.
    apply inj_pair2_eq_dec in H1; try apply eq_dec; subst v; now auto.
  Qed.
  
  Lemma neq_vu: (~ isEq2 (U:=variable) s v s u).
  Proof.
    intro.
    inversion H; clear H.
    apply inj_pair2_eq_dec in H1; try apply eq_dec; subst v; now auto.
  Qed.
  
  Class Binary := {
    b_pred: predicate;
    b_arity: pr_arity b_pred = 2;
    b_args: forall i, pr_args b_pred i = s
  }.  

  Definition call (r: Binary) (u v: variable s): formula Sg :=
    Atom Sg (Literal _ (PApp _ 0 b_pred (fun i => rew <-(b_args i) in match (rew b_arity in i : Fin.t 2) return term Sg s with Fin.F1 => Var Sg s u | Fin.FS _ => Var Sg s v end))).
  
  Notation "'[' x ':=' y ']'" := (vsubst Sg x y).
  
  Definition Propagates r (x: variable s) (h: vsIn Sg x (free _ P)) :=
    All Sg s u (All _ s v (Imp _ (call r u v) (G _ (Imp _ ([x:=u] P)  (F _ ([x:=v]P)))))).
  
  Definition AbsClosure r t x (h: vsIn Sg x (free _ P)) :=
    Imp Sg (Propagates r x h) (Propagates t x h).
  
  Variable D: Dom Sg.
  Variable itp: Interp D.
  
  Definition rel (r: Binary) env t x y := fm_sem (Itp:=itp) Sg env (call r x y) t.
  
  Definition call_sem (r: Binary) t (d1 d2: ssem s): Prop :=
    psem b_pred t (fun i => rew <-[ssem](b_args i) in match (rew b_arity in i : Fin.t 2) return ssem s with Fin.F1 => d1 | Fin.FS _ => d2 end).

  Definition isClosure r r' := forall t x y, Closure (call_sem r t) x y <-> call_sem r' t x y.
  
  Lemma rel_sem r env t x y: rel r env t x y <-> call_sem r t (env s x) (env s y).
  Proof.
    unfold rel, call_sem, call; simpl.
    split; intro.
    match goal with
      H: psem _ _ ?f1 |- psem _ _ ?f2 => assert (f1=f2) as Hf; try (rewrite <-Hf; auto)
    end.
    apply functional_extensionality_dep; intro i.
    destruct r; simpl in *.
    revert b_args0 H i.
    unfold eq_rect_r, eq_rect.
    destruct itp; simpl.
    unfold tm_sem; simpl.
    generalize (psem b_pred0); clear psem.
    generalize (pr_args b_pred0).
    generalize b_arity0.
    rewrite b_arity0; intro.
    rewrite (proof_irrelevance _ _ eq_refl); simpl.
    clear b_arity1; intros.
    rewrite (b_args0 i); simpl.
    destruct i; now auto.

    match goal with
      H: psem _ _ ?f1 |- psem _ _ ?f2 => assert (f1=f2) as Hf; try (rewrite <-Hf; auto)
    end.
    apply functional_extensionality_dep; intro i.
    destruct r; simpl in *.
    revert b_args0 H i.
    unfold eq_rect_r, eq_rect.
    destruct itp; simpl.
    unfold tm_sem; simpl.
    generalize (psem b_pred0); clear psem.
    generalize (pr_args b_pred0).
    generalize b_arity0.
    rewrite b_arity0; intro.
    rewrite (proof_irrelevance _ _ eq_refl); simpl.
    clear b_arity1; intros.
    rewrite (b_args0 i); simpl.
    destruct i; now auto.
    
  Qed.

  Definition Propagates_sem {T} (P: nat -> T -> Prop) (R: nat -> T -> T -> Prop) t :=
    forall u v, R t u v -> (forall t', t'>=t -> P t' u -> exists t'', t'' >= t' /\ P t'' v).
  
  Definition AbsClosure_sem {T} (P: nat -> T -> Prop) (R R': nat -> T -> T -> Prop) t :=
    Propagates_sem P R t -> Propagates_sem P R' t.

  Definition isClosure_sem {T}  (R R': nat -> T -> T -> Prop) := 
    forall t x y, Closure (R t) x y <-> R' t x y.
  
  Lemma preTheorem8 {T} (Q: nat -> T -> Prop) (R R': nat -> T -> T -> Prop):
    isClosure_sem R R' -> forall t, AbsClosure_sem Q R R' t.
  Proof.
    unfold isClosure_sem, AbsClosure_sem, Propagates_sem; intros.
    apply H in H1; clear H.
    revert t' H2 H3; induction H1; intros.
    subst d1.
    exists t'; split; now auto.
    
    specialize (H0 _ _ H t' H2 H3).
    destruct H0 as [t'' [h1 h2]].
    assert (t'' >= t) by (apply le_trans with (m:=t'); auto).
    specialize (IHClosure t'' H0 h2).
    destruct IHClosure as [t1 [k1 k2]].
    exists t1; split; auto.
    apply le_trans with (m:=t''); auto.
  Qed.  
  
  Lemma call_sem_equiv: forall env d1 d2 r t,
    fm_sem Sg (add Sg v d2 (add Sg u d1 env)) (call r u v) t <->
      call_sem r t d1 d2.
  Proof.
    intros.
    change (fm_sem Sg (add Sg v d2 (add Sg u d1 env)) (call r u v) t) with
      (rel r (add Sg v d2 (add Sg u d1 env)) t u v).
    rewrite rel_sem.
    rewrite add_eq.
    rewrite add_add_ne_swp; auto.
    rewrite add_eq.
    reflexivity.
    apply neq_vu.
  Qed.
  
  Lemma isClosure_equiv: forall (r r': Binary), 
    isClosure r r' <-> isClosure_sem (call_sem r) (call_sem r').
  Proof.
    unfold isClosure, isClosure_sem; intros.
    reflexivity.
  Qed.
  
  Lemma add_add_ne_swp_eq : forall (env: Env Sg D) s (v1 v2: variable s) d1 d2, v1 <> v2 ->
    add _ v2 d2 (add _ v1 d1 env) s v1 = d1.
  Proof.
    intros.
    rewrite add_add_ne_swp.
    rewrite add_eq; auto.
    intro.
    inversion H0; clear H0.
    apply inj_pair2_eq_dec in H2; subst; auto.
    apply eq_dec.
  Qed.

  (* PaperTheorem 8 *)
  Theorem theorem8: forall r r' env, 
    isClosure r r' -> forall x h t, fm_sem Sg env (AbsClosure r r' x h) t.
  Proof.
    intros.
    apply Imp_sem; intro.
    unfold Propagates in H0|-*.
    rewrite All_sem in *; intro d1.
    rewrite All_sem; intro d2.
    rewrite Imp_sem; intro.
    apply call_sem_equiv in H1.
    generalize (fun d => proj1 (All_sem _ D itp (add Sg u d env) _ _ _  t)  (H0 d)); clear H0; intros.
    setoid_rewrite Imp_sem in H0.
    setoid_rewrite call_sem_equiv in H0.
    setoid_rewrite G_sem in H0; setoid_rewrite G_sem.
    setoid_rewrite Imp_sem in H0; setoid_rewrite Imp_sem.
    setoid_rewrite F_sem in H0; setoid_rewrite F_sem.
    setoid_rewrite <-vsubst_sem in H0; setoid_rewrite <-vsubst_sem.
    setoid_rewrite add_eq in H0; setoid_rewrite add_eq.
    setoid_rewrite add_add_ne_swp_eq; auto.
    set (Q t d := fm_sem Sg (add Sg x d (add Sg v d2 (add Sg u d1 env))) P t).
    change (forall t' : nat, t' >= t -> Q t' d1 ->
                exists t'0 : nat, t'0 >= t' /\ Q t'0 d2).
    apply (preTheorem8 Q (call_sem r) (call_sem r')); auto.

    repeat intro.
    specialize (H0 u0 v0 H2 t' H3).
    rewrite add_add_ne_swp_eq in H0; auto.

    assert (forall t d d1 d2, fm_sem Sg (add Sg x d (add Sg v d1 (add Sg u d2 env))) P t <-> Q t d).
      intros.
      apply fm_sem_equiv; intros; auto.
      destruct (veq_dec Sg v1 x).
      injection e; intros; subst s0.
      apply inj_pair2_eq_dec in e; try apply eq_dec; subst v1.
      now do 2 rewrite add_eq.
      rewrite (add_ne2 _ _ (add Sg v d0 (add Sg u d3 env))); auto.
      rewrite (add_ne2 _ _ (add Sg v d2 (add Sg u d1 env))); auto.
      destruct (veq_dec Sg v1 v).
      injection e; intros; subst s0.
      apply inj_pair2_eq_dec in e; try apply eq_dec; subst v1.
      apply Pv in H5; tauto.
      rewrite (add_ne2 _ _ (add Sg u d3 env)); auto.
      rewrite (add_ne2 _ _ (add Sg u d1 env)); auto.
      destruct (veq_dec Sg v1 u).
      injection e; intros; subst s0.
      apply inj_pair2_eq_dec in e; try apply eq_dec; subst v1.
      apply Pu in H5; tauto.
      repeat rewrite add_ne2; auto.
    rewrite H5 in H0.
    setoid_rewrite H5 in H0.
    apply H0; auto.
  Qed.
  
End Propagation.
