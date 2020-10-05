
Require Import Coq.Logic.FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import Eqdep_dec.

Require Import foltl.
Require Import dec.
Require Import finite.

Section SubInterp.

  Context {Ts: Type} {Tv: Ts->Type} {Tc: Ts->Type} {Tp: Type}.
  Variable srcSig: @Sig Ts Tv Tc Tp.

  Ltac psemTac :=
    match goal with
      H:psem _ _ ?sa |- psem _ _ ?sa' => assert (sa' = sa) as ae;
          try (rewrite ae; assumption); (apply functional_extensionality_dep; intros)
    end.

  Record subInterp {D1 D2: Dom srcSig} (I1: Interp D1) (I2: Interp D2): Type := {
    si_m: forall s, ssem (Dom:=D1) s -> ssem (Dom:=D2) s;
    si_inj: forall s d1 d2, si_m s d1 = si_m s d2 -> d1 = d2;
    si_c: forall s c, csem (Interp:=I2) c = si_m s (csem (Interp:=I1) c);
    si_p: forall p t a, psem (Interp:=I1) p t a <-> psem (Interp:=I2) p t (fun i => si_m _ (a i))
  }.
  Arguments si_m [_ _ _ _ ]_ _.
  Arguments si_inj [_ _ _ _ ].
  Arguments si_c [_ _ _ _ ].
  Arguments si_p [_ _ _ _ ].

  Lemma subItp_refl: forall {D: Dom srcSig} (Itp: Interp D),
    subInterp Itp Itp.
  Proof.
    intros; split with (si_m:=fun s x => x); intros; auto.
    split; intro; psemTac; auto.
  Qed.

  Definition subEnv {D1 D2: Dom srcSig} {I1: Interp D1} {I2: Interp D2} (si: subInterp I1 I2) (env1: Env srcSig D1) (env2: Env srcSig D2) :=
    forall s v, env2 s v = si_m si s (env1 s v).

  Lemma subEnv_add: forall {D1 D2: Dom srcSig} {I1: Interp D1} {I2: Interp D2} (si: subInterp I1 I2) (env1: Env srcSig D1) (env2: Env srcSig D2) s v d,
    subEnv si env1 env2 ->
      subEnv si (add srcSig v d env1) (add srcSig v (si_m si s d) env2).
  Proof.
    repeat intro.
    unfold add.
    destruct (eq_dec s s0).
    subst s0.
    destruct (eq_dec v v0); auto.
    apply H.
  Qed.
  
  Lemma subEnv_iadd: forall {D1 D2: Dom srcSig} {I1: Interp D1} {I2: Interp D2} (si: subInterp I1 I2) (env1: Env srcSig D1) (env2: Env srcSig D2)
    `(K: Finite) (sk: K->Sort) (vk: forall k, variable (sk k)) (dk: forall k, ssem (sk k)),
    subEnv si env1 env2 ->
      subEnv si (iadd srcSig K sk vk dk env1)
                (iadd srcSig K sk vk (fun k : K => si_m si (sk k) (dk k))
                  env2).
  Proof.
    repeat intro.
    unfold iadd.
    destruct (ex_dec (fun k : K => isEq2 (sk k) (vk k) s v)).
    destruct s0 as [k h].
    simpl in h.
    destruct (eq_dec (sk k) s).
    subst s.
    destruct (eq_dec (vk k) v).
    subst v.
    rewrite (proof_irrelevance _ h eq_refl); auto.
    exfalso.
    apply inj_pair2_eq_dec in h; auto.
    apply eq_dec.
    exfalso.
    injection h; clear h; simpl; intros.
    apply (n H1).
    apply H.
  Qed.
  
  Lemma tm_siSat: forall {D1 D2: Dom srcSig} {I1: Interp D1} {I2: Interp D2} (si: subInterp I1 I2) (env1: Env srcSig D1) (env2: Env srcSig D2) s (tm: term _ s),
    subEnv si env1 env2 ->
      tm_sem srcSig (Itp:=I2) env2 tm = si_m si s (tm_sem srcSig (Itp:=I1) env1 tm).
  Proof.
    intros.
    destruct tm; simpl.
    apply H.
    apply (si_c si).
  Qed.
  
  Lemma lt_siSat: forall {D1 D2: Dom srcSig} {I1: Interp D1} {I2: Interp D2} (si: subInterp I1 I2) (env1: Env srcSig D1) (env2: Env srcSig D2) a t,
    subEnv si env1 env2 ->
      lt_sem srcSig (Itp:=I2) env2 a t <-> lt_sem srcSig (Itp:=I1) env1 a t.
  Proof.
    intros.
    destruct a; simpl in *.
    rewrite (si_p si).
    split; intro.
    psemTac.
    symmetry; apply tm_siSat; auto.
    psemTac.
    apply tm_siSat; auto.
  Qed.

  Lemma at_siSat: forall {D1 D2: Dom srcSig} {I1: Interp D1} {I2: Interp D2} (si: subInterp I1 I2) (env1: Env srcSig D1) (env2: Env srcSig D2) a t,
    subEnv si env1 env2 ->
      at_sem srcSig (Itp:=I2) env2 a t <-> at_sem srcSig (Itp:=I1) env1 a t.
  Proof.
    intros.
    destruct a; simpl in *.
    apply lt_siSat with (si0:=si); auto.
    apply not_iff_compat.
    apply lt_siSat with (si0:=si); now auto.
    rewrite tm_siSat with (si0:=si) (env3:=env1); auto.
    rewrite tm_siSat with (si0:=si) (env3:=env1); auto.
    split; intro.
    apply si_inj in H0; apply H0.
    f_equal; apply H0.
    
    apply not_iff_compat.
    rewrite tm_siSat with (si0:=si) (env3:=env1); auto.
    rewrite tm_siSat with (si0:=si) (env3:=env1); auto.
    split; intro.
    apply si_inj in H0; apply H0.
    f_equal; apply H0.
  Qed.

  Theorem fm_siSat: forall {D1 D2: Dom srcSig} (I1: Interp D1) (I2: Interp D2) (si: subInterp I1 I2) f (env1: Env srcSig D1) (env2: Env srcSig D2) t,
    noEx srcSig f -> subEnv si env1 env2 ->
      fm_sem srcSig (Itp:=I2) env2 f t -> 
        fm_sem srcSig (Itp:=I1) env1 f t.
  Proof.
    induction f; simpl; intros; try tauto.
  - revert H1; apply (at_siSat si); auto.
  - destruct H1.
    split; [revert H1; apply IHf1 | revert H2; apply IHf2]; intros; auto; tauto.
  - destruct H1; [left; revert H1; apply IHf1 | right; revert H1; apply IHf2]; auto; tauto.
  - specialize H1 with (si_m si _ d).
    revert H1; apply IHf; auto.
    apply subEnv_add; auto.
  - destruct H1 as [t' [h1 h2]].
    exists t'; split; auto.
    revert h2; apply IHf; auto.
  - generalize (H1 t' H2); clear H1; intro.
    revert H1; apply IHf; auto.
  Qed.

End SubInterp.
