
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Eqdep_dec.
Require Import Lia.
Require Import ProofIrrelevance.

Require Import dec.
Require Import finite.
Require Import foltl.
Require Import foltl_diff.
Require Import set.
Require Import itps.
Require Import extend.
Require Import varset.
Require Import vars.
Require Import fosem.

(*
isSatForC Fr (X f) <-> isSatForC Fr f
isSatForC Fr (F f) <-> isSatForC Fr f
isSatForC Fr (Or f g) <-> (isSatForC Fr f \/ isSatForC Fr g)
avec hyp |dom| > nb_vars 
isSatForC (vsUnion Sg (free Sg f) (free Sg g)) (Or Sg f g) <-> (isSatForC (free Sg f) f \/ isSatForC (free Sg g) g)).
isSatForC Fr (And f (X g)) <-> (isSatForC Fr f /\ isSatForC Fr g)
isSatForC (vsRemove v (free f)) (ExD v f) <-> isSatForC (free f) f

|- G (ExD x px & X qx)
|- (ExD x px & X (qx & G (ExD x px & X qx))
|- px & X (qx & G (ExD x px & X qx)
|- px & |- (qx & G (ExD x px & X qx)))
*)

Section EquiSatC.
  Context {Ts: Type} {Tv: Ts->Type} {Tc: Ts->Type} {Tp: Type}.
  Variable Sg: @Sig Ts Tv Tc Tp.

  Variable D: Dom Sg.
  Variable cs: forall s, constant s -> ssem s.
  (* Hyp: domaine assez grand -- sinon LTL sur dom fini *)
  Variable extEnv: VarSet Sg -> VarSet Sg -> Env Sg D -> Env Sg D.

Definition isItpForC (itp: Interp D) := @csem _ _ _ _ _ _ itp = cs.

Definition isUniq (F: VarSet Sg) (env: Env Sg D) :=
  (forall s v1 v2, vsIn Sg v1 F -> vsIn Sg v2 F -> env s v1 = env s v2 -> v1 = v2) /\
  (forall s v c, vsIn Sg v F -> cs s c <> env s v).

  Hypothesis extEnvUniq: forall (F1 F2: VarSet Sg) (env: Env Sg D),
    (isUniq F1 env -> isUniq F2 (extEnv F1 F2 env)) /\
    (forall s v, vsIn Sg v F1 -> env s v = extEnv F1 F2 env s v).

Definition pcomp (F: VarSet Sg) (env1 env2: Env Sg D) : forall s, ssem s -> ssem s  :=
  fun s d => 
    match (ex_dec (F:=asFinite (F s)) (fun v => isEq (env2 s (proj1_sig v)) d)) with
      inleft (exist _ v h) => env1 s (proj1_sig v)
    | _ => d
    end.

Definition pdom (F: VarSet Sg) (env2: Env Sg D) s :=
  SV.image (env2 s) (F s).

Lemma pcomp_inj: forall (F: VarSet Sg) (env1 env2: Env Sg D) (h1: isUniq F env1) (h2: isUniq F env2) s,
  pInjective (pdom F env2 s) (pcomp F env1 env2 s).
Proof.
  repeat intro.
  unfold pcomp in H1.
  match goal with H:match ?cnd with _=>_ end = match ?cnd' with _=>_ end |- _ => destruct cnd; destruct cnd'; auto end.
  destruct s0 as [[v1 k1] l1]; simpl in *.
  destruct s1 as [[v2 k2] l2]; simpl in *.
  apply h1 in H1; auto.
  subst v1.
  subst x; now auto.

  apply SV.InImage_elim in H0.
  destruct H0 as [w [H'1 H'2]].
  destruct (n (exist _ w H'2) (sym_eq H'1)).

  apply SV.InImage_elim in H.
  destruct H as [w [H'1 H'2]].
  destruct (n (exist _ w H'2) (sym_eq H'1)).  
Qed.

Definition icomp (F: VarSet Sg) (env1 env2: Env Sg D) (h1: isUniq F env1) (h2: isUniq F env2) s :=
  extend (pdom F env2 s) (pcomp F env1 env2 s) (pcomp_inj F env1 env2 h1 h2 s).
  
Lemma icomp_suj: forall (F: VarSet Sg) (env1 env2: Env Sg D) (h1: isUniq F env1) (h2: isUniq F env2),
  forall s (d': ssem s), exists d, icomp F env1 env2 h1 h2 s d = d'.
Proof.
  intros.
  generalize (@extend_surj _ (ssem s) (pdom F env2 s) (pcomp F env1 env2 s) (pcomp_inj F env1 env2 h1 h2 s)); intro.
  destruct (H d').
  exists x.
  apply H0.
Qed.

Definition icomp_inv (F: VarSet Sg) (env1 env2: Env Sg D) (h1: isUniq F env1) (h2: isUniq F env2) :=
  fun s =>
      extend_inv (pdom F env2 s) (pcomp F env1 env2 s) (pcomp_inj F env1 env2 h1 h2 s).

Lemma icomp_inj: forall (F: VarSet Sg) (env1 env2: Env Sg D) (h1: isUniq F env1) (h2: isUniq F env2),
  forall s (d d': ssem s), icomp F env1 env2 h1 h2 s d = icomp F env1 env2 h1 h2 s d' -> d = d'.
Proof.
  intros.
  apply (@extend_inj _ (ssem s) (pdom F env2 s) (pcomp F env1 env2 s) (pcomp_inj F env1 env2 h1 h2 s)) in H; auto.  
Qed.

Lemma icomp_inv_inj: forall (F: VarSet Sg) (env1 env2: Env Sg D) (h1: isUniq F env1) (h2: isUniq F env2),
  forall s (d d': ssem s), icomp_inv F env1 env2 h1 h2 s d = icomp_inv F env1 env2 h1 h2 s d' -> d = d'.
Proof.
  intros.
  apply (@extend_inv_inj _ (ssem s) (pdom F env2 s) (pcomp F env1 env2 s) (pcomp_inj F env1 env2 h1 h2 s)) in H; auto.
Qed.

Lemma pcomp_env1: forall F env1 env2 (h2: isUniq F env2),
  forall s v, vsIn Sg v F -> env1 s v = pcomp F env1 env2 s (env2 s v).
Proof.
  intros.
  unfold pcomp.
  match goal with
    |- _=match ?cnd with _=>_ end => destruct cnd; auto
  end.
  destruct s0.
  destruct x; simpl in *; auto.
  apply h2 in d; auto.
  subst x; now auto.
  simpl in *.
  destruct (n (exist _ v H) eq_refl).
Qed.

Lemma icomp_env1: forall F env1 env2 (h1: isUniq F env1) (h2: isUniq F env2),
  forall s v, vsIn Sg v F -> env1 s v = icomp F env1 env2 h1 h2 s (env2 s v).
Proof.
  intros.
  unfold icomp.
  rewrite (@extend_ext _ (ssem s) (pdom F env2 s) (pcomp F env1 env2 s) (pcomp_inj F env1 env2 h1 h2 s)).
  apply pcomp_env1; auto.

  unfold pdom.
  apply SV.InImage_intro with (w:=v); auto.
Qed.

Lemma pcomp_cs: forall env1 env2 F (h2: isUniq F env2),
  forall s v, cs s v = pcomp F env1 env2 s (cs s v).
Proof.
  intros.
  unfold pcomp.
  match goal with |- _=match ?cnd with _=>_ end => destruct cnd; auto end.
  destruct s0; simpl in *.
  destruct x; simpl in *.
  symmetry in d; apply h2 in d; tauto.
Qed.

Lemma icomp_cs: forall env1 env2 F (h1: isUniq F env1) (h2: isUniq F env2),
  forall s v, cs s v = icomp F env1 env2 h1 h2 s (cs s v).
Proof.
  intros.
  unfold icomp.
  symmetry; apply extend_id; repeat intro; auto.
  unfold pdom in H.
  apply SV.InImage_elim in H.
  destruct H as [w [k1 k2]].
  apply h2 in k1; tauto.
  
  apply SV.InImage_elim in H.
  destruct H as [w [k1 k2]].
  
  unfold pcomp in k1.
  match goal with k1: _=match ?cnd with _=>_ end |- _ => destruct cnd; auto end.
  destruct s0; simpl in *.
  destruct x; simpl in *.
  apply h1 in k1; tauto.
  
  unfold pdom in k2.
  apply SV.InImage_elim in k2.
  destruct k2 as [u [l1 l2]].
  subst w.
  apply h2 in l1; tauto.
Qed.

Lemma icomp_inv_cs: forall env1 env2 F (h1: isUniq F env1) (h2: isUniq F env2),
  forall s v, cs s v = icomp_inv F env1 env2 h1 h2 s (cs s v).
Proof.
  intros.
  assert (icomp F env1 env2 h1 h2 s (cs s v) = icomp F env1 env2 h1 h2 s (icomp_inv F env1 env2 h1 h2 s (cs s v))).
  unfold icomp, icomp_inv.
  rewrite extend_inv_r.
  symmetry; apply icomp_cs.
  apply icomp_inj in H; apply H.
Qed.

Lemma icomp_id: forall env1 env2 F (h1: isUniq F env1) (h2: isUniq F env2),
  forall s (d: ssem s),
  (forall v, SV.set_In v (F s) -> env1 s v <> d) -> 
  (forall v, SV.set_In v (F s) -> env2 s v <> d) -> 
    icomp F env1 env2 h1 h2 s d = d.
Proof.
  intros.
  unfold icomp.
  apply extend_id; repeat intro.
  unfold pdom in H1.
  apply SV.InImage_elim in H1.
  destruct H1 as [w [k1 k2]].
  apply H0 in k2.
  symmetry in k1; tauto.

  apply SV.InImage_elim in H1; destruct H1 as [d' [k1 k2]].
  unfold pdom in k2.
  apply SV.InImage_elim in k2; destruct k2 as [w [l1 l2]].
  subst d'.
  rewrite <-pcomp_env1 in k1; auto.
  symmetry in k1; apply H in k1; auto.
Qed.

Lemma icomp_inv_id: forall env1 env2 F (h1: isUniq F env1) (h2: isUniq F env2),
  forall s (d: ssem s),
  (forall v, SV.set_In v (F s) -> env1 s v <> d) -> 
  (forall v, SV.set_In v (F s) -> env2 s v <> d) -> 
    icomp_inv F env1 env2 h1 h2 s d = d.
Proof.
  intros.
  assert (icomp F env1 env2 h1 h2 s (icomp_inv F env1 env2 h1 h2 s d) = icomp F env1 env2 h1 h2 s d).
  unfold icomp, icomp_inv; rewrite extend_inv_r.
  symmetry; apply icomp_id; auto.
  apply icomp_inj in H1; auto.
Qed.

Inductive isSatForC (Fr: VarSet Sg) (f: formula Sg): Prop := 
isSatForC_intro:
  forall 
  (itp : Interp D)
  (env: Env Sg D)
  (t: nat)
  (isI : isItpForC itp)
  (Fs: vsSubset Sg (free Sg f) Fr)
  (isU: isUniq Fr env)
  (isS: fm_sem Sg env f t),
  isSatForC Fr f.
  
Ltac psemTac :=
  match goal with
    H:psem _ _ ?sa |- psem _ _ ?sa' => assert (sa' = sa) as ae;
        try (rewrite ae; assumption); (apply functional_extensionality_dep; intros)
  end.

(*
Notation "f1 =s= f2" := (equi_sat f1 f2) (at level 50, no associativity).
*)

Definition env_swp F env1 env2 (h1: isUniq F env1) (h2: isUniq F env2) (env: Env Sg D): Env Sg D :=
  fun s v => icomp_inv F env1 env2 h1 h2 s (env s v).

Lemma env_swp_add: forall F env1 env2 (h1: isUniq F env1) (h2: isUniq F env2) (env: Env Sg D) s v d,
  add Sg v (icomp_inv F env1 env2 h1 h2 s d)
            (env_swp F env1 env2 h1 h2 env) =
  env_swp F env1 env2 h1 h2 (add Sg v d env).
Proof.
  intros.
  apply functional_extensionality_dep; intro s'.
  apply functional_extensionality_dep; intro w.
  unfold env_swp.
  unfold add.
  destruct (eq_dec s s'); auto.
  subst s'.
  destruct (eq_dec v w); auto.
Qed.

Lemma add_env_swp: forall F env1 env2 (h1: isUniq F env1) (h2: isUniq F env2) (env: Env Sg D) s (v: variable s) d,
  add Sg v d (env_swp F env1 env2 h1 h2 env) =
  env_swp F env1 env2 h1 h2 (add Sg v (icomp F env1 env2 h1 h2 s d) env).
Proof.
  intros.
  apply functional_extensionality_dep; intro s'.
  apply functional_extensionality_dep; intro w.
  unfold env_swp, add.
  destruct (eq_dec s s'); auto.
  subst s'.
  destruct (eq_dec v w); auto.  
  unfold icomp_inv, icomp; rewrite extend_inv_l; auto.
Qed.

Lemma iadd_env_swp: forall F env1 env2 (h1: isUniq F env1) (h2: isUniq F env2) (env: Env Sg D) `(K: Finite) (sk: K -> Sort) (vk: forall k, variable (sk k)) (dk: forall k, ssem (sk k)),
  iadd Sg K sk vk dk (env_swp F env1 env2 h1 h2 env) =
  env_swp F env1 env2 h1 h2 (iadd Sg K sk vk (fun k => icomp F env1 env2 h1 h2 (sk k) (dk k)) env).
Proof.
  intros.
  apply functional_extensionality_dep; intro s'.
  apply functional_extensionality_dep; intro w.
  unfold env_swp.
  unfold iadd.
  match goal with |- match ?cnd with _=>_ end = _ => destruct cnd; auto end.
  destruct s as [k h]; simpl in h.
  injection h; intros; subst s'.
  apply inj_pair2_eq_dec in H; try apply eq_dec.
  subst w; simpl in *.
  rewrite (proof_irrelevance _ _ eq_refl).
  unfold icomp_inv, icomp; rewrite extend_inv_l; auto.
Qed.

Definition itp_fby F env1 env2 (h1: isUniq F env1) (h2: isUniq F env2) (itp1 itp2: Interp D): Interp D := {|
  csem := cs;
  psem p t args := match t with 
    0 => psem (Interp:=itp1) p t (fun i => icomp F env1 env2 h1 h2 _ (args i))
  | S t' => psem (Interp:=itp2) p t args
  end
|}.

Lemma tm_fby0_sem: forall (env1 env2: Env Sg D) s (tm: term Sg s) F (sF: vsSubset Sg (tm_vars Sg tm) F) (h1: isUniq F env1) (h2: isUniq F env2) itp1 itp2 (ih : isItpForC itp1),
  tm_sem (Itp:=itp1) Sg env1 tm = icomp F env1 env2 h1 h2 s (tm_sem (Itp:=itp_fby F env1 env2 h1 h2 itp1 itp2) Sg env2 tm).
Proof.
  intros; destruct tm; simpl in *; auto.
  apply icomp_env1; auto.
  apply sF; apply vsSing_intro.
  rewrite <-icomp_cs; auto.
  rewrite <-ih; auto.
Qed.

Lemma lt_fby0_sem: forall (env1 env2: Env Sg D) (l: literal Sg) F (sF: vsSubset Sg (lt_vars Sg l) F) (h1: isUniq F env1) (h2: isUniq F env2) itp1 itp2 (ih : isItpForC itp1),
  lt_noX Sg l ->
    lt_sem Sg (Itp:=itp_fby F env1 env2 h1 h2 itp1 itp2) env2 l 0 <-> lt_sem Sg (Itp:=itp1) env1 l 0.
Proof.
  intros; destruct l; simpl in *.
  subst n; simpl.
  split; intro; psemTac; clear H.
  apply tm_fby0_sem; auto.
  apply vsSubsetGUnion_elim with (k:=x) in sF.
  apply sF.
  symmetry; apply tm_fby0_sem; auto.
  apply vsSubsetGUnion_elim with (k:=x) in sF.
  apply sF.  
Qed.

Lemma at_fby0_sem: forall (env1 env2: Env Sg D) (a: atom Sg) F (sF: vsSubset Sg (at_vars Sg a) F) (h1: isUniq F env1) (h2: isUniq F env2) itp1 itp2 (ih : isItpForC itp1),
  at_noX Sg a ->
    at_sem Sg (Itp:=itp_fby F env1 env2 h1 h2 itp1 itp2) env2 a 0 <-> at_sem Sg (Itp:=itp1) env1 a 0.
Proof.
  intros; destruct a; simpl; intros; auto.
  apply lt_fby0_sem; now auto.
  apply not_iff_compat; apply lt_fby0_sem; now auto.
  rewrite tm_fby0_sem with (F:=F) (env1:=env1) (env2:=env2) (h1:=h1) (h2:=h2) (itp2:=itp2)(tm:=t); auto.
  rewrite tm_fby0_sem with (F:=F) (env1:=env1) (env2:=env2) (h1:=h1) (h2:=h2) (itp2:=itp2)(tm:=t0); auto.
  split; intro.
  rewrite H0; reflexivity.
  simpl in sF.
  generalize sF; intro sF1.
  apply vsSubsetUnion_elim_l in sF.
  apply vsSubsetUnion_elim_r in sF1.
  
  destruct t; destruct t0; simpl in *;
    try apply vsSubsetSing in sF;
    try apply vsSubsetSing in sF1;
    try rewrite <-icomp_env1 in H0; auto;
    try rewrite <-icomp_env1 in H0; auto;
    try rewrite <-icomp_cs in H0; auto;
    try rewrite <-icomp_cs in H0; auto;
    try apply h1 in H0; subst; auto;
    try tauto;
    try (symmetry in H0; apply h1 in H0; now destruct H0).

  simpl in sF.
  apply vsSubsetUnion_elim_r in sF; apply sF.
  apply vsSubsetUnion_elim_l in sF; apply sF.
  
  apply not_iff_compat.
  rewrite tm_fby0_sem with (F:=F) (env1:=env1) (env2:=env2) (h1:=h1) (h2:=h2) (itp2:=itp2)(tm:=t); auto.
  rewrite tm_fby0_sem with (F:=F) (env1:=env1) (env2:=env2) (h1:=h1) (h2:=h2) (itp2:=itp2)(tm:=t0); auto.
  split; intro.
  rewrite H0; reflexivity.
  simpl in sF.
  generalize sF; intro sF1.
  apply vsSubsetUnion_elim_l in sF.
  apply vsSubsetUnion_elim_r in sF1.
  
  destruct t; destruct t0; simpl in *;
    try apply vsSubsetSing in sF;
    try apply vsSubsetSing in sF1;
    try rewrite <-icomp_env1 in H0; auto;
    try rewrite <-icomp_env1 in H0; auto;
    try rewrite <-icomp_cs in H0; auto;
    try rewrite <-icomp_cs in H0; auto;
    try apply h1 in H0; subst; auto;
    try tauto;
    try (symmetry in H0; apply h1 in H0; now destruct H0).

  simpl in sF.
  apply vsSubsetUnion_elim_r in sF; apply sF.
  apply vsSubsetUnion_elim_l in sF; apply sF.
Qed.

Lemma isUniq_mono: forall F1 F2 env, vsSubset Sg F2 F1 -> isUniq F1 env -> isUniq F2 env.
Proof.
  intros.
  destruct H0.
  split; intros; auto.
  eapply H0 in H4; auto.
  apply H in H2; auto.
  apply H in H3; auto.
  
  apply H1; auto.
  apply H in H2; auto.
Qed.

Lemma X_satC: forall Fr (f: formula Sg), isSatForC Fr (X Sg f) <-> isSatForC Fr f.
Proof.
  intros; split; intro.
  destruct H.
  apply X_sem in isS.
  split with itp env (S t); auto.
  rewrite free_X in Fs; now auto.

  destruct H.
  split with (itp_P itp) env t; auto.
  rewrite free_X; auto.
  apply X_sem.
  apply itp_P_sem; auto.
Qed.

Lemma F_satC: forall (Fr: VarSet Sg) (f: formula Sg), isSatForC Fr (F Sg f) <-> isSatForC Fr f.
Proof.
  intros; split; intros.
  destruct H.
  simpl in isS.
  destruct isS as [t' [_ isS]].
  split with itp env t'; intros; now auto.

  destruct H.
  esplit; eauto.
  exists t.
  split; auto.
Qed.

Lemma Or_satC: forall Fr f g, vsSubset Sg (vsUnion Sg (free Sg f) (free Sg g)) Fr ->
  (isSatForC Fr (Or Sg f g) <-> (isSatForC Fr f \/ isSatForC Fr g)).
Proof.
  intros; split; intro.
  destruct H0.
  apply Or_sem in isS; destruct isS as [isS | isS]; [left|right].
  esplit; eauto.
  intros s v h; apply Fs; rewrite free_Or; apply vsUnion_l; now auto.
  esplit; eauto.
  intros s v h; apply Fs; rewrite free_Or; apply vsUnion_r; now auto.
  
  destruct H0; destruct H0; esplit; eauto.
  
  apply Or_sem; left; apply isS.

  apply Or_sem; right; apply isS.
Qed.

Lemma Or_satC': forall f g,
  (isSatForC (vsUnion Sg (free Sg f) (free Sg g)) (Or Sg f g) <-> (isSatForC (free Sg f) f \/ isSatForC (free Sg g) g)).
Proof.
  intros; split; intro.
  destruct H.
  apply Or_sem in isS; destruct isS as [isS | isS]; [left|right].
  esplit; eauto.
  apply vsSubset_refl.
  revert isU; apply isUniq_mono.
  intros s v h; apply vsUnion_l; apply h.
  esplit; eauto.
  apply vsSubset_refl.
  revert isU; apply isUniq_mono.
  intros s v h; apply vsUnion_r; apply h.

  destruct H; destruct H.
  split with itp (extEnv (free Sg f) (vsUnion Sg (free Sg f) (free Sg g)) env) t; eauto.
  
  apply vsSubset_refl.
  
  revert isU; apply extEnvUniq.
  apply Or_sem; left.
  revert isS; apply fm_sem_equiv; intros.
  symmetry; apply extEnvUniq; now auto.
  
  split with itp (extEnv (free Sg g) (vsUnion Sg (free Sg f) (free Sg g)) env) t; eauto.

  apply vsSubset_refl.
    
  revert isU; apply extEnvUniq.
  apply Or_sem; right.
  revert isS; apply fm_sem_equiv; intros.
  symmetry; apply extEnvUniq; now auto.
Qed.

Lemma And_satC: forall Fr f g, vsSubset Sg (vsUnion Sg (free Sg f) (free Sg g)) Fr ->
  (isSatForC Fr (And Sg f g) -> (isSatForC Fr f /\ isSatForC Fr g)).
Proof.
  intros.
  destruct H0.
  apply And_sem in isS; destruct isS.
  split; esplit; eauto.
  revert Fs; apply vsSubsetUnion_elim_l.
  revert Fs; apply vsSubsetUnion_elim_r.
Qed.

Lemma isUniq_add: forall (itp: Interp D) (ih : isItpForC itp) F env s (v: variable s) (d: ssem s),
  isUniq (vsRemove Sg v F) env -> isNew (SV.remove v (F s)) itp env d -> isUniq F (add Sg v d env).
Proof.
  intros.
  destruct H.
  split; intros; auto.
  unfold add in H4.
  destruct (eq_dec s s0); auto.
  subst s0.
  destruct (eq_dec v v1).
  destruct (eq_dec v v2).
  subst v1; apply e0.
  destruct H0.
  destruct (fun h => H0 v2 h H4).
  apply SV.InRemove; now auto.
  destruct (eq_dec v v2).
  destruct H0.
  symmetry in H4.
  destruct (fun h => H0 v1 h H4).
  apply SV.InRemove; now auto.
  eapply H in H4; auto.
  apply vsInRemove_intro; auto.
  intro; apply n.
  unfold isEq2 in H5; simpl in H5.
  apply inj_pair2_eq_dec in H5; try apply eq_dec; now auto.
  apply vsInRemove_intro; auto.
  intro; apply n0.
  unfold isEq2 in H5; simpl in H5.
  apply inj_pair2_eq_dec in H5; try apply eq_dec; now auto.

  eapply H in H4; auto.
  apply vsInRemove_intro; auto.
  intro; apply n.
  injection H5; intros; now auto.
  apply vsInRemove_intro; auto.
  intro; apply n.
  injection H5; intros; now auto.

  
  unfold add; intro.
  destruct (eq_dec s s0).
  subst s0.
  destruct (eq_dec v v0).
  subst v0.
  destruct H0.
  symmetry in H3; apply (H4 c).
  rewrite <-ih in H3.
  apply H3.

  apply H1 in H3; auto.
  apply vsInRemove_intro; auto.
  intro; apply n.
  unfold isEq2 in H4; simpl in H4; apply inj_pair2_eq_dec in H4; try apply eq_dec; now auto.
  
  apply H1 in H3; auto.
  apply vsInRemove_intro; auto.
  intro; apply n.
  injection H4; intros; auto.
Qed.

Lemma ExD_intro_sem: forall (itp: Interp D) (ih : isItpForC itp)env s v f t,
  fm_sem Sg env f t -> isUniq (free Sg f) env -> vsIn Sg v (free Sg f) ->
    isNew (SV.remove v (free Sg f s)) itp env (env s v) /\
    fm_sem Sg (add Sg v (env s v) env) (ExD v f) t.
Proof.
  intros.
  assert (exists d : ssem s,
        isNew (SV.remove v (free Sg f s)) itp env d /\
        fm_sem Sg (add Sg v d env) f t).
  exists (env s v).
  split; auto.
  split; intros.
  destruct H0.
  intro.
  apply H0 in H4; auto.
  subst w.
  apply SV.InRemove_l in H2; tauto.
  apply SV.InRemove_r in H2; tauto.
  destruct H0.
  rewrite <-ih in H2.
  intro h; symmetry in h; apply H2 in h; now auto.
  apply fm_sem_equiv with (e2:=env); intros; auto.
  unfold add.
  destruct (eq_dec s s0); subst; auto.
  destruct (eq_dec v v0); subst; auto.

  apply ExD_sem in H2.
  split.
  
  split; intros.
  destruct H0.
  intro h; apply H0 in h; intros; auto.
  subst w.
  apply SV.InRemove_l in H3; tauto.
  apply SV.InRemove_r in H3; tauto.
  destruct H0.
  rewrite <-ih in H3.
  intro h; symmetry in h; apply H3 in h; now auto.
  apply fm_sem_equiv with (e2:=env); intros; auto.
  unfold add.
  destruct (eq_dec s s0); subst; auto.
  destruct (eq_dec v v0); subst; auto.
Qed.

Lemma tm_fby0_swp_sem: forall Fr (env1 env2: Env Sg D) (h1:isUniq Fr env1) (h2:isUniq Fr env2) itp1 itp2 (ih : isItpForC itp1) env s (tm: term Sg s),
    (tm_sem Sg (Itp:=itp_fby Fr env1 env2 h1 h2 itp1 itp2) env tm = tm_sem Sg (Itp:=itp1) env tm).
Proof.
  intros.
  destruct tm; simpl in *; auto.
  rewrite <-ih; reflexivity.
Qed.

Lemma lt_fby0_swp_sem: forall Fr (env1 env2: Env Sg D) (h1:isUniq Fr env1) (h2:isUniq Fr env2) itp1 itp2 (ih : isItpForC itp1) env l,
  lt_noX Sg l ->
    (lt_sem Sg (Itp:=itp_fby Fr env1 env2 h1 h2 itp1 itp2) (env_swp Fr env1 env2 h1 h2 env) l 0 <-> lt_sem Sg (Itp:=itp1) env l 0).
Proof.
  intros.
  destruct l; simpl in *.
  subst n; simpl.
  split; intro; psemTac.
  rewrite tm_fby0_swp_sem; auto.
  
  destruct (t x); simpl.
  unfold env_swp.
  unfold icomp, icomp_inv; rewrite extend_inv_r; reflexivity.
  rewrite ih.
  apply icomp_cs; auto.

  destruct (t x); simpl.
  unfold env_swp.
  unfold icomp, icomp_inv; rewrite extend_inv_r; reflexivity.
  rewrite ih.
  symmetry; apply icomp_cs; auto.
Qed.

Lemma at_fby0_swp_sem: forall Fr (env1 env2: Env Sg D) (h1:isUniq Fr env1) (h2:isUniq Fr env2) itp1 itp2 (ih : isItpForC itp1) env a,
  at_noX Sg a ->
    (at_sem Sg (Itp:=itp_fby Fr env1 env2 h1 h2 itp1 itp2) (env_swp Fr env1 env2 h1 h2 env) a 0 <-> at_sem Sg (Itp:=itp1) env a 0).
Proof.
  intros.
  destruct a; simpl.
  apply lt_fby0_swp_sem; now auto.
  apply not_iff_compat; apply lt_fby0_swp_sem; now auto.
  simpl in H.
  rewrite tm_fby0_swp_sem; auto.
  rewrite tm_fby0_swp_sem; auto.

  destruct t; destruct t0; simpl in *.
  unfold env_swp.
  split; intro.
  revert H0; apply icomp_inv_inj; auto.
  rewrite H0; auto.
  rewrite ih.
  split; intro.
  rewrite icomp_inv_cs with (h1:=h1) (h2:=h2) (F:=Fr) in H0; auto.
  apply icomp_inv_inj in H0; now auto.
  rewrite icomp_inv_cs with (h1:=h1) (h2:=h2) (F:=Fr); auto.
  rewrite <-H0; reflexivity.

  rewrite ih.
  split; intro.
  rewrite icomp_inv_cs with (h1:=h1) (h2:=h2) (F:=Fr) in H0; auto.
  apply icomp_inv_inj in H0; now auto.
  rewrite icomp_inv_cs with (h1:=h1) (h2:=h2) (F:=Fr); auto.
  rewrite H0; reflexivity.

  reflexivity.

  apply not_iff_compat.
  destruct t; destruct t0; simpl in *.
  unfold env_swp.
  split; intro.
  revert H0; apply icomp_inv_inj; auto.
  rewrite H0; auto.
  rewrite ih.
  split; intro.
  rewrite icomp_inv_cs with (h1:=h1) (h2:=h2) (F:=Fr) in H0; auto.
  apply icomp_inv_inj in H0; now auto.
  rewrite icomp_inv_cs with (h1:=h1) (h2:=h2) (F:=Fr); auto.
  rewrite <-H0; reflexivity.

  rewrite ih.
  split; intro.
  rewrite icomp_inv_cs with (h1:=h1) (h2:=h2) (F:=Fr) in H0; auto.
  apply icomp_inv_inj in H0; now auto.
  rewrite icomp_inv_cs with (h1:=h1) (h2:=h2) (F:=Fr); auto.
  rewrite H0; reflexivity.

  rewrite ih; reflexivity.
Qed.

Lemma fby0_swp_sem: forall Fr (env1 env2: Env Sg D) (h1:isUniq Fr env1) (h2:isUniq Fr env2) itp1 itp2 (ih : isItpForC itp1) env f,
  isFO Sg f ->
    (fm_sem Sg (Itp:=itp_fby Fr env1 env2 h1 h2 itp1 itp2) (env_swp Fr env1 env2 h1 h2 env) f 0 <-> fm_sem Sg (Itp:=itp1) env f 0).
Proof.
  intros.
  revert H env1 env2 h1 h2 env.
  pattern f; apply formula_ind; intros; try tauto.
  - apply at_fby0_swp_sem; auto.
  - simpl.
    destruct H1.
    rewrite H,H0; auto; reflexivity.
  - simpl.
    destruct H1.
    rewrite H,H0; auto; reflexivity.
  - simpl in H0.
    do 2 rewrite Ex_sem.
    split; intro H1; destruct H1 as [d H1].
    exists (icomp Fr env1 env2 h1 h2 s d).
    rewrite add_env_swp in H1.
    apply H in H1; auto.
    
    exists (icomp_inv Fr env1 env2 h1 h2 s d).
    rewrite add_env_swp.
    apply H; auto.
    fm_semTac.
    unfold icomp,icomp_inv; symmetry; rewrite extend_inv_r; now auto.
  - simpl in H0.
    do 2 rewrite All_sem.
    split; intros H1 d.
    specialize H1 with (icomp_inv Fr env1 env2 h1 h2 s d).
    rewrite add_env_swp in H1.
    apply H in H1; auto.
    fm_semTac.
    unfold icomp,icomp_inv; rewrite extend_inv_r; now auto.

    specialize H1 with (icomp Fr env1 env2 h1 h2 s d).
    rewrite add_env_swp.
    apply H; auto.
Qed.

Lemma swp_env1: forall F (env1 env2: Env Sg D) (h1:isUniq F env1) (h2:isUniq F env2),
  forall s v, SV.set_In v (F s) ->
    env_swp F env1 env2 h1 h2 env1 s v = env2 s v.
Proof.
  intros.
  unfold env_swp.
  rewrite icomp_env1 with (env2:=env2) (F:=F) (h1:=h1) (h2:=h2).
  unfold icomp_inv, icomp; rewrite extend_inv_l; auto.
  apply H.
Qed.

Lemma fby0_sem: forall f (env1 env2: Env Sg D) (h1:isUniq (free Sg f) env1) (h2:isUniq (free Sg f) env2) itp1 itp2 (ih : isItpForC itp1),
  isFO Sg f ->
    (fm_sem Sg (Itp:=itp_fby (free Sg f) env1 env2 h1 h2 itp1 itp2) env2 f 0 <-> fm_sem Sg (Itp:=itp1) env1 f 0).
Proof.
  intros.
  rewrite fm_sem_equiv with (e1:=env2) (e2:=env_swp (free Sg f) env1 env2 h1 h2 env1).
  apply fby0_swp_sem; auto.

  intros.
  symmetry; apply swp_env1; auto.
Qed.

Lemma tm_fbyS_sem: forall Fr (env1 env2: Env Sg D) (h1:isUniq Fr env1) (h2:isUniq Fr env2) itp1 itp2 (ih : isItpForC itp2) env s (tm: term _ s),
    (tm_sem Sg (Itp:=itp_fby Fr env1 env2 h1 h2 itp1 itp2) env tm = tm_sem Sg (Itp:=itp2) env tm).
Proof.
  intros.
  destruct tm; simpl in *; auto.
  rewrite ih; auto.
Qed.

Lemma lt_fbyS_sem: forall Fr (env1 env2: Env Sg D) (h1:isUniq Fr env1) (h2:isUniq Fr env2) itp1 itp2 (ih : isItpForC itp2) env l t,
    (lt_sem Sg (Itp:=itp_fby Fr env1 env2 h1 h2 itp1 itp2) env l (S t) <-> lt_sem Sg (Itp:=itp2) env l (S t)).
Proof.
  intros.
  destruct l; simpl; intros; auto.
  rewrite <-plus_n_Sm.
  split; intro H; psemTac; clear H.
  rewrite tm_fbyS_sem; auto.
  rewrite tm_fbyS_sem; auto.
Qed.

Lemma at_fbyS_sem: forall Fr (env1 env2: Env Sg D) (h1:isUniq Fr env1) (h2:isUniq Fr env2) itp1 itp2 (ih : isItpForC itp2) env a t,
    (at_sem Sg (Itp:=itp_fby Fr env1 env2 h1 h2 itp1 itp2) env a (S t) <-> at_sem Sg (Itp:=itp2) env a (S t)).
Proof.
  intros.
  destruct a; simpl in *.
  apply lt_fbyS_sem; auto.
  apply not_iff_compat; apply lt_fbyS_sem; auto.

  rewrite tm_fbyS_sem; auto.
  rewrite tm_fbyS_sem; auto.
  reflexivity.

  apply not_iff_compat.
  rewrite tm_fbyS_sem; auto.
  rewrite tm_fbyS_sem; auto.
  reflexivity.
Qed.

Lemma fbyS_sem: forall Fr (env1 env2: Env Sg D) (h1:isUniq Fr env1) (h2:isUniq Fr env2) itp1 itp2 (ih : isItpForC itp2) env f t,
  (fm_sem Sg (Itp:=itp_fby Fr env1 env2 h1 h2 itp1 itp2) env f (S t) <-> fm_sem Sg (Itp:=itp2) env f (S t)).
Proof.
  intros.
  revert env1 env2 h1 h2 env t.
  pattern f; apply formula_ind; intros; try tauto.
  - apply at_fbyS_sem; auto.
  - simpl.
    setoid_rewrite H; setoid_rewrite H0; auto.
    reflexivity.
  - simpl.
    setoid_rewrite H; setoid_rewrite H0; auto.
    reflexivity.
  - simpl.
    setoid_rewrite H; auto.
    reflexivity.
  - simpl.
    setoid_rewrite H; auto.
    reflexivity.
  - simpl.
    split; intros.
    destruct H0 as [t' [h3 h4]].
    destruct t'; try lia.
    apply H in h4.
    exists (S t'); split; auto.
    destruct H0 as [t' [h3 h4]].
    exists t'; split; auto.
    destruct t';  try lia.
    apply H; auto.
  - simpl.
    split; intros.
    generalize (H0 t' H1); clear H0; intro.
    destruct t'; try lia.
    apply H in H0; auto.
    generalize (H0 t' H1); clear H0; intro.
    destruct t'; try lia.
    apply H; auto.
Qed.

Lemma PAndX_satC: forall f g Fr, isFO Sg f ->
  isSatForC Fr (And Sg f (X Sg g)) <-> (isSatForC Fr f /\ isSatForC Fr g). 
Proof.
  intros.
  split; intros.
  apply And_satC in H0; destruct H0; auto.
  split; auto.
  apply X_satC; apply H1.
    
  destruct H0.
  destruct H0 as [itp1 env1 t1 isI1 Fs1 isU1 isS1].
  destruct H1 as [itp2 env2 t2 isI2 Fs2 isU2 isS2].
  apply itp_rst_sem in isS1.
  apply itp_rst_sem in isS2.
  apply itp_P_sem in isS2.
  assert (isUniq (free Sg f) env1) as isUf by
    (revert isU1; apply isUniq_mono; auto).
  assert (isUniq (free Sg f) env2) as isUg by
    (revert isU2; apply isUniq_mono; auto).
  split with (itp_fby (free Sg f) env1 env2 isUf isUg (itp_add t1 itp1) (itp_P (itp_add t2 itp2))) env2 0; eauto.
  reflexivity.
  rewrite free_And, free_X.
  
  intros s' v' h'.
  apply SV.InUnion in h'; destruct h'.
  apply Fs1; apply s.
  apply Fs2; apply s.
  
  apply And_sem; split.
  apply fby0_sem; auto.
  apply X_sem.
  apply fbyS_sem; auto.
Qed.

Lemma ExD_satC: forall f s (v: variable s), vsIn Sg v (free Sg f) ->
  isSatForC (free Sg f) f <-> isSatForC (vsRemove Sg v (free Sg f)) (ExD v f).
Proof.
  intros.
  split; intro.
  destruct H0 as [itp env t isI Fs isU isS].
  split with itp env t; auto.
  repeat intro.
  apply free_ExD_sub in H0; auto.
  revert isU; apply isUniq_mono.
  repeat intro.
  apply vsInRemove_elim in H0; tauto.
  
  apply ExD_sem.
  exists (env s v).
  split.
  split; intros.
  intro.
  apply isU in H1; auto.
  subst w.
  apply SV.InRemove_l in H0; tauto.
  apply SV.InRemove_r in H0; tauto.
  intro.
  rewrite isI in H0.
  symmetry in H0; apply isU in H0; tauto.
  fm_semTac.
  unfold add.
  destruct (eq_dec s x); auto.
  subst x.
  destruct (eq_dec v x0); auto.
  subst x0; now auto.
  
  destruct H0 as [itp env t isI Fs isU isS].
  apply ExD_sem in isS.
  destruct isS as [d [h1 h2]].
  split with itp (add Sg v d env) t; auto.
  apply vsSubset_refl.
  apply isUniq_add with (itp:=itp); auto.
Qed.

(*
  LTL
  phi sat ssi prop sat
*)

End EquiSatC.
