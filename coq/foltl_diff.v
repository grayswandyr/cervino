
Require Import ProofIrrelevance.
Require Import Coq.Logic.JMeq.
Require Import Eqdep_dec.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Classical.

Require Import foltl.
Require Import dec.
Require Import finite.
Require Import set.
Require Import vars.
Require Import varset.
Require Import fosem.

Ltac fm_semTac :=
    match goal with
      H: fm_sem _ ?e1 ?f ?t |- fm_sem _ ?e2 ?f ?t => assert (e1 = e2) as eeq;
        try (rewrite eeq in H; assumption); 
        apply functional_extensionality_dep; intro; 
        apply functional_extensionality_dep; intro
    end.

Definition ExD `{Sg: Sig} {s} (v: variable s) (f: formula Sg) :=
  Ex Sg s v
    (And Sg (IAnd Sg (asFinite (SV.remove v (free Sg f s))) (fun w => Atom Sg (NEq Sg s (Var Sg s v) (Var Sg s (proj1_sig w)))))
             (And Sg 
                  (IAnd Sg (constant s) (fun c => Atom Sg (NEq Sg s (Var Sg s v) (Cst Sg s c))))
                     f)).

Definition AllD `{Sg: Sig} {s} (v: variable s) (f: formula Sg) :=
  All Sg s v
    (Imp Sg (IAnd Sg (asFinite (SV.remove v (free Sg f s))) (fun w => Atom Sg (NEq Sg s (Var Sg s v) (Var Sg s (proj1_sig w)))))
             (Imp Sg 
                  (IAnd Sg (constant s) (fun c => Atom Sg (NEq Sg s (Var Sg s v) (Cst Sg s c))))
                     f)).

Definition isNew `{Sg: Sig} {D: Dom Sg} {s} (F: SV.set (variable s)) (Itp: Interp D) (env: Env Sg D) d :=
  (forall w, SV.set_In w F -> d <> env s w) /\
  (forall c, d <> csem c).

Lemma isNew_mono: forall `(Sg: Sig) D s (F1 F2: SV.set (variable s)) (itp: Interp D) (env: Env Sg D) d,
  SV.subset F1 F2 -> isNew F2 itp env d -> isNew F1 itp env d.
Proof.
  intros.
  destruct H0.
  split; intros; auto.
  apply H0.
  apply H; auto.
Qed.

Lemma ExD_sem: forall `(Sg: Sig) (D: Dom Sg) (Itp: Interp D) env s v f t,
  fm_sem Sg env (ExD v f) t <-> 
    exists (d: ssem s),
      isNew (SV.remove v (free Sg f s)) Itp env d /\
      fm_sem Sg (add Sg v d env) f t.
Proof.
  intros.
  unfold ExD.
  rewrite Ex_sem.
  repeat (setoid_rewrite And_sem || setoid_rewrite IAnd_sem).
  simpl.
  split; intro.
  destruct H as [d [h1 [h2 h3]]].
  exists d; split; auto.
  split; intros.
  specialize h1 with (exist (fun w => SV.set_In w (SV.remove v (free Sg f s))) w H); simpl in h1.
  intro; apply h1; clear h1 h2 h3; subst d.
  rewrite add_eq, add_upd; reflexivity.

  intro; apply (h2 c); clear h1 h2 h3; subst d.
  rewrite add_eq; reflexivity.

  destruct H as [d [[h1 h2] h3]].
  exists d; split; intros; auto.
  destruct k; simpl.
  rewrite add_eq.
  intro; apply (h1 x s0); clear h1 h2 h3.
  destruct (eq_dec x v).
  subst x.
  apply SV.InRemove_l in s0; tauto.
  rewrite add_ne in H; now auto.

  split; intros; auto.
  rewrite add_eq; auto.
Qed.

Lemma AllD_sem: forall `(Sg: Sig) (D: Dom Sg) (Itp: Interp D) env s v f t,
  fm_sem Sg env (AllD v f) t <-> 
    forall (d: ssem s),
      isNew (SV.remove v (free Sg f s)) Itp env d ->
      fm_sem Sg (add Sg v d env) f t.
Proof.
  intros.
  unfold AllD.
  rewrite All_sem.
  do 2 setoid_rewrite Imp_sem.
  setoid_rewrite IAnd_sem.
  simpl.
  split; intros.

  apply (H d); clear H; repeat intro; auto.
  apply proj1 in H0.
  destruct k; simpl in *.
  rewrite add_eq in H.
  generalize s0; intro s1.
  apply SV.InRemove_l in s1.
  apply H0 in s0; apply s0; clear H0 s0.
  rewrite add_ne in H; now auto.
  
  apply proj2 in H0.
  rewrite add_eq in H.
  apply H0 in H; now auto.
  
  apply H; clear H; split; repeat intro; subst d; auto.
  generalize (H0 (exist _ w H)); simpl; clear H0; intro H0.
  rewrite add_eq, add_upd in H0; tauto.
  
  apply (H1 c); clear H0 H1.
  rewrite add_eq; reflexivity.
Qed.

Definition subst `{Sg: Sig} {s} v (tm: term Sg s) (f: formula Sg) :=
  Ex Sg s v (And Sg (Atom Sg (Eq Sg s (Var Sg s v) tm)) f).

Lemma subst_sem: forall `(Sg: Sig) (D: Dom Sg) (Itp: Interp D) env s (v: variable s) tm f t,
  not (SV.set_In v (tm_vars Sg tm s)) ->
    (fm_sem Sg env (subst v tm f) t <-> fm_sem Sg (add Sg v (tm_sem Sg env tm) env) f t).
Proof.
  intros.
  unfold subst.
  rewrite Ex_sem.
  setoid_rewrite And_sem; simpl.
  setoid_rewrite add_eq.
  repeat split; intros; auto.
  destruct H0 as [d [h1 h2]].
  rewrite tm_sem_eq with (e1:=(add Sg v d env)) (e2:=env) in h1.
  rewrite <-h1; now auto.
  
  intros.
  destruct tm; try destruct H0; simpl in H0,H.
  apply vsSing_elim in H0.
  injection H0; intros; subst s0.
  apply inj_pair2_eq_dec in H0; try apply eq_dec; subst v0.
  simpl in h1.
  destruct (eq_dec v e).
  subst e.
  exfalso; apply H; apply vsSing_intro.
  rewrite add_ne in *; now auto.
  
  exists (tm_sem Sg env tm); split; auto.
  apply tm_sem_eq; intros.
  destruct tm; try destruct H0; simpl in H0,H.
  apply vsSing_elim in H1.
  injection H1; intros; subst s0.
  apply inj_pair2_eq_dec in H1; try apply eq_dec; subst v0.
  simpl.
  destruct (eq_dec v e).
  subst e.
  exfalso; apply H; apply vsSing_intro.
  rewrite add_ne in *; now auto.
  simpl in *.
  destruct H1.
Qed.

Lemma free_ExD_sub: forall `{Sg: Sig} s (v: variable s) f, vsSubset Sg (free Sg (ExD v f)) (vsRemove Sg v (free Sg f)).
Proof.
  intros.
  unfold ExD.
  repeat intro.
  rewrite free_Ex in H.
  apply vsInRemove_elim in H; destruct H.
  apply vsInRemove_intro; auto.
  repeat rewrite free_And in H.
  apply vsUnion_elim in H.
  destruct H.
  apply free_IAnd_sub in H.
  simpl in H.
  apply vsGUnion_elim in H.
  destruct H as [k H].
  apply vsUnion_elim in H; destruct H.
  apply vsSing_elim in H.
  exfalso; apply H0; symmetry; apply H.
  apply vsSing_elim in H.
  destruct k; simpl in *.
  injection H; clear H; intros; subst s0.
  apply inj_pair2_eq_dec in H; try apply eq_dec; subst v0.
  apply SV.InRemove_r in s1; apply s1.
  
  apply vsUnion_elim in H; destruct H.
  apply free_IAnd_sub in H.
  apply vsGUnion_elim in H.
  destruct H as [k H].
  apply vsUnion_elim in H; destruct H.
  apply vsSing_elim in H.
  exfalso; apply H0; symmetry; apply H.
  destruct H.
  apply H.
Qed.

Lemma free_ExD_sup: forall `{Sg: Sig} s (v: variable s) f, vsSubset Sg (vsRemove Sg v (free Sg f)) (free Sg (ExD v f)).
Proof.
  intros.
  unfold ExD.
  repeat intro.
  rewrite free_Ex.
  apply vsInRemove_elim in H; destruct H.
  apply vsInRemove_intro; auto.
  rewrite free_And.
  apply vsUnion_r.
  rewrite free_And.
  apply vsUnion_r.
  apply H.
Qed.

Definition Ex' `{Sg: Sig} {s} v (f: formula Sg) :=
  Or Sg
    (IOr Sg (asFinite (SV.remove v (free Sg f s)))
            (fun w => subst v (Var Sg s (proj1_sig w)) f))
    (Or Sg
      (IOr Sg (constant s) (fun c => subst v (Cst Sg s c) f))
      (ExD v f)).

Definition All' `{Sg: Sig} {s} v (f: formula Sg) :=
  And Sg
    (IAnd Sg (asFinite (SV.remove v (free Sg f s)))
            (fun w => subst v (Var Sg s (proj1_sig w)) f))
    (And Sg
      (IAnd Sg (constant s) (fun c => subst v (Cst Sg s c) f))
      (AllD v f)).

Lemma Ex_Ex': forall `(Sg: Sig) (D: Dom Sg) (Itp: Interp D) env s (v: variable s) f t,
  fm_sem Sg env (Ex Sg s v f) t <-> fm_sem Sg env (Ex' v f) t.
Proof.
  intros.
  rewrite Ex_sem.
  unfold Ex'.
  repeat rewrite Or_sem.
  repeat rewrite IOr_sem.
  rewrite ExD_sem.
  unfold subst.
  repeat setoid_rewrite Ex_sem.
  repeat setoid_rewrite And_sem.
  simpl.
  split; intros.
  destruct H as [d H].
  destruct (classic (exists
   (k : {x : variable s |
        SV.set_In x (SV.remove v (free Sg f s))}),
   add Sg v d env s v = add Sg v d env s (proj1_sig k))).
  destruct H0 as [k H0].
  left; exists k; exists d; split; now auto.
  right.
  destruct (classic (exists (k : constant s),
   add Sg v d env s v = csem k)).
  destruct H1 as [k H1].
  left; exists k; exists d; split; now auto.
  right; exists d; split; auto.
  split; repeat intro; subst d; auto.
  apply H0; clear H0.
  exists (exist _ w H2); simpl.
  rewrite add_eq, add_upd; reflexivity.
  apply H1; clear H1.
  exists c; rewrite add_eq; reflexivity.
  
  destruct H as [H | [H | H]].
  destruct H as [k [d [h1 h2]]].
  exists d; now auto.
  destruct H as [k [d [h1 h2]]].
  exists d; now auto.
  destruct H as [d [[h1 h2] h3]].
  exists d; auto.
Qed.

Lemma All_All': forall `(Sg: Sig) (D: Dom Sg) (Itp: Interp D) env s (v: variable s) f t,
  fm_sem Sg env (All Sg s v f) t <-> fm_sem Sg env (All' v f) t.
Proof.
  intros.
  rewrite All_sem.
  unfold All'.
  repeat rewrite And_sem.
  repeat rewrite IAnd_sem.
  rewrite AllD_sem.
  unfold subst.
  repeat setoid_rewrite Ex_sem.
  repeat setoid_rewrite And_sem.
  simpl.
  split; intros.
  
  repeat split; intros.
  destruct k; simpl.
  exists (env s x); split; auto.
  rewrite add_eq, add_upd; reflexivity.
  exists (csem k); split; auto.
  rewrite add_eq; reflexivity.
  apply H.
  
  destruct H as [H1 [H2 H3]].
  destruct (classic (exists
   (k : {x : variable s |
        SV.set_In x (SV.remove v (free Sg f s))}),
   add Sg v d env s v = add Sg v d env s (proj1_sig k))).
  destruct H as [k H].
  destruct (H1 k) as [d' [h1 h2]]; clear H1 H2 H3; intros.
  destruct k; simpl in *.
  rewrite add_eq in H,h1.
  apply SV.InRemove_l in s0.
  rewrite add_ne in H,h1; auto.
  rewrite <-H in h1; subst d'; now auto.
  clear H1.
  destruct (classic (exists k, add Sg v d env s v = csem k)).
  destruct H0 as [c H0].
  destruct (H2 c) as [d' [h1 h2]]; clear H2 H3.
  rewrite add_eq in H0,h1.
  rewrite <-H0 in h1; subst d'; now auto.
  clear H2.
  apply H3; split; repeat intro; subst; auto.
  apply H; clear H H0.
  exists (exist _ w H1); simpl; auto.
  rewrite add_eq, add_upd; reflexivity.
  apply H0; clear H H0.
  exists c; rewrite add_eq; reflexivity.
Qed.

Lemma isFO_ExD: forall `(Sg: Sig) s (v: variable s) (f: formula Sg), isFO Sg (ExD v f) <-> isFO Sg f.
Proof.
  intros.
  unfold ExD.
  rewrite isFO_Ex, isFO_And, isFO_And.
  setoid_rewrite isFO_IAnd.
  simpl.
  tauto.
Qed.

Lemma isFO_AllD: forall `(Sg: Sig) s (v: variable s) (f: formula Sg), isFO Sg (AllD v f) <-> isFO Sg f.
Proof.
  intros.
  unfold AllD.
  rewrite isFO_All, isFO_Imp, isFO_Imp.
  setoid_rewrite isFO_IAnd.
  simpl.
  tauto.
Qed.

Lemma And_IAnd_ind: forall `(Sg: Sig) `(K: Finite) (fk: K -> formula Sg) (P: formula Sg -> Prop),
  (forall f1 f2, P f1 -> P f2 -> P (And Sg f1 f2)) ->
  (forall k, P (fk k)) ->
  P (IAnd Sg K fk).
Proof.
Admitted.

Lemma Or_IOr_ind: forall `(Sg: Sig) `(K: Finite) (fk: K -> formula Sg) (P: formula Sg -> Prop),
  (forall f1 f2, P f1 -> P f2 -> P (Or Sg f1 f2)) ->
  (forall k, P (fk k)) ->
  P (IOr Sg K fk).
Proof.
Admitted.

Lemma ExD_IEx_ind: forall `(Sg: Sig) `(K:Finite) (sk: K -> Sort) (vk: forall k, variable (sk k)) (P: formula Sg -> Prop),
  (forall s (v: variable s) f, P f -> P (ExD v f)) ->
  forall f, P f -> P (IEx Sg K sk vk f).
Proof.
Admitted.

Lemma ExD_Ex_ind: forall `(Sg: Sig) (P: formula Sg -> Prop),
  (forall s (v: variable s) f, P f -> P (ExD v f)) ->
  forall s (v: variable s) f, P f -> P (Ex Sg s v f).
Proof.
Admitted.

Lemma AllD_IAll_ind: forall `(Sg: Sig) `(K:Finite) (sk: K -> Sort) (vk: forall k, variable (sk k)) (P: formula Sg -> Prop),
  (forall s (v: variable s) f, P f -> P (AllD v f)) ->
  forall f, P f -> P (IAll Sg K sk vk f).
Proof.
Admitted.

Lemma All_IAll_ind: forall `(Sg: Sig) `(K:Finite) (sk: K -> Sort) (vk: forall k, variable (sk k)) (P: formula Sg -> Prop),
  (forall s (v: variable s) f, P f -> P (All Sg s v f)) ->
  forall f, P f -> P (IAll Sg K sk vk f).
Proof.
Admitted.

Lemma formulaEXD_ind: forall `(Sg : Sig) (P : formula Sg -> Prop),
  P (FTrue Sg) ->
  P (FFalse Sg) ->
  (forall a : atom Sg, P (Atom Sg a)) ->
  (forall f1 f2, P f1 -> P f2 -> P (And Sg f1 f2)) ->
  (forall f1 f2, P f1 -> P f2 -> P (Or Sg f1 f2)) ->
  (forall s (v: variable s) f, P f -> P (ExD v f)) ->
  (forall s (v: variable s) f, P f -> P (All Sg s v f)) ->
  (forall f, P f -> P (F Sg f)) ->
  (forall f, P f -> P (G Sg f)) ->
  forall f, P f.
Proof.
  intros.
  revert f; apply formula_ind; intros; auto.
  apply ExD_Ex_ind; auto.
Qed.
