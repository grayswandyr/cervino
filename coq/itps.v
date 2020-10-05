
Require Import Coq.Logic.FunctionalExtensionality.
Require Import foltl.

Definition itp_add `{Sg: Sig} {D: Dom Sg} i (itp: Interp D): Interp D := {|
  csem s c := csem c;
  psem p t args := psem p (i+t) args;
|}.

Definition itp_S `{Sg: Sig} {D: Dom Sg} (itp: Interp D): Interp D := {|
  csem s c := csem c;
  psem p t args := psem p (S t) args;
|}.

Definition itp_P `{Sg: Sig} {D: Dom Sg} (itp: Interp D): Interp D := {|
  csem s c := csem c;
  psem p t args := psem p (pred t) args;
|}.

Lemma tm_itp_add_sem: forall `{Sg: Sig} (D: Dom Sg) env (itp: Interp D) i s (tm: term Sg s),
  tm_sem Sg env tm = tm_sem Sg (Itp:=itp_add i itp) env tm.
Proof.
  intros.
  destruct tm; simpl; auto.
Qed.

Lemma tm_itp_S_sem: forall `{Sg: Sig} (D: Dom Sg) env (itp: Interp D) s (tm: term Sg s),
  tm_sem Sg env tm = tm_sem Sg (Itp:=itp_S itp) env tm.
Proof.
  intros.
  destruct tm; simpl; auto.
Qed.

Lemma tm_itp_P_sem: forall `{Sg: Sig} (D: Dom Sg) env (itp: Interp D) s (tm: term Sg s),
  tm_sem Sg env tm = tm_sem Sg (Itp:=itp_P itp) env tm.
Proof.
  intros.
  destruct tm; simpl; auto.
Qed.

Ltac psemTac :=
  match goal with
    H:psem _ _ ?sa |- psem _ _ ?sa' => assert (sa' = sa) as ae;
        try (rewrite ae; assumption); (apply functional_extensionality_dep; intros)
  end.

Lemma lt_itp_S_sem: forall `{Sg: Sig} (D: Dom Sg) env (itp: Interp D) (l: literal Sg) t,
  lt_sem Sg env l (S t) <-> lt_sem Sg (Itp:=itp_S itp) env l t.
Proof.
  intros.
  destruct l; simpl.
  rewrite plus_n_Sm; simpl.
  split; intro; psemTac.
  rewrite <-tm_itp_S_sem; reflexivity.
  rewrite tm_itp_S_sem; reflexivity.
Qed.

Require Import Lia.

Lemma lt_itp_add_sem: forall `{Sg: Sig} (D: Dom Sg) env (itp: Interp D) i (l: literal Sg) t,
  lt_sem Sg env l (i+t) <-> lt_sem Sg (Itp:=itp_add i itp) env l t.
Proof.
  intros.
  destruct l; simpl.
  assert (n+(i+t) = i+(n+t)) by lia.
  rewrite H; clear H; simpl.
  split; intro; psemTac.
  rewrite <-tm_itp_add_sem; reflexivity.
  rewrite <-tm_itp_add_sem; reflexivity.
Qed.

Lemma lt_itp_P_sem: forall `{Sg: Sig} (D: Dom Sg) env (itp: Interp D) (l: literal Sg) t,
  lt_sem Sg (Itp:=itp_P itp) env l (S t) <-> lt_sem Sg env l t.
Proof.
  intros.
  destruct l; simpl.
  rewrite <-plus_n_Sm; simpl.
  split; intro; psemTac.
  rewrite <-tm_itp_P_sem; reflexivity.
  rewrite <-tm_itp_P_sem; reflexivity.
Qed.

Lemma at_itp_S_sem: forall `{Sg: Sig} (D: Dom Sg) env (itp: Interp D) (a: atom Sg) t,
  at_sem Sg env a (S t) <-> at_sem Sg (Itp:=itp_S itp) env a t.
Proof.
  intros.
  destruct a; simpl; try rewrite lt_itp_S_sem; try reflexivity.
Qed.

Lemma at_itp_add_sem: forall `{Sg: Sig} (D: Dom Sg) env (itp: Interp D) i (a: atom Sg) t,
  at_sem Sg env a (i+t) <-> at_sem Sg (Itp:=itp_add i itp) env a t.
Proof.
  intros.
  destruct a; simpl; try rewrite lt_itp_add_sem; try reflexivity.
Qed.

Lemma at_itp_P_sem: forall `{Sg: Sig} (D: Dom Sg) env (itp: Interp D) (a: atom Sg) t,
  at_sem Sg (Itp:=itp_P itp) env a (S t) <-> at_sem Sg env a t.
Proof.
  intros.
  destruct a; simpl; try rewrite lt_itp_P_sem; try reflexivity.
Qed.

Lemma itp_add_sem: forall `{Sg: Sig} (D: Dom Sg) env (itp: Interp D) (f: formula Sg) i t,
  fm_sem Sg env f (i+t) <-> fm_sem Sg (Itp:=itp_add i itp) env f t.
Proof.
  intros; revert env t.
  induction f; simpl; intros; try rewrite at_itp_add_sem; try reflexivity; try tauto;
    try (setoid_rewrite H; reflexivity);
    try (setoid_rewrite IHf; reflexivity).
  setoid_rewrite <-IHf1; setoid_rewrite <-IHf2; reflexivity.
  setoid_rewrite <-IHf1; setoid_rewrite <-IHf2; reflexivity.

  split; intro.
  destruct H as [t' [h1 h2]].
  exists (t'-i); split; try lia.
  assert (i+(t'-i)=t') by lia.
  rewrite <-H in h2.
  apply IHf in h2; tauto.

  destruct H as [t' [h1 h2]].
  exists (i+t').
  split; try lia; apply IHf; now auto.

  setoid_rewrite <-IHf.
  split; intros.
  apply H; auto with arith.
  specialize H with (t'-i).
  assert (i+(t'-i) = t') by lia.
  rewrite H1 in H; clear H1; apply H.
  lia.
Qed.

Lemma itp_rst_sem: forall `{Sg: Sig} (D: Dom Sg) env (itp: Interp D) (f: formula Sg) t,
  fm_sem Sg env f t <-> fm_sem Sg (Itp:=itp_add t itp) env f 0.
Proof.
  intros.
  rewrite (plus_n_O t).
  rewrite itp_add_sem.
  rewrite <-(plus_n_O t).
  reflexivity.  
Qed.

Lemma itp_S_sem: forall `{Sg: Sig} (D: Dom Sg) env (itp: Interp D) (f: formula Sg) t,
  fm_sem Sg env f (S t) <-> fm_sem Sg (Itp:=itp_S itp) env f t.
Proof.
  intros; revert env t.
  induction f; simpl; intros; try rewrite at_itp_S_sem; try reflexivity; try tauto;
    try (setoid_rewrite H; reflexivity);
    try (setoid_rewrite IHf; reflexivity).
  rewrite IHf1, IHf2; reflexivity.
  rewrite IHf1, IHf2; reflexivity.

  setoid_rewrite <-IHf.
  split; intro.
  destruct H as [t' [h1 h2]].
  destruct t'; try (now inversion h1).
  exists t'; split; simpl; auto.
  apply le_S_n in h1; apply h1.

  destruct H as [t' [h1 h2]].
  exists (S t'); split; auto.
  apply Le.le_n_S; auto.

  setoid_rewrite <-IHf.
  split; intros.
  apply H; auto with arith.
  destruct t'; try (now inversion H0).
  auto with arith.
Qed.

Lemma itp_P_sem: forall `{Sg: Sig} (D: Dom Sg) env (itp: Interp D) (f: formula Sg) t,
  fm_sem Sg (Itp:=itp_P itp) env f (S t) <-> fm_sem Sg env f t.
Proof.
  intros; revert env t.
  induction f; simpl; intros; try rewrite at_itp_P_sem; try reflexivity; try tauto;
    try (setoid_rewrite H; reflexivity);
    try (setoid_rewrite IHf; reflexivity).
  rewrite IHf1, IHf2; reflexivity.
  rewrite IHf1, IHf2; reflexivity.
  
  setoid_rewrite <-IHf.
  split; intro.
  destruct H as [t' [h1 h2]].
  destruct t'; try (now inversion h1).
  exists t'; split; simpl; auto.
  apply le_S_n in h1; apply h1.

  destruct H as [t' [h1 h2]].
  exists (S t'); split; auto.
  apply Le.le_n_S; auto.

  setoid_rewrite <-IHf.
  split; intros.
  apply H; auto with arith.
  destruct t'; try (now inversion H0).
  auto with arith.
Qed.

Notation "f1 =s= f2" := (equi_sat _ f1 f2) (at level 50, no associativity).

Lemma isSat_X: forall `{Sg: Sig} (f: formula Sg),
  (X Sg f) =s= f.
Proof.
  intros; split; intro.
  destruct H as [D [itp [env [t h]]]].
  apply X_sem in h.
  exists D.
  exists (itp_S itp).
  exists env; exists t.
  apply itp_S_sem; auto.
  
  destruct H as [D [itp [env [t h]]]].
  exists D.
  setoid_rewrite X_sem.
  exists (itp_P itp); exists env; exists t.
  apply itp_P_sem; auto.
Qed.

