
Require Import List.
Include ListNotations.
Require Import Coq.Logic.FinFun.
Require Import Lia.
Require Import Coq.Logic.ClassicalEpsilon.
Require Import Classical.

Require Import dec.
Require Import set.
Require Import finite.

Definition pInjective `{T: EqDec} (D: SV.set T) (f: T -> T) :=
  forall x y, SV.set_In x D -> SV.set_In y D -> f x = f y -> x = y.

Lemma pInj_sub: forall `{T: EqDec} {D1 D2: SV.set T} (f: T->T),
  SV.subset D1 D2 -> pInjective D2 f -> pInjective D1 f.
Proof.
  repeat intro; auto.
  apply H0 in H3; auto.
  apply H; auto.
  apply H; auto.
Qed.

Lemma pInj_tl: forall `{T: EqDec} {d: T} {D: SV.set T} (f: T->T),
   pInjective (d::D) f -> pInjective D f.
Proof.
  repeat intro; auto.
  apply H; auto; right; auto.
Qed.

Lemma pInj_hd: forall `{T: EqDec} {d: T} {D: SV.set T} (f: T->T),
   pInjective (d::D) f -> forall x, SV.set_In x D -> x <> d -> f x <> f d.
Proof.
  repeat intro; auto.
  apply H in H2; simpl in *; auto.
Qed.

Lemma pInj_rem: forall `{T: EqDec} {d: T} {D: SV.set T} (h: SV.set_In d D) (f: T->T),
   pInjective D f -> pInjective (SV.remove d D) f.
Proof.
  repeat intro; auto.
  apply H; auto.
  apply SV.InRemove_r in H0; apply H0.
  apply SV.InRemove_r in H1; apply H1.
Qed.

Definition ran `{T:EqDec} (D: SV.set T) (f: T->T) :=
  SV.image f D.

Lemma ran_sub: forall `{T:EqDec} (D1 D2: SV.set T) f,
  SV.subset D1 D2 -> SV.subset (ran D1 f) (ran D2 f).
Proof.
  repeat intro.
  apply SV.InImage_elim in H0.
  destruct H0 as [w [h1 h2]].
  apply SV.InImage_intro with (w0:=w); auto.
  apply H; auto.
Qed.

Definition pSurjective `{T: EqDec} (D: SV.set T) (f: T -> T) :=
  SV.subset D (ran D f).
  
Lemma pSurj_eq: forall `{T: EqDec} (D1 D2: SV.set T) (f: T -> T),
  SV.subset D1 D2 -> SV.subset D2 D1 -> pSurjective D1 f -> pSurjective D2 f.
Proof.
  intros.
  unfold pSurjective in *.
  repeat intro.
  apply H0 in H2; apply H1 in H2.
  apply SV.InImage_elim in H2.
  destruct H2 as [w [h1 h2]].
  apply SV.InImage_intro with (w0:=w); simpl; intros; auto.
  apply H.
  auto.
Qed. 

Definition swap `{T:EqDec} a b (f: T->T):T->T :=
  fun x =>
    if eq_dec x a then f b else if eq_dec x b then f a else f x.

Lemma pInj_swap: forall `{T:EqDec} a b (D: SV.set T) (f:T->T),
  SV.set_In b D -> pInjective (a :: D) f -> pInjective (a::D) (swap a b f).
Proof.
  repeat intro.
  unfold swap in H3.
  simpl in *.
  destruct (eq_dec x a); try subst x; destruct (eq_dec y a); try subst y; auto.
  destruct (eq_dec y b); try (subst y; auto).
  destruct H2; try tauto.
  symmetry in H3; apply H0 in H3; simpl; now auto.
  destruct H1; try (symmetry in H1; tauto).
  destruct (eq_dec x b); try (subst x; auto).
  symmetry; apply H0 in H3; simpl; now auto.
  apply H0 in H3; simpl; now auto.

  destruct (eq_dec x b); try subst x; destruct (eq_dec y b); try subst y; auto.
  symmetry in H3; apply H0 in H3; simpl; tauto.
  apply H0 in H3; simpl; tauto.
Qed.

Lemma pSurj_swap: forall `{T:EqDec} a b (D: SV.set T) (f:T->T),
  SV.set_In (f a) D -> f b = a -> a <> b -> SV.set_In b D -> pSurjective (b :: D) (swap a b f) -> pSurjective (a::D) f.
Proof.
  repeat intro.
  destruct H4.
  subst v.
  
  apply SV.InImage_intro with (w:=b); simpl; auto.
  destruct (eq_dec v b).
  subst v.
  assert (In b (b :: D)) by (left; auto).
  generalize (H3 b H5); clear H5; intro.
  apply SV.InImage_elim in H5.
  destruct H5 as [w [h1 h2]].
  destruct (eq_dec w b); auto.
  apply SV.InImage_intro with (w0:=a); simpl; auto.
  unfold swap in h1.
  destruct (eq_dec w a).
  rewrite <-h1 in H0; symmetry in H0; tauto.
  destruct (eq_dec w b); try tauto.
  apply SV.InImage_intro with (w0:=w); simpl; auto.
  unfold swap in h1.
  destruct (eq_dec w a).
  rewrite <-h1 in H0; symmetry in H0; tauto.
  destruct (eq_dec w b); tauto.
  right.
  destruct h2; try tauto.
  subst b; now auto.
  
  destruct (eq_dec v a).
  subst v.
  apply SV.InImage_intro with (w:=b); auto.
  right; now auto.
  
  assert (In v (b::D)) by (right; auto).
  generalize (H3 v H5); clear H5; intro.
  apply SV.InImage_elim in H5.
  destruct H5 as [w [h1 h2]].
  destruct (eq_dec w a).
  subst w.
  apply SV.InImage_intro with (w:=b); simpl; intros; auto.
  unfold swap in h1.
  destruct (eq_dec a a); tauto.
  destruct (eq_dec w b).
  subst w.
  apply SV.InImage_intro with (w:=a); simpl; intros; auto.
  unfold swap in h1.
  destruct (eq_dec b a); try tauto.
  destruct (eq_dec b b); tauto.
  apply SV.InImage_intro with (w0:=w); simpl; intros; auto.
  unfold swap in h1.
  destruct (eq_dec w a); try tauto.
  destruct (eq_dec w b); try tauto.
  right.
  destruct h2; try tauto.
  symmetry in H5; tauto.
Qed.

Lemma pInj_surj: forall `{T: EqDec} (D: SV.set T) (f: T -> T),
  pInjective D f -> SV.subset (ran D f) D ->
    pSurjective D f.
Proof.
  induction D; simpl; intros; auto.
  destruct (eq_dec (f a) a).
  assert (SV.subset (ran D f) D).
    repeat intro.
    destruct (eq_dec a v).
    subst v.
    apply SV.InImage_elim in H1.
    destruct H1 as [w [h1 h2]].
    rewrite <-e in h1.
    apply H in h1.
    subst w; tauto.
    left; now auto.
    right; now auto.
    assert (In v (a::D)).
    apply H0.
    apply SV.InImage_elim in H1.
    destruct H1 as [w [h1 h2]].
    apply SV.InImage_intro with (w0:=w); simpl; auto.
    destruct H2; tauto.
  apply IHD in H1; auto.
  repeat intro.
  destruct H2.
  subst v.
  apply SV.InImage_intro with (w:=a); intros; simpl; auto.
  generalize (H1 v H2); intro.
  apply ran_sub with D; auto.
  repeat intro; right; now auto.
  revert H; apply pInj_sub.
  repeat intro; right; now auto.
  
  assert (SV.set_In (f a) D).
    assert (In (f a) (a::D)).
    apply H0; clear H0.
    apply SV.InImage_intro with (w:=a); simpl; intros; auto.
    destruct H1; try tauto.
    symmetry in H1; tauto.
  
  destruct (SV.set_In_dec a (ran D f)).
  apply SV.InImage_elim in i.
  destruct i as [b [h1 h2]].
  specialize IHD with (swap a b f).
  generalize H; intro H2.
  apply pInj_swap with (b0:=b) in H2; auto.
  apply pSurj_swap with (b0:=b); auto.
  intro; subst b.
  symmetry in h1; tauto.
  generalize (pInj_hd _ H2); intro.
  apply pInj_tl in H2.
  apply IHD in H2; clear IHD; auto.
  apply pSurj_eq with (D1:=D); auto.
  repeat intro; right; now auto.
  intros x hx; destruct hx; auto; subst x; now auto.
  
  intros x hx.
  apply SV.InImage_elim in hx.
  destruct hx as [w [k1 k2]].
  unfold swap in k1.
  destruct (eq_dec w a).
  subst w.
  rewrite k1,<-h1; now auto.
  destruct (eq_dec w b).
  subst x; now auto.
  subst x.
  assert (In (f w) (ran D f)).
  apply SV.InImage_intro with (w0:=w); auto.
  assert (In (f w) (a::D)).
    apply H0; clear H0.
    apply SV.InImage_intro with (w0:=w); simpl; now auto.
  destruct H5; auto.
  subst a.
  apply H in H5; auto.
  subst w; tauto.
  right; now auto.
  right; now auto.

  assert (SV.subset (ran D f) D).
    repeat intro.
    assert (In v (a::D)).
    apply H0; clear H0.
    apply SV.InImage_elim in H2.
    destruct H2 as [w [h1 h2]].
    apply SV.InImage_intro with (w0:=w); simpl; now auto.
    destruct H3; try tauto.
    subst v; tauto.
  generalize (IHD f (pInj_tl _ H) H2); clear IHD; intro.
  unfold pSurjective in *.
  apply H3 in H1.
  apply SV.InImage_elim in H1.
  destruct H1 as [w [h1 h2]].
  apply H in h1; auto.
  subst w.
  apply H3 in h2; tauto.
  left; now auto.
  right; now auto.
Qed.

Definition pBijective `{T: EqDec} (D: SV.set T) (f: T -> T) :=
  SV.subset (ran D f) D /\ pInjective D f /\ pSurjective D f.

Lemma card_rem_le: forall `{T: EqDec} (D: SV.set T) v,
  SV.card (SV.remove v D) <= SV.card D.
Proof.
  induction D; simpl; intros; auto.
  destruct (eq_dec v a).
  subst a.
  specialize IHD with v.
  auto with arith.
  simpl.
  specialize IHD with v.
  auto with arith.
Qed.

Lemma card_rem_lt: forall `{T: EqDec} (D: SV.set T) v (h: SV.set_In v D),
  SV.card (SV.remove v D) < SV.card D.
Proof.
  induction D; simpl; intros; try tauto.
  destruct (eq_dec v a).
  clear h; subst a.
  unfold lt.
  generalize (card_rem_le D v); intro; auto with arith.

  destruct h; try (subst a; tauto).
  apply IHD in H.
  auto with arith.
Qed.

Lemma card_add_gt: forall `{T: EqDec} x D,
  not (SV.set_In x D) -> SV.card (SV.add x D) > SV.card D.
Proof.
  induction D; simpl; intros; auto.
  destruct (eq_dec x a); auto.
  subst x.
  exfalso; apply H; left; auto.
  simpl.
  destruct (SV.set_In_dec x D); try tauto.
  apply IHD in n0.
  lia.
Qed.

Lemma pInj_add_imp: forall `{T: EqDec} (D: SV.set T) a (f: T->T),
  (forall x : T, SV.set_In (f x) D) -> not (SV.set_In a D) ->
    pInjective (SV.add a D) f -> False.
Proof.
  induction D; simpl; intros; auto.
  destruct (eq_dec a0 a).
  subst a0.
  apply H0; left; now auto.
  
  assert (not (SV.set_In a0 D)).
    destruct (SV.set_In_dec a0 D); now auto.
  clear H0.
  destruct (SV.set_In_dec a D).
  assert (forall x : T, SV.set_In (f x) D).
    intro.
    destruct (H x); clear H; auto.
    subst a; auto.
  apply (IHD a0 f H0 H2); clear IHD.
  revert H1; apply pInj_sub.
  repeat intro.
  right; now auto.
  
  destruct (ex_dec (F:=asFinite D) (fun u => isEq (f (proj1_sig u)) a)).
  destruct s as [[u h1] h2]; simpl in *.
  destruct (SV.set_In_dec (f a) D).
  set (f' x := if eq_dec x u then f a 
              else if SV.set_In_dec x D then f x
              else f a0).
  apply (fun h => IHD a f' h n0); intros; auto.
  unfold f'.
  destruct (eq_dec x u); auto.
  destruct (SV.set_In_dec x D); auto.
  destruct (H x); auto.
  subst a.
  apply H1 in H0; auto.
  subst u; tauto.
  right; apply SV.InAdd_r; tauto.
  right; apply SV.InAdd_r; tauto.
  destruct (H a0); auto.
  subst a.
  apply H1 in H0; auto.
  subst u; tauto.
  right; apply SV.InAdd_r; tauto.
  right; apply SV.InAdd_l.
  repeat intro.
  unfold f' in H4.
  destruct (eq_dec x u); destruct (eq_dec y u); auto.
  subst y; apply e.
  destruct (SV.set_In_dec y D); auto.
  apply H1 in H4; auto.
  subst y; tauto.
  left; tauto.
  right; apply SV.InAdd_r; tauto.
  apply SV.InAdd in H3; destruct H3; try tauto.
  subst y; subst x; clear H0 n2.
  apply H1 in H4; try tauto.
  subst a0; tauto.
  left; now auto.
  right; apply SV.InAdd_l.
  destruct (SV.set_In_dec x D); auto.
  apply H1 in H4; auto.
  subst x; tauto.
  right; apply SV.InAdd_r; tauto.
  left; now auto.
  apply H1 in H4; try tauto.
  right; apply SV.InAdd_l.
  left; now auto.
  apply SV.InAdd in H0; destruct H0.
  subst x.
  destruct (SV.set_In_dec a D); try tauto.
  apply SV.InAdd in H3; destruct H3.
  subst y; tauto.
  destruct (SV.set_In_dec y D); try tauto.
  apply H1 in H4; auto.
  subst y; tauto.
  right; apply SV.InAdd_l.
  right; apply SV.InAdd_r; tauto.
  destruct (SV.set_In_dec x D); try tauto.
  apply SV.InAdd in H3; destruct H3.
  subst y.
  destruct (SV.set_In_dec a D); try tauto.
  apply H1 in H4; try (subst x; tauto).
  right; apply SV.InAdd_r; tauto.
  right; apply SV.InAdd_l.
  destruct (SV.set_In_dec y D); try tauto.
  apply H1 in H4; auto.
  right; apply SV.InAdd_r; tauto.
  right; apply SV.InAdd_r; tauto.

  assert (SV.set_In (f a0) D).
  destruct (H a0); auto.
  subst a.
  apply H1 in H0; try (subst u; tauto).
  right; apply SV.InAdd_r; tauto.
  right; apply SV.InAdd_l.
  
  destruct (H a).
  rewrite H3 in h2.
  apply H1 in h2.
  subst u; tauto.
  right;apply SV.InAdd_r; tauto.
  left; now auto.
  tauto.
  
  assert (exists v, not (SV.set_In v D) /\ SV.set_In (f v) D /\ 
    pInjective (SV.add v D) f).
  destruct (H a).
  destruct (H a0).
  rewrite H0 in H3.
  symmetry in H3; apply H1 in H3; try tauto.
  right; apply SV.InAdd_l.
  left; now auto.
  exists a0; split; auto; split; auto.
  revert H1; apply pInj_sub.
  repeat intro.
  right; apply H1.
  exists a; split; auto; split; auto.
  revert H1; apply pInj_sub.
  repeat intro.
  apply SV.InAdd in H1; destruct H1.
  left; auto.
  right; apply SV.InAdd_r; tauto.
  
  destruct H0 as [v [h1 [h2 h3]]].
  set (f' x := if SV.set_In_dec x D then f x else f v).
  apply (fun h => IHD v f' h h1); intros; auto.
  unfold f'.
  destruct (SV.set_In_dec x D); try tauto.
  destruct (H x); auto.
  generalize (n1 (exist _ x i)); simpl; intro.
  symmetry in H0; tauto.

  repeat intro.
  unfold f' in H4.
  apply SV.InAdd in H0; destruct H0.
  
  subst x.
  destruct (SV.set_In_dec v D); try tauto.
  apply SV.InAdd in H3; destruct H3.
  subst y; now auto.
  destruct (SV.set_In_dec y D); try tauto.
  apply h3 in H4; auto.
  apply SV.InAdd_l.
  apply SV.InAdd_r; tauto.
  destruct (SV.set_In_dec x D); try tauto.
  apply SV.InAdd in H3; destruct H3.
  subst y.
  assert (f x = f v) by (destruct (SV.set_In_dec v D); auto).
  apply h3 in H0; auto.
  apply SV.InAdd_r; tauto.
  apply SV.InAdd_l.
  destruct (SV.set_In_dec y D); try tauto.
  apply h3 in H4; auto.
  apply SV.InAdd_r; tauto.
  apply SV.InAdd_r; tauto.
Qed.

Lemma InRan_cons_elim: forall `{T: EqDec} v a (D: SV.set T) (f: T->T),
  In v (ran (a::D) f) -> v = f a \/ In v (ran D f).
Proof.
  intros.
  apply SV.InImage_elim in H; destruct H as [w [h1 h2]].
  destruct h2; try subst a; auto.
  right.
  apply SV.InImage_intro with (w0:=w); auto.
Qed.

Lemma pInj_pSurj_subr: forall `{T: EqDec} (D: SV.set T) (f: T->T),
  pInjective D f -> pSurjective D f -> SV.subset (ran D f) D.
Proof.
  induction D; simpl; intros; auto.
  destruct (SV.set_In_dec a D).
  assert (pSurjective D f).
    revert H0; apply pSurj_eq.
    repeat intro.
    destruct H0; try subst v; tauto.
    repeat intro; right; tauto.
  apply pInj_tl in H.
  assert (SV.subset (ran D f) D) by (apply IHD; auto).
  repeat intro.
  apply SV.InImage_elim in H3; destruct H3 as [w [h1 h2]].
  destruct h2; try subst w.
  right; apply H2.
  apply SV.InImage_intro with (w:=a); now auto.
  right; apply H2.
  apply SV.InImage_intro with (w0:=w); now auto.

  assert (not (SV.set_In (f a) (ran D f))).
    intro.
    apply SV.InImage_elim in H1; destruct H1 as [w [h1 h2]].
    apply pInj_hd with (x:=w) in H; auto.
    intro; subst w; tauto.
  generalize H; intro pI.
  apply pInj_tl in H.
  destruct (eq_dec (f a) a).
  
  assert (pSurjective D f).
    unfold pSurjective in H0 |-*.
    repeat intro.
    assert (In v (a::D)) by (right; auto).
    apply H0 in H3.
    apply SV.InImage_elim in H3; destruct H3 as [w [h1 h2]].
    destruct h2; try subst w.
    rewrite e in h1; subst v; tauto.
    apply SV.InImage_intro with (w0:=w); now auto.
  assert (SV.subset (ran D f) D) by (apply IHD; auto).
  repeat intro.
  apply InRan_cons_elim in H4; destruct H4; [left|right]; auto.
  subst v; symmetry; now auto.

  generalize (H0 a (or_introl _ eq_refl)); intro.
  apply InRan_cons_elim in H2.
  destruct H2; try (symmetry in H2; tauto).
  apply SV.InImage_elim in H2.
  destruct H2 as [b [h1 h2]].
  
  assert (pSurjective D (swap a b f)).
    repeat intro.
    generalize (H0 v (or_intror _ H2)); intro.
    apply InRan_cons_elim in H3; destruct H3.
    apply SV.InImage_intro with (w:=b); simpl; intros; auto.
    unfold swap.
    destruct (eq_dec b a).
    subst b; tauto.
    destruct (eq_dec b b); tauto.
    apply SV.InImage_elim in H3; destruct H3 as [w [k1 k2]].
    apply SV.InImage_intro with (w0:=w); simpl; auto.
    unfold swap.
    destruct (eq_dec w a); try (subst w; tauto).
    destruct (eq_dec w b); auto.
    subst v; subst w.
    rewrite <-h1 in H2; tauto.

  assert (pInjective D (swap a b f)).
    generalize (pInj_swap a b D f h2 pI); intro.
    apply pInj_tl in H3; apply H3.
  generalize (IHD _ H3 H2); clear H2 H3; intro.

  destruct (SV.set_In_dec (f a) D).

  repeat intro.
  apply InRan_cons_elim in H3.
  destruct H3.
  subst v; right; tauto.
  destruct (eq_dec v a).
  subst v; simpl; tauto.
  right.
  apply H2; clear H2.
  apply SV.InImage_elim in H3.
  destruct H3 as [w [k1 k2]].
  apply SV.InImage_intro with (w0:=w); simpl; auto.
  unfold swap.
  destruct (eq_dec w a); try (subst w; tauto).
  destruct (eq_dec w b); auto.
  subst w; subst v.
  symmetry in h1; tauto.
  
  assert (pSurjective D f).
    repeat intro.
    generalize (H0 v (or_intror _ H3)); intro.
    apply InRan_cons_elim in H4.
    destruct H4; try (subst v; tauto); now auto.

  generalize (IHD f (pInj_tl _ pI) H3 ); clear IHD pI H3; intro.

  repeat intro.
  apply InRan_cons_elim in H4.
  destruct H4.
  right; apply H2.
  apply SV.InImage_intro with (w:=b); simpl; intros; auto.
  unfold swap.
  destruct (eq_dec b a); try (subst b; tauto).
  destruct (eq_dec b b); tauto.
  right; apply H3; auto.
Qed.

Lemma ext_inj_add: forall `{T: EqDec},
  forall D (f: T->T) (pI: pInjective D f) a (inR: SV.set_In a (ran D f)) (nD: not (SV.set_In a D)), exists g, pInjective (SV.add a D) g /\ (forall x, SV.set_In x D -> f x = g x) /\ (SV.set_In (g a) (SV.union D (ran D f))).
Proof.
  intros.
  destruct (classic (pSurjective D f)).
  generalize (pInj_pSurj_subr D f pI H); intro.
  apply H0 in inR; tauto.
  unfold pSurjective in H.
  assert (exists b, SV.set_In b D /\ not (SV.set_In b (ran D f))).
    apply NNPP; intro.
    apply H; clear H.
    repeat intro.
    apply NNPP; intro.
    apply H0; clear H0; exists v; split; now auto.
  destruct H0 as [b [h1 h2]].
  
  exists (fun x => if eq_dec x a then b else f x); repeat split; intros; auto.
  repeat intro.
  destruct (eq_dec x a); try subst x; destruct (eq_dec y a); try subst y; auto.
  apply SV.InAdd in H1; destruct H1; try (subst y; tauto).
  exfalso; apply h2.
  apply SV.InImage_intro with (w:= y); simpl; now auto.
  apply SV.InAdd in H0; destruct H0; try (subst x; tauto).
  exfalso; apply h2.
  apply SV.InImage_intro with (w:= x); simpl; now auto.
  apply pI in H2; auto.
  apply SV.InAdd in H0; destruct H0; tauto.
  apply SV.InAdd in H1; destruct H1; tauto.
  destruct (eq_dec x a); auto; subst x; tauto.
  
  destruct (eq_dec a a); try tauto.
  apply SV.InUnion_l; auto.
Qed.

Lemma ext_inj_set: forall `{T: EqDec},
  forall D' D (f: T->T) (pI: pInjective D f) (disj: SV.disjoint D D') (sub: SV.subset D' (ran D f)), 
    exists g, pInjective (SV.union D D') g /\ (forall x, SV.set_In x D -> f x = g x) /\ SV.subset (SV.union D (ran D' g)) (SV.union D (ran D f)).
Proof.
  induction D'; simpl; intros; auto.
  exists f; repeat split; intros; auto.
  revert pI; apply pInj_sub; intros; auto.
  apply SV.subset_union_empty_r.
  repeat intro.
  apply SV.InUnion in H; try destruct H.
  apply SV.InUnion_l; apply s.
  destruct s.
  
  assert (SV.disjoint D D') as disj'.
    repeat intro.
    apply (disj v); split; try tauto; right; tauto.

  assert (SV.subset D' (ran D f)) as sub'.
    repeat intro.
    apply sub.
    right; now auto.
    
  destruct (IHD' D f pI disj' sub') as [g' [h1 [h2 h3]]].

  destruct (SV.set_In_dec a D').
  
  exists g'; repeat split; intros; auto.
  revert h1; apply pInj_sub; intros; auto.
    repeat intro.
    apply SV.InUnion in H; destruct H.
    apply SV.InUnion_l; now auto.
    apply SV.InUnion_r; simpl in s; destruct s; try subst v; tauto.
    
    repeat intro.
    apply SV.InUnion in H; destruct H.
    apply SV.InUnion_l; now auto.
    apply h3; apply SV.InUnion_r.
    apply InRan_cons_elim in s; destruct s; auto.
    apply SV.InImage_intro with (w:=a); now auto.

  assert (SV.set_In a (ran (SV.union D D') g')).
    assert (In a (ran D f)).
    apply sub; left; now auto.
  assert (In a (ran D g')).
    apply SV.InImage_elim in H; destruct H as [w [k1 k2]].
    apply SV.InImage_intro with (w0:=w); auto.
    rewrite <-h2; now auto.
  apply ran_sub with (D1:=D); auto.
  apply SV.subset_union_l.
  
  assert (~ SV.set_In a (SV.union D D')).
    intro.
    apply SV.InUnion in H0; destruct H0.
    apply (disj a); split; simpl; tauto.
    assert (In a (ran D f)) by (apply sub; left; auto).
  tauto.
  
  destruct (ext_inj_add (SV.union D D') g' h1 a H H0) as [g [k1 [k2 k3]]].
  exists g; repeat split; intros; auto.
  
  revert k1; apply pInj_sub; intros; auto.
    repeat intro.
    apply SV.InUnion in H1; destruct H1.
    apply SV.InAdd_r; apply SV.InUnion_l; now auto.
    destruct s.
    subst v; apply SV.InAdd_l.
    apply SV.InAdd_r; apply SV.InUnion_r; tauto.

  rewrite <-k2; auto.
  apply SV.InUnion_l; now auto.
  
  repeat intro.
  apply SV.InUnion in H1; destruct H1.
  apply SV.InUnion_l; tauto.
  apply InRan_cons_elim in s; destruct s; auto.
  subst v.
  apply SV.InUnion in k3; destruct k3.
  apply SV.InUnion in s; destruct s.
  apply SV.InUnion_l; tauto.
  apply SV.InUnion_r; apply sub'; tauto.
  apply SV.InImage_elim in s; destruct s as [w [l1 l2]].
  rewrite k2 in l1; auto.
  apply k1 in l1; auto.
  subst w; tauto.
  apply SV.InAdd_l.
  apply SV.InAdd_r; tauto.
  
  apply h3.
  apply SV.InUnion_r.
  apply SV.InImage_elim in H1; destruct H1 as [w [l1 l2]].
  apply SV.InImage_intro with (w0:=w); simpl; auto.
  rewrite k2; auto.
  apply SV.InUnion_r; tauto.
Qed.

Lemma uniq_diff: forall `{T:EqDec} (l1 l2: list T),
  uniq l1 -> uniq (SV.diff l1 l2).
Proof.
  induction l1; simpl; intros; auto.
  destruct (in_dec eq_dec a l2).
  apply IHl1.
  apply uniq_tl in H; now auto.
  apply uniq_tl_intro; intros; auto.
  intro.
  apply SV.InDiff_l in H0.
  apply (H (cons a nil) l1 eq_refl a); simpl; intros; auto.
  apply IHl1.
  apply uniq_tl in H; auto.
Qed.

Lemma uniq_union: forall `{T: EqDec} (e1 e2: SV.set T),
  uniq e1 -> uniq e2 -> uniq (SV.union e1 e2).
Proof.
  induction e1; simpl; intros; auto.
  apply SV.uniq_add.
  apply IHe1; auto.
  apply uniq_tl in H.
  auto.
Qed.

Lemma uniq_image: forall `{T1: EqDec} `{T2: EqDec} (f: T1->T2) (e: SV.set T1),
  uniq (SV.image f e).
Proof.
  induction e; simpl; intros; auto.
  apply SV.uniq_empty.
  apply SV.uniq_add; auto.
Qed.

Lemma ext_inj_surj: forall `{T: EqDec},
  forall D (f: T->T) (pI: pInjective D f), 
    exists g, pInjective (SV.union D (ran D f)) g /\
              pSurjective (SV.union D (ran D f)) g /\
              (forall x, SV.set_In x D -> f x = g x).
Proof.
  intros.
  set (F := SV.union D (ran D f)).
  assert (SV.disjoint D (SV.diff F D)).
    repeat intro.
    destruct H.
    apply SV.InDiff_r in H0; tauto.
  
  assert (SV.subset (SV.diff F D) (ran D f)).
    repeat intro.
    generalize H0; intro H1.
    apply SV.InDiff_r in H1.
    apply SV.InDiff_l in H0.
    apply SV.InUnion in H0; destruct H0; tauto.
  
  destruct (ext_inj_set (SV.diff F D) D f pI H H0) as [g [h1 [h2 h3]]].

  exists g; split; intros; auto.
  revert h1; apply pInj_sub.
  repeat intro.
  apply SV.InUnion in H1; destruct H1.
  apply SV.InUnion_l; tauto.
  destruct (SV.set_In_dec v D).
  apply SV.InUnion_l; tauto.
  apply SV.InUnion_r.
  apply SV.InDiff; auto.
  apply SV.InUnion_r; tauto.
  
  split; intros; auto.
  
  apply pInj_surj.
  revert h1; apply pInj_sub.
  repeat intro.
  destruct (SV.set_In_dec v D).
  apply SV.InUnion_l; tauto.
  apply SV.InUnion_r.
  apply SV.InDiff; auto.
  
  repeat intro.
  apply SV.InImage_elim in H1; destruct H1 as [w [k1 k2]].
  destruct (SV.set_In_dec w D).
  apply SV.InUnion_r.
  apply SV.InImage_intro with (w0:=w); simpl; auto.
  rewrite h2; now auto.
  apply SV.InUnion in k2; destruct k2; try tauto.
  apply h3.
  apply SV.InUnion_r.
  apply SV.InImage_intro with (w0:=w); auto.
  apply SV.InDiff; auto.
  apply SV.InUnion_r; auto.
Qed.

Lemma ext_inj: forall `{T: EqDec},
  forall D (f: T->T) (pI: pInjective D f),
    exists g, Injective g /\ Surjective g /\ 
      (forall x, SV.set_In x D -> f x = g x) /\
      (forall x, not (SV.set_In x D) -> not (SV.set_In x (ran D f)) -> g x = x).
Proof.
  intros.
  destruct (ext_inj_surj D f pI) as [f' [h1 [h2 h3]]].
  generalize (pInj_pSurj_subr _ _ h1 h2); intro.
  revert h1 h2 H; set (F:=SV.union D (ran D f)); intros.

  set (g x :=
    match (SV.set_In_dec x F) with
      left h => f' x
    | right h => x
    end).
  exists g; repeat split; intros; auto.
  - repeat intro.
    unfold g in H0; clear g.
    destruct (SV.set_In_dec x F); destruct (SV.set_In_dec y F); auto.
    assert (SV.set_In y (ran F f')).
    apply SV.InImage_intro with (w:= x); auto.
    apply H in H1; tauto.
    assert (SV.set_In x (ran F f')).
    apply SV.InImage_intro with (w:= y); auto.
    apply H in H1; tauto.
  - repeat intro.
    unfold g.
    destruct (SV.set_In_dec y (ran F f')).
    apply SV.InImage_elim in i; destruct i as [x [k1 k2]].
    exists x.
    destruct (SV.set_In_dec x F); try tauto.
    symmetry; tauto.
    exists y.
    destruct (SV.set_In_dec y F); try tauto.
    apply h2 in i; tauto.
  - unfold g; clear g.
    destruct (SV.set_In_dec x F); auto.
    exfalso; apply n; apply SV.InUnion_l; auto.
  - unfold g; clear g.
    destruct (SV.set_In_dec x F); auto.
    apply SV.InUnion in i; destruct i; tauto.
Qed.

Lemma extend_ex: forall `{T: EqDec},
  forall D (f: T->T) (pI: pInjective D f),
    {g | Injective g /\ Surjective g /\ 
        (forall x, SV.set_In x D -> f x = g x) /\
        (forall x, not (SV.set_In x D) -> not (SV.set_In x (ran D f)) -> g x = x)
    }.
Proof.
  intros.
  apply constructive_indefinite_description.
  apply ext_inj; auto.
Qed.

Definition extend `{T: EqDec} D f (pI: pInjective D f): T -> T :=
  proj1_sig (extend_ex D f pI).

Lemma extend_inj: forall `{T: EqDec} (D: SV.set T) f (pI: pInjective D f), Injective (extend D f pI).
Proof.
  intros.
  unfold extend.
  destruct (extend_ex D f pI); simpl; tauto.
Qed.

Lemma extend_surj: forall `{T: EqDec} (D: SV.set T) f (pI: pInjective D f), Surjective (extend D f pI).
Proof.
  intros.
  unfold extend.
  destruct (extend_ex D f pI); simpl; tauto.
Defined.

Lemma extend_ext: forall `{T: EqDec} {D: SV.set T} {f} {pI: pInjective D f}, 
  forall x, SV.set_In x D -> extend D f pI x = f x.
Proof.
  intros.
  unfold extend.
  destruct (extend_ex D f pI); simpl.
  symmetry; apply a; auto.
Qed.

Lemma extend_id: forall `{T: EqDec} {D: SV.set T} {f} {pI: pInjective D f}, 
  forall x, not (SV.set_In x D) -> not (SV.set_In x (ran D f)) -> extend D f pI x = x.
Proof.
  intros.
  unfold extend.
  destruct (extend_ex D f pI); simpl.
  apply a; auto.  
Qed.

Definition extend_inv `{T: EqDec} D f (pI: pInjective D f) : T -> T.
Proof.
  intro y.
  generalize (extend_surj D f pI y); intro.
  apply constructive_indefinite_description in H.
  apply (proj1_sig H).
Defined.

Lemma extend_inv_l: forall `{T: EqDec} {D: SV.set T} f {pI: pInjective D f} x,
  extend_inv D f pI (extend D f pI x) = x.
Proof.
  intros.
  unfold extend_inv.
  generalize (proj2_sig
  (constructive_indefinite_description
     (fun x0 : T => extend D f pI x0 = extend D f pI x)
     (extend_surj D f pI (extend D f pI x)))); intro.
  apply (extend_inj D f pI _ x H).
Qed.

Lemma extend_inv_r: forall `{T: EqDec} {D: SV.set T} f {pI: pInjective D f} x,
  extend D f pI (extend_inv D f pI x) = x.
Proof.
  intros.
  destruct (extend_surj D f pI x) as [y H].
  rewrite <-H.
  rewrite extend_inv_l; auto.
Qed.

Lemma extend_inv_inj: forall `{T: EqDec} {D: SV.set T} f {pI: pInjective D f},
  forall x y, extend_inv D f pI x = extend_inv D f pI y -> x = y.
Proof.
  intros.
  apply f_equal with (f:=extend D f pI) in H.
  do 2 rewrite extend_inv_r in H; auto. 
Qed.
