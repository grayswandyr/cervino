
Require Import ProofIrrelevance.
Require Import Eqdep_dec.

Require Import foltl.
Require Import set.
Require Import dec.
Require Import finite.

Section VarSet.

Context {Ts: Type} {Tv: Ts->Type} {Tc: Ts->Type} {Tp: Type}.
Variable Sg: @Sig Ts Tv Tc Tp.


Definition VarSet := forall s, SV.set (variable s).

Definition vsIn {s} (v: variable s) (F: VarSet) := SV.set_In v (F s).

Lemma vsIn_dec {s} (v: variable s) F : {vsIn v F} + {not (vsIn v F)}.
Proof.
  destruct (SV.set_In_dec v (F s)); [left|right]; auto.
Defined.

Definition vsSubset e1 e2 := forall s, SV.subset (T:=variable s) (e1 s) (e2 s).

Lemma vsSubset_dec e1 e2 : {vsSubset e1 e2} + { not (vsSubset e1 e2) }.
Proof.
  intros.
  unfold vsSubset.
  destruct (all_dec (fun (s: (Sort (Sig:=Sg))) => {| dc_dec := SV.subset_dec (e1 s) (e2 s) |})); simpl in *.
  left; auto.
  destruct s as [s h].
  right; intro.
  apply h; apply H.  
Defined.

Lemma vsSubset_refl : forall e, vsSubset e e.
Proof.
  repeat intro; auto.
Qed.

Lemma vsSubset_trans : forall {e1 e2 e3}, vsSubset e1 e2 -> vsSubset e2 e3 -> vsSubset e1 e3.
Proof.
  repeat intro; auto.
  apply H0.
  apply H.
  auto.
Qed.

Definition vsAdd {s} (v: variable s) (e: VarSet): VarSet :=
  fun s' =>
    match eq_dec s s' with
      left h => match h in _=s' return SV.set (variable s') with 
                  eq_refl => SV.add v (e s)
                end
    | right _ => e s'
    end.

Lemma vsAdd_l: forall {s} (v: variable s) (e: VarSet),
  SV.set_In v (vsAdd v e s).
Proof.
  unfold vsAdd; simpl; intros.
  destruct (eq_dec s s); try tauto.
  rewrite (proof_irrelevance _ e0 eq_refl).
  apply SV.InAdd_l.
Qed.

Lemma vsAdd_r: forall {s s'} (v: variable s) (e: VarSet) {w: variable s'},
  SV.set_In w (e s') -> SV.set_In w (vsAdd v e s').
Proof.
  intros.
  unfold vsAdd.
  destruct (eq_dec s s'); auto.
  subst s'.
  apply SV.InAdd_r; auto.
Qed.

Lemma vsAdd_elim: forall {s s'} (v: variable s) (e: VarSet) {w: variable s'},
  SV.set_In w (vsAdd v e s') -> isEq2 (U:=variable) s' w s v \/ SV.set_In w (e s').
Proof.
  intros.
  unfold vsAdd in H.
  unfold isEq2; simpl.
  destruct (eq_dec s s').
  subst s'.
  apply SV.InAdd in H; destruct H.
  subst v.
  left; auto.
  right; auto.
  right; auto.
Qed.

Lemma vsAdd_ne: forall {s s'} {v: variable s} {e: VarSet} {w: variable s'},
  SV.set_In w (vsAdd v e s') -> not (isEq2 (U:=variable) s' w s v) -> SV.set_In w (e s').
Proof.
  intros.
  apply vsAdd_elim in H.
  destruct H; tauto.
Qed.

Lemma vsAdd_ne2: forall {s s'} {v: variable s} {e: VarSet} {w: variable s'},
  SV.set_In w (vsAdd v e s') -> not (SV.set_In w (e s')) -> (isEq2 (U:=variable) s' w s v).
Proof.
  intros.
  apply vsAdd_elim in H.
  destruct H; tauto.
Qed.

Definition vsEmpty: VarSet := fun s => SV.empty _.

Definition vsSing {s} (v: variable s): VarSet :=
  fun s' =>
    match eq_dec s s' with
      left h => match h in _=s' return SV.set (variable s') with 
                  eq_refl => SV.sing _  v
                end
    | right _ => SV.empty _
    end.

Definition vsUnion (e1 e2: VarSet): VarSet :=
  fun s => SV.union (e1 s) (e2 s).

Lemma vsUnion_l: forall {s v} {e1 e2: VarSet},
  SV.set_In v (e1 s) -> SV.set_In v (vsUnion e1 e2 s).
Proof.
  intros.
  apply SV.InUnion_l; auto.
Qed.

Lemma vsUnion_r: forall {s v} {e1 e2: VarSet},
  SV.set_In v (e2 s) -> SV.set_In v (vsUnion e1 e2 s).
Proof.
  intros.
  apply SV.InUnion_r; auto.
Qed.

Lemma vsUnion_elim: forall {s v} {e1 e2: VarSet},
  SV.set_In v (vsUnion e1 e2 s) -> SV.set_In v (e1 s) \/ SV.set_In v (e2 s).
Proof.
  intros.
  apply SV.InUnion in H.
  destruct H; tauto.
Qed.

Lemma vsUnion_equiv: forall {s} {v: variable s} {e1 e2: VarSet},
  vsIn v (vsUnion e1 e2) <-> vsIn v e1 \/ vsIn v e2.
Proof.
  intros; split; intro.
  apply vsUnion_elim in H; apply H.
  destruct H; [apply vsUnion_l | apply vsUnion_r]; apply H.
Qed.

Definition vsInter (e1 e2: VarSet): VarSet :=
  fun s => SV.inter (e1 s) (e2 s).

Lemma vsInter_intro: forall {s v} {e1 e2: VarSet},
  SV.set_In v (e1 s) -> SV.set_In v (e2 s) -> SV.set_In v (vsInter e1 e2 s).
Proof.
  intros.
  apply SV.InInter; auto.
Qed.

Lemma vsInter_elim: forall {s v} {e1 e2: VarSet},
  SV.set_In v (vsInter e1 e2 s) -> SV.set_In v (e1 s) /\ SV.set_In v (e2 s).
Proof.
  intros; split.
  apply SV.InInter_l in H; auto.
  apply SV.InInter_r in H; auto.
Qed.

Definition vsGUnion `{K: Finite} (ek: K->VarSet): VarSet :=
  fun s => SV.GUnion (T1:=K) (T2:=variable s) fin_set fin_set (fun k _ => ek k s).

Lemma vsGUnion_intro `{K:Finite} {ek: K->VarSet}:
  forall s k, SV.subset (ek k s) (vsGUnion ek s).
Proof.
  repeat intro.
  unfold vsGUnion.
  apply SV.InCUnion_intro with (u:=k); simpl; auto.
  apply fin_all.
  apply fin_all.
Qed.

Lemma vsGUnion_elim `{K:Finite} {ek: K->VarSet} s (v: variable s):
  vsIn v (vsGUnion ek) -> exists k, vsIn v (ek k).
Proof.
  repeat intro.
  unfold vsGUnion in H.
  apply SV.InCUnion_elim in H; simpl; auto.
  destruct H as [k [h1 [h2 h3]]].
  exists k.
  apply h3.
  apply h2.
Qed.

Lemma vsSubsetUnion_elim_l: forall e1 e2 e,
  vsSubset (vsUnion e1 e2) e -> vsSubset e1 e.
Proof.
  repeat intro.
  apply (H s v); clear H; intros.
  apply vsUnion_l; auto.
Qed.

Lemma vsSubsetUnion_elim_r: forall e1 e2 e,
  vsSubset (vsUnion e1 e2) e -> vsSubset e2 e.
Proof.
  repeat intro.
  apply (H s v); clear H; intros.
  apply vsUnion_r; auto.
Qed.

Lemma vsSubsetGUnion_elim `{K:Finite} {ek: K->VarSet} e:
  vsSubset (vsGUnion ek) e -> forall k, vsSubset (ek k) e.
Proof.
  repeat intro.
  unfold vsGUnion.
  apply (H s v); clear H.
  apply SV.InCUnion_intro with (u:=k); simpl; auto.
  apply fin_all.
  apply fin_all.
Qed.

Definition vsRemove {s} (v: variable s) (e: VarSet): VarSet :=
  fun s' => match eq_dec s s' with
    left h =>
      match h in _=s' return SV.set (variable s') with
        eq_refl => SV.remove v (e s)
      end
  | right _ => e s'
  end.

Lemma vsInRemove_intro: forall s (v: variable s) (e: VarSet) s' (w: variable s'),
  vsIn w e -> not (isEq2 (U:=variable) s v s' w) -> vsIn w (vsRemove v e).
Proof.
  intros.
  unfold vsRemove, vsIn; simpl.
  destruct (eq_dec s s'); auto.
  subst s'.
  apply SV.InRemove.
  intro.
  subst w.
  apply H0; reflexivity.
  apply H.
Qed.

Lemma vsInRemove_elim: forall s (v: variable s) (e: VarSet) s' (w: variable s'),
  vsIn w (vsRemove v e) -> vsIn w e /\ not (isEq2 (U:=variable) s v s' w).
Proof.
  intros.
  unfold vsRemove, vsIn in H.
  destruct (eq_dec s s'); auto.
  subst s'.
  split.
  apply SV.InRemove_r in H; apply H.
  apply SV.InRemove_l in H.
  simpl; intro.
  apply H; clear H.
  apply inj_pair2_eq_dec in H0; try apply eq_dec.
  symmetry; apply H0.

  split.
  apply H.
  intro; apply n; clear n.
  injection H0; intro; auto.  
Qed.

Lemma vsRemove_equiv: forall {s} {v: variable s} {e: VarSet} s' (v': variable s'),
  vsIn v' (vsRemove v e) <-> vsIn v' e /\ not (isEq2 (U:=variable) s v s' v').
Proof.
  intros; split; intro.
  apply vsInRemove_elim in H; apply H.
  apply vsInRemove_intro; tauto.
Qed.

Definition vsFinite (vs: VarSet): Finite :=
  DepPairFin Sort (fun s => asFinite (vs s)).

Lemma vsSing_intro: forall s v, SV.set_In v (vsSing v s).
Proof.
  intros.
  unfold vsSing.
  destruct (eq_dec s s); try tauto.
  rewrite (proof_irrelevance _ e eq_refl).
  left; auto.
Qed.

Lemma vsSing_intro_eq: forall s (v: variable s) s' (w: variable s'), isEq2 (U:=variable) s v s' w -> vsIn v (vsSing w).
Proof.
  intros.
  unfold vsSing, vsIn.
  destruct (eq_dec s' s); try tauto.
  subst s'.
  left.
  apply inj_pair2_eq_dec in H; try apply eq_dec.
  symmetry; assumption.
  exfalso; apply n.
  injection H; intros; auto.
Qed.

Lemma vsSing_elim: forall s (v: variable s) s' (w: variable s'), 
  SV.set_In v (vsSing w s) -> isEq2 (U:=variable) s v s' w.
Proof.
  intros.
  unfold vsSing in H.
  unfold isEq2; simpl.
  destruct (eq_dec s' s); try tauto; subst.
  destruct H; try tauto; subst; auto.
Qed.

Lemma vsSubsetSing: forall {s} {v: variable s} e, vsSubset (vsSing v) e -> SV.set_In v (e s).
Proof.
  intros.
  apply SV.subset_sing; repeat intro.
  generalize (H s v0); intro.
  apply H1.
  destruct H0.
  subst v0.
  apply vsSing_intro.
  destruct H0.
Qed.

Lemma vsSubsetSing_r: forall {s} {v: variable s} e, vsSubset e (vsSing v) -> forall s' (w: variable s'), vsIn w e -> isEq2 (U:=variable) s' w s v.
Proof.
  intros.
  generalize (H _ w H0); clear H; intro.
  apply vsSing_elim in H; auto.
Qed.

Definition vsVars `{K: Finite} {sk: K->Sort} (vk: forall k, variable (sk k)) : VarSet :=
  vsGUnion (fun k => vsSing (vk k)).

Lemma vsVars_intro: forall `{K: Finite} {sk: K->Sort} (vk: forall k, variable (sk k)),
  forall k, SV.set_In (vk k) (vsVars vk (sk k)).
Proof.
  intros.
  apply SV.InCUnion_intro with (u:=k); auto.
  apply fin_all; simpl; intros; auto.
  apply fin_all.
  intro.
  apply vsSing_intro.
Qed.

Lemma vsVars_elim: forall `{K: Finite} {sk: K->Sort} (vk: forall k, variable (sk k)),
  forall s (v: variable s), SV.set_In v (vsVars vk s) -> exists k, isEq2 (U:=variable) (sk k) (vk k) s v.
Proof.
  intros.
  unfold vsVars in H.
  apply SV.InCUnion_elim in H.
  destruct H as [u [h1 [h2 h3]]].
  exists u; unfold isEq2; simpl.
  apply h3 in h2; clear h3.
  apply vsSing_elim in h2.
  symmetry; apply h2.
Qed.

End VarSet.

Require Import Coq.Logic.FunctionalExtensionality.

Section VSMap.
  Context {Ts: Type}.
  Context `{srcSig: Sig (Ts:=Ts)}.
  Context `{dstSig: Sig (Ts:=Ts)}.
  Variable f : forall s, variable (Sig:=srcSig) s -> variable (Sig:=dstSig) s.
  
  Definition vsMap e: VarSet dstSig := fun s => List.map (f s) (e s).
  
  Lemma vsSubset_map: forall {e1 e2}, vsSubset srcSig e1 e2 -> vsSubset dstSig (vsMap e1) (vsMap e2).
  Proof.
    unfold vsMap; repeat intro.
    apply List.in_map_iff in H0.
    destruct H0 as [x [h1 h2]]; subst v.
    apply List.in_map_iff.
    exists x; split; auto.
    apply H in h2; auto.
  Qed.

  Lemma vsMap_In_intro: forall {s v e}, vsIn srcSig v e -> vsIn dstSig (f s v) (vsMap e).
  Proof.
    unfold vsIn, vsMap; intros.
    apply List.in_map_iff.
    exists v; split; auto.
  Qed.
  
  Lemma vsUnion_map_l: forall {e e1 e2},
    vsSubset _ (vsUnion srcSig e1 e2) e -> vsSubset _ (vsUnion dstSig (vsMap e1) (vsMap e2)) (vsMap e) .
  Proof.
    repeat intro.
    apply (vsUnion_elim dstSig) in H0.
    destruct H0; apply List.in_map_iff in H0; destruct H0 as [x [h1 h2]]; subst v;
      apply List.in_map_iff; exists x; split; auto; apply H.
    now apply vsUnion_l.
    now apply vsUnion_r.
  Qed.
  
  Lemma vsUnion_map_r: forall {e e1 e2},
    vsSubset _ e (vsUnion srcSig e1 e2) -> vsSubset _ (vsMap e) (vsUnion dstSig (vsMap e1) (vsMap e2)).
  Proof.
    repeat intro.
    apply List.in_map_iff in H0.
    destruct H0 as [x [h1 h2]]; subst v.
    apply H in h2.
    apply vsUnion_elim in h2.
    destruct h2; [apply SV.InUnion_l | apply SV.InUnion_r]; apply List.in_map_iff; exists x; auto.
  Qed.
  
  Definition isInj {T1 T2} (f: T1 -> T2) := forall x1 x2, f x1 = f x2 -> x1 = x2.
  
  Lemma vsMap_add: forall s (v: variable s) (hf: forall s, isInj (f s)) e, 
    vsAdd dstSig (f s v) (vsMap e) = vsMap (vsAdd srcSig v e).
  Proof.
    intros.
    apply functional_extensionality_dep; intros s'.
    unfold vsMap, vsAdd; simpl.
    destruct (eq_dec s s'); auto.
    subst s'.
    match goal with |- match ?cnd with _=>_ end=_ => destruct cnd end.
    rewrite (proof_irrelevance _ _ eq_refl).
    generalize (hf s); generalize (f s); intros g hg; clear hf f.
    generalize (e s); clear e; intro l.
    induction l; simpl; intros; auto.
    destruct (eq_dec v a).
    subst a.
    match goal with |- match ?cnd with _=>_ end=_ => destruct cnd; tauto end.
    match goal with |- match ?cnd with _=>_ end=_ => destruct cnd end.
    apply hg in e; tauto.
    simpl; rewrite <-IHl; clear IHl.
    reflexivity.
    tauto.
    match goal with |- match ?cnd with _=>_ end=_ => destruct cnd; tauto end.
  Qed.

  Lemma vsMap_In_elim: forall  {s v e},
    (forall s, isInj (f s)) -> vsIn dstSig (f s v) (vsMap e) -> vsIn srcSig v e.
  Proof.
    unfold vsIn, vsMap; intros.
    apply List.in_map_iff in H0.
    destruct H0 as [x [h1 h2]].
    apply H in h1; subst x; auto.
  Qed.

  Lemma vsMap_In_ran: forall {s v e},
    vsIn dstSig v (vsMap e) -> exists v', v = f s v'.
  Proof.
    unfold vsIn, vsMap; intros.
    apply List.in_map_iff in H.
    destruct H as [x [h1 h2]].
    exists x; symmetry; auto.
  Qed.

  Lemma vsMap_Union: forall {e1 e2}, (forall s, isInj (f s)) -> forall s' (v': variable (Sig:=dstSig) s'),
    vsIn _ v' (vsMap (vsUnion srcSig e1 e2)) <-> vsIn _ v' (vsUnion dstSig (vsMap e1) (vsMap e2)).
  Proof.
    intros.
    split; intro.
    destruct (vsMap_In_ran H0) as [v h]; subst v'.
    apply (vsMap_In_elim) in H0; auto.
    apply vsUnion_elim in H0.
    destruct H0; [apply vsUnion_l | apply vsUnion_r]; apply vsMap_In_intro; auto.

    apply vsUnion_elim in H0; destruct H0.
    destruct (vsMap_In_ran H0) as [v h]; subst v'.
    apply vsMap_In_elim in H0; auto.
    apply vsMap_In_intro; apply vsUnion_l; apply H0.

    destruct (vsMap_In_ran H0) as [v h]; subst v'.
    apply vsMap_In_elim in H0; auto.
    apply vsMap_In_intro; apply vsUnion_r; apply H0.
  Qed.

  Lemma vsMap_Inter: forall {e1 e2}, (forall s, isInj (f s)) -> forall s' (v': variable (Sig:=dstSig) s'),
    vsIn _ v' (vsMap (vsInter srcSig e1 e2)) <-> vsIn _ v' (vsInter dstSig (vsMap e1) (vsMap e2)).
  Proof.
    intros.
    split; intro.
    destruct (vsMap_In_ran H0) as [v h]; subst v'.
    apply (vsMap_In_elim) in H0; auto.
    apply vsInter_elim in H0; destruct H0.
    apply vsInter_intro; apply vsMap_In_intro; auto.

    apply vsInter_elim in H0; destruct H0.
    destruct (vsMap_In_ran H0) as [v h]; subst v'.
    apply vsMap_In_intro.
    apply (vsMap_In_elim H) in H0.
    apply (vsMap_In_elim H) in H1.
    apply vsInter_intro; auto.
  Qed.
  
  Lemma vsMap_Remove: forall {s v} {e}, (forall s, isInj (f s)) -> forall s' (v': variable (Sig:=dstSig) s'),
    vsIn _ v' (vsMap (vsRemove srcSig v e)) <-> vsIn _ v' (vsRemove dstSig (f s v) (vsMap e)).
  Proof.
    intros; split; intro.
    destruct (vsMap_In_ran H0) as [w h]; subst v'.
    apply (vsMap_In_elim) in H0; auto.
    apply vsInRemove_elim in H0.
    apply vsInRemove_intro; auto.
    apply vsMap_In_intro; tauto.
    intro; apply proj2 in H0; apply H0; clear H0.
    inversion H1; clear H1; intros; subst s'.
    apply inj_pair2_eq_dec in H3; try apply eq_dec.
    apply (H s) in H3; subst w; constructor.
    
    apply vsInRemove_elim in H0; destruct H0.
    destruct (vsMap_In_ran H0) as [w h]; subst v'.
    apply (vsMap_In_elim) in H0; auto.
    apply vsMap_In_intro; auto.
    apply vsInRemove_intro; auto.
    intro; apply H1; clear H1.    
    inversion H2; clear H2; intros; subst s'; auto.
    constructor.
  Qed.

End VSMap.

