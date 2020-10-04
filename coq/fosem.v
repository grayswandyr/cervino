Add LoadPath "$HOME/COQ/FO-LTL" as Top.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Eqdep_dec.
Require Import ProofIrrelevance.
Require Import Classical.

Require Import Top.foltl.
Require Import Top.set.
Require Import Top.dec.
Require Import Top.finite.
Require Import Top.vars.
Require Import Top.varset.

Section FOsem.

Context {Ts: Type} {Tv: Ts->Type} {Tc: Ts->Type} {Tp: Type}.
Context {Sg: @Sig Ts Tv Tc Tp}.

  Lemma tm_sem_eq: forall (D: Dom Sg) (Itp: Interp D) s (tm: term Sg s) (e1 e2: Env Sg D),
      (forall s (v: variable s), SV.set_In v (tm_vars Sg tm s) -> e1 s v = e2 s v) ->
        tm_sem (Itp:=Itp) Sg e1 tm = tm_sem (Itp:=Itp) Sg e2 tm.
  Proof.
    intros.
    destruct tm; simpl in *.
    apply H; clear H; auto.
    apply vsSing_intro.
    reflexivity.
  Qed.

  
  Ltac psemTac :=
    match goal with
      H:psem _ _ ?sa |- psem _ _ ?sa' => assert (sa' = sa) as ae;
          try (rewrite ae; assumption); (apply functional_extensionality_dep; intros)
    end.

  Lemma lt_sem_imp: forall (D: Dom Sg) (Itp: Interp D) (l: literal Sg) t (e1 e2: Env Sg D),
      (forall s (v: variable s), SV.set_In v (lt_vars Sg l s) -> e1 s v = e2 s v) ->
        lt_sem (Itp:=Itp) Sg e1 l t -> lt_sem (Itp:=Itp) Sg e2 l t.
  Proof.
    intros.
    destruct l; simpl in *.
    psemTac.
    apply tm_sem_eq; intros.
    symmetry; apply H; clear H; intros; auto.
    apply (vsGUnion_intro Sg s x); auto.
  Qed.

  Lemma lt_sem_equiv: forall (D: Dom Sg) (Itp: Interp D) (l: literal Sg) t (e1 e2: Env Sg D),
      (forall s (v: variable s), SV.set_In v (lt_vars Sg l s) -> e1 s v = e2 s v) ->
        lt_sem (Itp:=Itp) Sg e1 l t <-> lt_sem (Itp:=Itp) Sg e2 l t.
  Proof.
    intros; split.
    apply lt_sem_imp; auto.
    apply lt_sem_imp; intros.
    symmetry; apply H; auto. 
  Qed.
  
  Lemma at_sem_equiv: forall (D: Dom Sg) (Itp: Interp D) (a: atom Sg) t (e1 e2: Env Sg D),
      (forall s (v: variable s), SV.set_In v (at_free Sg a s) -> e1 s v = e2 s v) ->
        at_sem (Itp:=Itp) Sg e1 a t <-> at_sem (Itp:=Itp) Sg e2 a t.
  Proof.
    intros.
    destruct a; simpl in *.
    apply lt_sem_equiv; auto.
    
    apply not_iff_compat.
    apply lt_sem_equiv; auto.

    rewrite tm_sem_eq with (e1:=e2) (e2:=e1); intros; auto.
    rewrite tm_sem_eq with (e1:=e2) (e2:=e1); intros; auto.
    reflexivity.
    symmetry; apply H; clear H.
    apply vsUnion_r; auto.
    symmetry; apply H; clear H.
    apply vsUnion_l; auto.
    
    apply not_iff_compat.
    rewrite tm_sem_eq with (e1:=e2) (e2:=e1); intros; auto.
    rewrite tm_sem_eq with (e1:=e2) (e2:=e1); intros; auto.
    reflexivity.
    symmetry; apply H; clear H.
    apply vsUnion_r; auto.
    symmetry; apply H; clear H.
    apply vsUnion_l; auto.
  Qed.

  Lemma fm_sem_equiv: forall (D: Dom Sg) (Itp: Interp D) (f: formula Sg) t (e1 e2: Env Sg D),
      (forall s (v: variable s), SV.set_In v (free Sg f s) -> e1 s v = e2 s v) ->
        fm_sem (Itp:=Itp) Sg e1 f t <-> fm_sem (Itp:=Itp) Sg e2 f t.
  Proof.
    induction f; intros; auto.
  - reflexivity.
  - reflexivity.
  - apply at_sem_equiv; auto.
  - simpl.
    rewrite (IHf1 t e1 e2), (IHf2 t e1 e2); auto.
    reflexivity.
    intros; apply H; auto.
    apply vsUnion_r; apply H0.
    intros; apply H; auto.
    apply vsUnion_l; apply H0.
  - simpl.
    rewrite (IHf1 t e1 e2), (IHf2 t e1 e2); auto.
    reflexivity.
    intros; apply H; auto.
    apply vsUnion_r; apply H0.
    intros; apply H; auto.
    apply vsUnion_l; apply H0.
  - simpl.
    assert (forall d, fm_sem Sg (add Sg e d e1) f t <-> fm_sem Sg (add Sg e d e2) f t).
    intro.
    apply IHf; clear IHf; intros.
    unfold add.
    destruct (eq_dec s s0); auto.
    subst s0.
    destruct (eq_dec e v); auto.
    apply H; clear H; intros; auto.
    simpl.
    apply vsInRemove_intro; simpl; auto.
    intro; apply n; clear n.
    apply inj_pair2_eq_dec in H; try apply eq_dec; now auto.
    apply H; clear H; intros; auto.
    simpl.
    apply vsInRemove_intro; simpl; auto.
    intro; apply n; clear n.
    injection H; clear H; intros; now auto.

    setoid_rewrite H0; reflexivity.
  - simpl.
    assert (forall d, fm_sem Sg (add Sg e d e1) f t <-> fm_sem Sg (add Sg e d e2) f t).
    intro.
    apply IHf; clear IHf; intros.
    unfold add.
    destruct (eq_dec s s0); auto.
    subst s0.
    destruct (eq_dec e v); auto.
    apply H; clear H; intros; auto.
    simpl.
    apply vsInRemove_intro; simpl; auto.
    intro; apply n; clear n.
    apply inj_pair2_eq_dec in H; try apply eq_dec; now auto.
    apply H; clear H; intros; auto.
    simpl.
    apply vsInRemove_intro; simpl; auto.
    intro; apply n; clear n.
    injection H; clear H; intros; now auto.

    setoid_rewrite H0; reflexivity.
  - simpl.
    assert (forall t', (t'>=t /\ fm_sem Sg e1 f t') <-> (t'>=t /\ fm_sem Sg e2 f t')).
    intro.    
    setoid_rewrite (IHf t' e1 e2); auto.
    reflexivity.
    setoid_rewrite H0; reflexivity.
  - simpl.
    assert (forall t', (t'>=t -> fm_sem Sg e1 f t') <-> (t'>=t -> fm_sem Sg e2 f t')).
    intro.    
    setoid_rewrite (IHf t' e1 e2); auto.
    reflexivity.
    setoid_rewrite H0; reflexivity.
  Qed.

Lemma fold_in: forall `{K:Finite} {D: Dom Sg} {sk: K-> Sort} (vk: forall k, variable (sk k)) (dk: forall k, ssem (sk k)) (env: Env Sg D) l s (w: variable s) d,
  (exists k, List.In k l /\ isEq2 (U:=variable) _ w _ (vk k)) -> forall s' v,
    List.fold_left (fun (e : Env Sg D) (k0 : K) => add Sg (vk k0) (dk k0) e) l
      (add Sg w d env) s' v =
    List.fold_left (fun (e : Env Sg D) (k0 : K) => add Sg (vk k0) (dk k0) e) l
      env s' v.
Proof.
  intros.
  revert env; induction l; simpl; intros; auto.
  destruct H as [k [H _]]; destruct H.
  
  destruct (@dc_dec (isEq2 (U:=variable) s w (sk a) (vk a))).
  simpl in d0; injection d0; clear d0; intros; subst s.
  apply inj_pair2_eq_dec in H0; try apply eq_dec; subst w.
  rewrite add_add_eq; now auto.
  
  assert (exists k : K, List.In k l /\ isEq2 (U:=variable) s w (sk k) (vk k)).
  destruct H as [k [h1 h2]].
  exists k; split; auto.
  destruct h1; try tauto.
  subst k; tauto.
  rewrite add_add_ne_swp; auto.
  simpl in *; intro; apply n; clear n.
  injection H1; clear H1; intros; subst s; auto.
Qed.

Lemma fold_add_ex: forall `{K:Finite} {D: Dom Sg} {sk: K-> Sort} (vk: forall k, variable (sk k)) (dk: forall k, ssem (sk k)) (env: Env Sg D) l s (w: variable s),
  (exists k, SV.set_In k l /\ isEq2 (U:=variable) _ (vk k) _ w) -> forall d1 d2 s' v,
  List.fold_left (fun (e : Env Sg D) (k0 : K) => add Sg (vk k0) (dk k0) e) l
    (add Sg w d1 env) s' v =
  List.fold_left (fun (e : Env Sg D) (k0 : K) => add Sg (vk k0) (dk k0) e) l
    (add Sg w d2 env) s' v.
Proof.
  intros.
  revert env d1 d2; induction l; simpl; intros; auto.
  destruct H as [k [h1 h2]]; destruct h1.
  
  destruct H as [k [h1 h2]].
  destruct h1.
  subst k.
  change  (
    List.fold_left (fun (e : Env Sg D) (k0 : K) => add Sg (vk k0) (dk k0) e) (a::l)
      (add Sg w d1 env) s' v =
    List.fold_left (fun (e : Env Sg D) (k0 : K) => add Sg (vk k0) (dk k0) e) (a::l)
      (add Sg w d2 env) s' v).
  
  rewrite fold_in.
  rewrite fold_in; auto.
  
  exists a; split; simpl; now auto.
  exists a; split; simpl; now auto.

  destruct (@dc_dec (isEq2 (U:=variable) _ w _ (vk a))).
  injection d; intros; subst s.
  apply inj_pair2_eq_dec in d; try apply eq_dec; subst w.
  do 2 rewrite add_add_eq; now auto.  

  rewrite (add_add_ne_swp Sg) with (v2:=w); auto.
  rewrite (add_add_ne_swp Sg) with (v2:=w); auto.
  apply IHl.
  exists k; split; now auto.
  simpl in *; intro; apply n; clear n.
  injection H0; clear H0; intros; subst s; auto.
  simpl in *; intro; apply n; clear n.
  injection H0; clear H0; intros; subst s; auto.
Qed.

Lemma fold_add_nex: forall `(K: EqDec) {D: Dom Sg} {sk: K-> Sort} (vk: forall k, variable (sk k)) (dk dk': forall k, ssem (sk k)) (env: Env Sg D) l s (w: variable s) (a:K),
  (forall k, List.In k l -> ~ (isEq2 (U:=variable) (sk k) (vk k) (sk a) (vk a))) ->
  (forall k, a <> k -> dk' k = dk k) ->
  List.fold_left (fun e k => add Sg (vk k) (dk' k) e) l env s w =
  List.fold_left (fun e k => add Sg (vk k) (dk k) e) l env s w.
Proof.
  intros.
  revert env; induction l; simpl; intros; auto.
  
  rewrite (H0 a0).
  apply IHl; clear IHl; intros; auto.
  apply H.
  right; now auto.
  intro; subst a0.
  apply (H a); simpl; auto.
Qed.

Lemma IEx_sem: forall D (Itp: Interp D) env `(K: Finite) sk vk f t,
    fm_sem Sg env (IEx Sg K sk vk f) t
  <-> exists (dk: forall k, ssem (sk k)), fm_sem Sg (addl Sg K sk vk dk env) f t.
Proof.
  intros.
  unfold addl, IEx.
  unfold last_dec.
  revert env; induction fin_set; simpl; intros.
  
  split; intro.
  
  exists (fun k => neDom (sk k)); now auto.
  destruct H as [dk H].
  apply H.
  
  split; intro.
  destruct H as [d H].
  (***)
  
  apply IHs in H; clear IHs.
  destruct H as [dk H].
  
  destruct (SV.set_In_dec a s).
  exists dk.
  revert H; apply fm_sem_equiv; intros; clear H.
  destruct (SV.last_dec (fun k : K => isEq2 (sk k) (vk k) s0 v) s); auto.
  destruct s1 as [k [h1 h2]]; simpl; reflexivity.
  destruct ( dec.isEq2_obligation_1 _ Sort _ (fun x : Sort => variable x)
        (sk a) (vk a) s0 v); auto.
  unfold and_ind.
  injection e; intros; subst s0.
  apply inj_pair2_eq_dec in H; try apply eq_dec; subst v.
  exfalso; apply (n a i eq_refl).
  rewrite add_ne2; now auto.
    
  set (dk' := fun k => 
    match eq_dec a k return ssem (sk k) 
    with left e =>
      match e in _=k return ssem (sk k) with
        eq_refl => d
      end
      | _ => dk k
      end).
  exists dk'.
  
  revert H; apply fm_sem_equiv; intros; clear H.
  destruct (SV.last_dec (fun k : K => isEq2 (sk k) (vk k) s0 v) s); auto.
  destruct s1 as [k [h1 h2]]; simpl.
  
  injection h2; intros; subst s0.
  apply inj_pair2_eq_dec in H; try apply eq_dec; subst v.
  rewrite (proof_irrelevance _ _ eq_refl).
  unfold dk'.
  destruct (eq_dec a k); auto.
  subst k; tauto.
  
  destruct (dec.isEq2_obligation_1 _ Sort _ (fun x : Sort => variable x) 
        (sk a) (vk a) s0 v); auto.
  injection e; intros; subst s0.
  destruct (eq_dec (sk a) (sk a)); try tauto.
  unfold and_ind.
  apply inj_pair2_eq_dec in H; try apply eq_dec; subst v.
  rewrite (proof_irrelevance _ e eq_refl).
  rewrite add_eq.
  unfold dk'.
  destruct (eq_dec a a); try tauto.
  rewrite (proof_irrelevance _ e1 eq_refl); now auto.
  rewrite add_ne2; now auto.
  
  destruct H as [dk H].
  exists (dk a).
  apply IHs; clear IHs.
  exists dk.
  unfold and_ind in *.
  revert H; apply fm_sem_equiv; intros; auto.
  destruct (SV.last_dec (fun k : K => isEq2 (sk k) (vk k) s0 v) s); auto.
  destruct s1 as [k [h1 h2]]; simpl in *.
  reflexivity.
  destruct (dec.isEq2_obligation_1 _ Sort _ (fun x : Sort => variable x) 
        (sk a) (vk a) s0 v); auto.
  injection e; intros; subst s0.
  apply inj_pair2_eq_dec in H0; try apply eq_dec; subst v.
  rewrite add_eq.
  rewrite (proof_irrelevance _ _ eq_refl); now auto.  
  rewrite add_ne2; auto.
Qed.

Lemma IAll_sem: forall D (Itp: Interp D) env `(K: Finite) sk vk f t,
  fm_sem Sg env (IAll Sg K sk vk f) t <-> forall (dk: forall k, ssem (sk k)), fm_sem Sg (addl Sg K sk vk dk env) f t.
Proof.
  intros.
  assert (not (fm_sem Sg env (IAll Sg K sk vk f) t) <->
           (exists dk : forall k : K, ssem (sk k), not (fm_sem Sg (addl Sg K sk vk dk env) f t))).
  rewrite <-Not_sem.
  setoid_rewrite <-Not_sem.
  rewrite Not_IAll.
  rewrite IEx_sem; now auto.
  assert (not (fm_sem Sg env (IAll Sg K sk vk f) t) <->
           not (forall dk : forall k : K, ssem (sk k), (fm_sem Sg (addl Sg K sk vk dk env) f t))).
  rewrite H; clear H.
  split; intro.
  intro.
  destruct H as [dk H]; apply H; apply H0; now auto.
  apply not_all_ex_not in H; apply H.
  clear H.
  split; intros; try tauto.
  apply proj2 in H0.
  apply NNPP; intro; revert H; apply H0; clear H0; intro.
  apply (H1 (H dk)).
Qed.

End FOsem.