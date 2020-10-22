Require Import List.
Require Import String.

Require Import utils.

Require Import api.

Definition mlVarIds v := MLV v :: MLS (var_sort v) :: nil.

Definition mlCstIds c := MLC c :: MLS (cst_sort c) :: nil.

Definition mlRelIds r := MLR r :: (List.map MLS (rel_profile r)).

Definition termIds tm: list mlIdent :=
  match tm with
   Var v => mlVarIds v
  | Cst c => mlCstIds c
  end.

Definition mlLitIds r args : list mlIdent :=
  mlRelIds {| rel_name := r; rel_profile := List.map termSort args |} ++
        List.concat (List.map termIds args).

Definition mlAtomIds a : list mlIdent :=
  match a with
  | Pos_app nx r args => mlLitIds r args 
  | Neg_app nx r args => mlLitIds r args 
  | Eq t1 t2 => termIds t1 ++ termIds t2
  | Not_eq t1 t2 => termIds t1 ++ termIds t2
  end.

Fixpoint formulaIds f :=
  match f with
    True | False => nil
  | Lit a => mlAtomIds a
  | And f1 f2 | Or f1 f2 => formulaIds f1 ++ formulaIds f2
  | Exists v f' | All v f' => MLS (var_sort v) :: MLV v :: formulaIds f'
  | F f' | G f' => formulaIds f'
  end.

Definition eventIds ev :=
  List.map MLV (ev_args ev) ++ 
  List.map MLS (List.map var_sort (ev_args ev)) ++
  formulaIds (ev_body ev).

Definition pathIds p := mlRelIds (tc p) ++ mlRelIds (base p).

Definition mlUsingIds u evts :=
  match u with
    TEA => nil
  | TTC r v f => (mlRelIds r) ++ (mlVarIds v) ++ (formulaIds f)
  | TFC ef => List.concat (List.map (fun e => formulaIds (ef e)) evts) 
  end.

Definition checkIds chk evts :=
  formulaIds (chk_body chk) ++
  formulaIds (chk_assuming chk) ++
  mlUsingIds (chk_using chk) evts.

Definition modelIds m :=
  List.concat (List.map formulaIds (axioms m)) ++
  List.concat (List.map eventIds (events m)) ++
  List.concat (List.map pathIds (closures m)) ++
  (checkIds (checkWith m) (events m)).

Definition mlSorts m := 
  imap_filter isMLSortDec
    (modelIds m)
    (fun v h1 h2 => getMLSort v h1).

Definition mlAllVariables m: list variable :=
  imap_filter isVarDec
    (modelIds m)
    (fun v h1 h2 => getVar v h1).

Definition variables m s :=
  List.filter (fun v => if string_dec (var_sort v) s then true else false) (mlAllVariables m).

Definition mlAllConstants m: list constant :=
  imap_filter isCstDec
    (modelIds m)
    (fun v h1 h2 => getCst v h1).

Definition constants m s :=
  List.filter (fun v => if string_dec (cst_sort v) s then true else false) (mlAllConstants m).

Definition relations m: list relation :=
  imap_filter isMLRelDec
    (modelIds m)
    (fun v h1 h2 => getMLRel v h1).

Lemma mlSortOfTermVarIn:
 forall v tm, In (MLV v) (termIds tm) -> In (MLS (var_sort v)) (termIds tm).
Proof.
  intros.
  destruct tm; simpl in *.
  destruct H.
  injection H; intros; subst v0; tauto.
  destruct H; auto; discriminate.

  destruct H; auto; try discriminate.
  destruct H; auto; try discriminate.
Qed.

Lemma mlSortOfTermCstIn:
 forall c tm, In (MLC c) (termIds tm) -> In (MLS (cst_sort c)) (termIds tm).
Proof.
  intros.
  destruct tm; simpl in *.
  destruct H; auto; try discriminate.
  destruct H; auto; try discriminate.

  destruct H.
  injection H; intros; subst c0; tauto.
  destruct H; auto; discriminate.
Qed.

Lemma mlSortOfLitVarIn:
 forall v r a, In (MLV v) (mlLitIds r a) -> In (MLS (var_sort v)) (mlLitIds r a).
Proof.
  intros; simpl in *; intros; auto.
  destruct H; [left | right]; auto; try discriminate.
  revert H; apply In_app_imp_In_app; intros.
  exfalso; revert H; generalize (map termSort a); simpl; intros; auto.
  apply in_map_iff in H; destruct H as [x [h1 h2]]; subst; auto; discriminate.
  revert H; apply In_cmap_In_cmap.
  apply mlSortOfTermVarIn.
Qed.

Lemma mlSortOfLitCstIn:
 forall c r a, In (MLC c) (mlLitIds r a) -> In (MLS (cst_sort c)) (mlLitIds r a).
Proof.
  simpl in *; intros; auto.
  destruct H; [left | right]; auto; try discriminate.
  revert H; apply In_app_imp_In_app; intros.
  exfalso; revert H; generalize (map termSort a); simpl; intros; auto.
  apply in_map_iff in H; destruct H as [x [h1 h2]]; subst; auto; discriminate.
  revert H; apply In_cmap_In_cmap.
  apply mlSortOfTermCstIn.
Qed.

Lemma mlSortOfAtmVarIn:
 forall v a, In (MLV v) (mlAtomIds a) -> In (MLS (var_sort v)) (mlAtomIds a).
Proof.
  intros v a; destruct a; simpl; intros.
  revert H; apply mlSortOfLitVarIn.
  revert H; apply mlSortOfLitVarIn.
  revert H; apply In_app_imp_In_app; apply mlSortOfTermVarIn.
  revert H; apply In_app_imp_In_app; apply mlSortOfTermVarIn.
Qed.

Lemma mlSortOfAtmCstIn:
 forall c a, In (MLC c) (mlAtomIds a) -> In (MLS (cst_sort c)) (mlAtomIds a).
Proof.
  intros v a; destruct a; simpl; intros.
  revert H; apply mlSortOfLitCstIn.
  revert H; apply mlSortOfLitCstIn.
  revert H; apply In_app_imp_In_app; apply mlSortOfTermCstIn.
  revert H; apply In_app_imp_In_app; apply mlSortOfTermCstIn.
Qed.

Lemma mlSortOfFormVarIn:
 forall v f, In (MLV v) (formulaIds f) -> In (MLS (var_sort v)) (formulaIds f).
Proof.
  induction f; simpl; intros; auto.
  revert H; apply mlSortOfAtmVarIn.
  revert H; apply In_app_imp_In_app; auto.
  revert H; apply In_app_imp_In_app; auto.

  destruct H; try discriminate.
  destruct H.
  injection H; intros; subst v0; tauto.
  right; right; now auto.

  destruct H; try discriminate.
  destruct H.
  injection H; intros; subst v0; tauto.
  right; right; now auto.  
Qed.

Lemma mlSortOfFormCstIn:
 forall c f, In (MLC c) (formulaIds f) -> In (MLS (cst_sort c)) (formulaIds f).
Proof.
  induction f; simpl; intros; auto.
  revert H; apply mlSortOfAtmCstIn.
  revert H; apply In_app_imp_In_app; auto.
  revert H; apply In_app_imp_In_app; auto.

  destruct H; try discriminate.
  destruct H; try discriminate.
  tauto.

  destruct H; try discriminate.
  destruct H; try discriminate.
  tauto.
Qed.

Lemma mlSortOfTermRelIn: forall tm r s,
  In s (rel_profile r) -> In (MLR r) (termIds tm) -> In (MLS s) (termIds tm).
Proof.
  intros.
  destruct tm; simpl in *.
  destruct H0; try discriminate.
  destruct H0; try discriminate; tauto.
  destruct H0; try discriminate.
  destruct H0; try discriminate; tauto.
Qed.

Lemma mlSortOfRelRelIn: forall r1 r2 s,
  In s (rel_profile r1) -> In (MLR r1) (mlRelIds r2) -> In (MLS s) (mlRelIds r2).
Proof.
  intros.
  unfold mlRelIds in *.
  destruct H0.
  injection H0; clear H0; intros; subst r2; simpl.
  right; apply in_map_iff; exists s; tauto.
  apply in_map_iff in H0.
  destruct H0 as [s' [H0 _]]; discriminate.
Qed.

Lemma mlSortOfLitRelIn: forall a r p s,
  In s (rel_profile r) -> In (MLR r) (mlLitIds p a) -> In (MLS s) (mlLitIds p a).
Proof.
  intros; simpl in *.
  destruct H0.
  injection H0; clear H0; intros; subst r; simpl in *.
  right.
  apply in_app_iff.
  left.
  apply in_map_iff in H.
  destruct H as [x [h1 h2]]; subst.
  apply in_map_iff.
  exists (termSort x); split; auto.
  apply in_map_iff.
  exists x; split; auto.
  
  apply in_app_iff in H0.
  destruct H0.
  apply in_map_iff in H0.
  destruct H0 as [x [H0 _]]; discriminate.
  apply in_concat in H0.
  destruct H0 as [x [H0 H1]].
  apply in_map_iff in H0.
  destruct H0 as [t [h1 h2]]; subst.
  destruct t; simpl in *.
  destruct H1; try discriminate.
  destruct H0; try discriminate; tauto.
  destruct H1; try discriminate.
  destruct H0; try discriminate; tauto.
Qed.

Lemma mlSortOfAtmRelIn: forall a r s,
  In s (rel_profile r) -> In (MLR r) (mlAtomIds a) -> In (MLS s) (mlAtomIds a).
Proof.
  intros.
  destruct a; simpl in *.
  revert H H0; apply mlSortOfLitRelIn.
  revert H H0; apply mlSortOfLitRelIn.
  revert H0; apply In_app_imp_In_app; apply mlSortOfTermRelIn; now auto.
  revert H0; apply In_app_imp_In_app; apply mlSortOfTermRelIn; now auto.
Qed.

Lemma mlSortOfFormRelIn: forall f r s,
  In s (rel_profile r) -> In (MLR r) (formulaIds f) -> In (MLS s) (formulaIds f).
Proof.
  intros.
  induction f; simpl in *; intros; auto.
  revert H0; apply mlSortOfAtmRelIn; auto.
  revert H0; apply In_app_imp_In_app; now auto.
  revert H0; apply In_app_imp_In_app; now auto.
  destruct H0; try discriminate; destruct H0; try discriminate; tauto.
  destruct H0; try discriminate; destruct H0; try discriminate; tauto.
Qed.

Lemma mlSortOfEvtVarIn:
  forall v e, In (MLV v) (eventIds e) -> In (MLS (var_sort v)) (eventIds e).
Proof.
  unfold eventIds; intros.
  apply in_app_iff in H; destruct H.
  apply in_map_iff in H.
  destruct H as [x [h1 h2]].
  injection h1; clear h1; intros; subst x.
  apply in_app_iff; right.
  apply in_app_iff; left.
  apply in_map_iff.
  exists (var_sort v); split; auto.
  apply in_map_iff; exists v; now auto.
  
  apply in_app_iff in H; destruct H.
  
  apply in_map_iff in H.
  destruct H as [x [H _]]; discriminate.
  
  apply in_app_iff; right.
  
  apply in_app_iff; right.
  revert H; apply mlSortOfFormVarIn.
Qed.

Lemma mlSortOfEvtCstIn:
  forall c e, In (MLC c) (eventIds e) -> In (MLS (cst_sort c)) (eventIds e).
Proof.
  unfold eventIds; intros.
  apply in_app_iff in H; destruct H.
  apply in_map_iff in H.
  destruct H as [x [H _]]; discriminate.
  apply in_app_iff in H; destruct H.
  apply in_map_iff in H.
  destruct H as [x [H _]]; discriminate.
  
  apply in_app_iff; right.
  apply in_app_iff; right.
  revert H; apply mlSortOfFormCstIn.
Qed.

Lemma mlSortOfPathVarIn:
  forall v p, In (MLV v) (pathIds p) -> In (MLS (var_sort v)) (pathIds p).
Proof.
  unfold pathIds; intros.
  revert H; apply In_app_imp_In_app; intros.
  unfold mlRelIds in H.
  destruct H; try discriminate.
  apply in_map_iff in H.
  destruct H as [x [H _]]; discriminate.

  unfold mlRelIds in H.
  destruct H; try discriminate.
  apply in_map_iff in H.
  destruct H as [x [H _]]; discriminate.
Qed.

Lemma mlSortOfPathCstIn:
  forall c p, In (MLC c) (pathIds p) -> In (MLS (cst_sort c)) (pathIds p).
Proof.
  unfold pathIds; intros.
  revert H; apply In_app_imp_In_app; intros.
  unfold mlRelIds in H.
  destruct H; try discriminate.
  apply in_map_iff in H.
  destruct H as [x [H _]]; discriminate.

  unfold mlRelIds in H.
  destruct H; try discriminate.
  apply in_map_iff in H.
  destruct H as [x [H _]]; discriminate.
Qed.

Lemma mlSortOfChkVarIn: forall v m,
  In (MLV v) (checkIds (checkWith m) (events m)) ->
  In (MLS (var_sort v)) (checkIds (checkWith m) (events m)).
Proof.
  unfold checkIds; intros.
  revert H; apply In_app_imp_In_app.
  apply mlSortOfFormVarIn.
  apply In_app_imp_In_app.
  apply mlSortOfFormVarIn.
  generalize (chk_using (checkWith m)); intro u.
  unfold mlUsingIds.
  destruct u; simpl in *; intros; auto.
  destruct H; try discriminate.
  right.
  revert H; apply In_app_imp_In_app.
  intro.
  apply in_map_iff in H.
  destruct H as [x [H _]]; discriminate.
  intro.
  destruct H.
  injection H; clear H; intros; subst v0; simpl; tauto.
  destruct H; try discriminate.
  right; right; revert H; apply mlSortOfFormVarIn.
  revert H; apply In_cmap_In_cmap.
  intro; apply mlSortOfFormVarIn.
Qed.

Lemma mlSortOfChkCstIn: forall c m,
  In (MLC c) (checkIds (checkWith m) (events m)) ->
  In (MLS (cst_sort c)) (checkIds (checkWith m) (events m)).
Proof.
  unfold checkIds; intros.
  revert H; apply In_app_imp_In_app.
  apply mlSortOfFormCstIn.
  apply In_app_imp_In_app.
  apply mlSortOfFormCstIn.
  generalize (chk_using (checkWith m)); intro u.
  unfold mlUsingIds.
  destruct u; simpl in *; intros; auto.
  destruct H; try discriminate.
  right.
  revert H; apply In_app_imp_In_app.
  intro.
  apply in_map_iff in H.
  destruct H as [x [H _]]; discriminate.
  intro.
  destruct H; try discriminate.
  destruct H; try discriminate.
  right; right; revert H; apply mlSortOfFormCstIn.
  revert H; apply In_cmap_In_cmap.
  intro; apply mlSortOfFormCstIn.
Qed.

Lemma mlSortOfVarIn: forall m v,
  In (MLV v) (modelIds m) -> In (MLS (var_sort v)) (modelIds m).
Proof.
  intros.
  unfold modelIds in *.
  revert H.
  apply utils.In_app_imp_In_app.
  apply In_cmap_In_cmap.
  apply mlSortOfFormVarIn.

  apply utils.In_app_imp_In_app.
  apply In_cmap_In_cmap.
  apply mlSortOfEvtVarIn.

  apply utils.In_app_imp_In_app.
  apply In_cmap_In_cmap.
  apply mlSortOfPathVarIn.
  
  apply mlSortOfChkVarIn.
Qed.

Lemma mlSortOfCstIn: forall m c,
  In (MLC c) (modelIds m) -> In (MLS (cst_sort c)) (modelIds m).
Proof.
  intros.
  unfold modelIds in *.
  revert H.
  apply utils.In_app_imp_In_app.
  apply In_cmap_In_cmap.
  apply mlSortOfFormCstIn.

  apply utils.In_app_imp_In_app.
  apply In_cmap_In_cmap.
  apply mlSortOfEvtCstIn.

  apply utils.In_app_imp_In_app.
  apply In_cmap_In_cmap.
  apply mlSortOfPathCstIn.
  
  apply mlSortOfChkCstIn.
Qed.

Lemma mlSortOfEvtArityIn: forall e r s, 
  In s (rel_profile r) -> In (MLR r) (eventIds e) -> In (MLS s) (eventIds e).
Proof.
  intros.
  unfold eventIds in *.
  revert H0; apply In_app_imp_In_app.
  intros.
  apply in_map_iff in H0.
  destruct H0 as [v [H0 _]]; discriminate.
  apply In_app_imp_In_app.
  intro.
  apply in_map_iff in H0.
  destruct H0 as [s' [h1 h2]]; try discriminate.
  apply mlSortOfFormRelIn; auto.
Qed.

Lemma mlSortOfPathArityIn: forall p r s,
  In s (rel_profile r) -> In (MLR r) (pathIds p) -> In (MLS s) (pathIds p).
Proof.
  intros.
  unfold pathIds in *.
  revert H0; apply In_app_imp_In_app; simpl; intros.
  destruct H0.
  injection H0; clear H0; intros; subst.
  right.
  apply in_map_iff; exists s; tauto. 
  apply in_map_iff in H0.
  destruct H0 as [s' [h1 _]]; discriminate.

  destruct H0.
  injection H0; clear H0; intros; subst.
  right.
  apply in_map_iff; exists s; tauto. 
  apply in_map_iff in H0.
  destruct H0 as [s' [h1 _]]; discriminate.  
Qed.

Lemma mlSortOfRelUsingArityIn: forall m u r s,
  In s (rel_profile r) -> In (MLR r) (mlUsingIds u (events m)) ->
    In (MLS s) (mlUsingIds u (events m)).
Proof.
  intros.
  unfold mlUsingIds in *.
  destruct u.
  destruct H0.
  revert H0; apply In_app_imp_In_app.
  apply mlSortOfRelRelIn; now auto.
  apply In_app_imp_In_app.
  unfold mlVarIds; intro.
  simpl in H0.
  destruct H0; try discriminate.
  destruct H0; try tauto; discriminate.
  apply mlSortOfFormRelIn; now auto.
  revert H0; apply In_cmap_In_cmap; intro e.
  apply mlSortOfFormRelIn; auto.
Qed.

Lemma mlSortOfRelChkArityIn: forall m r s,
  In s (rel_profile r) -> In (MLR r) (checkIds (checkWith m) (events m))
   -> In (MLS s) (checkIds (checkWith m) (events m)).
Proof.
  intros.
  unfold checkIds in *.
  revert H0.
  apply In_app_imp_In_app.
  apply mlSortOfFormRelIn; now auto.
  apply In_app_imp_In_app.
  apply mlSortOfFormRelIn; now auto.
  apply mlSortOfRelUsingArityIn; now auto.
Qed.

Lemma mlSortOfRelArityIn: forall m r s,
  In (MLR r) (modelIds m) -> In s (rel_profile r) -> In (MLS s) (modelIds m).
Proof.
  unfold modelIds; intros.
  revert H.
  apply utils.In_app_imp_In_app.
  apply In_cmap_In_cmap.
  intro; apply mlSortOfFormRelIn; now auto.
  
  apply utils.In_app_imp_In_app.
  apply In_cmap_In_cmap.
  intro; apply mlSortOfEvtArityIn;  now auto.

  apply utils.In_app_imp_In_app.
  apply In_cmap_In_cmap.
  intro; apply mlSortOfPathArityIn; now auto.
  apply mlSortOfRelChkArityIn; now auto.
Qed.

Lemma mlSortOfVarsIn: forall m v,
  In v (mlAllVariables m) -> In (var_sort v) (mlSorts m).
Proof.
  intros.
  unfold mlAllVariables in H; unfold mlSorts.
  apply imap_filiter_in_elim in H.
  destruct H as [u [h1 [h2 h3]]]; subst v.
  destruct u; simpl in *; try tauto.
  apply (imap_filter_In_intro _ _ isMLSortDec (modelIds m)
    (fun (v0 : mlIdent) (h0 : isMLSort v0) (_ : In v0 (modelIds m))
      => getMLSort v0 h0) (MLS (var_sort v)) I).
  apply mlSortOfVarIn; auto.
Qed.

Lemma mlSortOfCstsIn: forall m c,
  In c (mlAllConstants m) -> In (cst_sort c) (mlSorts m).
Proof.
  intros.
  unfold mlAllConstants in H; unfold mlSorts.
  apply imap_filiter_in_elim in H.
  destruct H as [u [h1 [h2 h3]]]; subst c.
  destruct u; simpl in *; try tauto.
  apply (imap_filter_In_intro _ _ isMLSortDec (modelIds m)
    (fun (v0 : mlIdent) (h0 : isMLSort v0) (_ : In v0 (modelIds m))
      => getMLSort v0 h0) (MLS (cst_sort c)) I).
  apply mlSortOfCstIn; auto.
Qed.

Lemma mlSortOfRelAritiesIn: forall m r,
  In r (relations m) -> forall s, In s (rel_profile r) -> In s (mlSorts m).
Proof.
  intros.
  unfold relations in H; unfold mlSorts.
  apply imap_filiter_in_elim in H.
  destruct H as [u [h1 [h2 h3]]]; subst r.
  destruct u; simpl in *; try tauto.
  apply (imap_filter_In_intro _ _ isMLSortDec (modelIds m)
    (fun (v0 : mlIdent) (h0 : isMLSort v0) (_ : In v0 (modelIds m))
      => getMLSort v0 h0) (MLS s) I).
  revert H0; apply mlSortOfRelArityIn; auto.
Qed.

