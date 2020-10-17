Require Import List.
Require Import String.

Require Import utils.

Require Import api.

Definition mlVarIds v := MLV v :: MLS (mlVarSort v) :: nil.

Definition mlCstIds c := MLC c :: MLS (mlCstSort c) :: nil.

Definition mlRelIds r := MLR r :: (List.map MLS (mlRelArity r)).

Definition mlTermIds tm: list mlIdent :=
  match tm with
   MLVar v => mlVarIds v
  | MLCst c => mlCstIds c
  end.

Definition mlLitIds l : list mlIdent :=
  match l with
    MLPApp nx r args => 
      mlRelIds {| mlRelName := r; mlRelArity := List.map mlTermSort args |} ++
        List.concat (List.map mlTermIds args)
  end.

Definition mlAtomIds a : list mlIdent :=
  match a with
  | MLLiteral l => mlLitIds l
  | MLNLiteral l => mlLitIds l
  | MLEq t1 t2 => mlTermIds t1 ++ mlTermIds t2
  | MLNEq t1 t2 => mlTermIds t1 ++ mlTermIds t2
  end.

Fixpoint mlFormulaIds f :=
  match f with
    MLFTrue | MLFFalse => nil
  | MLAtom a => mlAtomIds a
  | MLAnd f1 f2 | MLOr f1 f2 => mlFormulaIds f1 ++ mlFormulaIds f2
  | MLEx v f' | MLAll v f' => MLS (mlVarSort v) :: MLV v :: mlFormulaIds f'
  | MLF f' | MLG f' => mlFormulaIds f'
  end.

Definition mlEventIds ev :=
  List.map MLV (mlEvArgs ev) ++ 
  List.map MLS (List.map mlVarSort (mlEvArgs ev)) ++
  mlFormulaIds (mlEvBody ev).

Definition mlPathIds p := mlRelIds (mlTC p) ++ mlRelIds (mlBase p).

Definition mlUsingIds u evts :=
  match u with
    TEA => nil
  | TTC r v f => (mlRelIds r) ++ (mlVarIds v) ++ (mlFormulaIds f)
  | TFC ef => List.concat (List.map (fun e => mlFormulaIds (ef e)) evts) 
  end.

Definition mlCheckIds chk evts :=
  mlFormulaIds (mlChkBody chk) ++
  mlFormulaIds (mlChkAssumes chk) ++
  mlUsingIds (mlChkUsing chk) evts.

Definition mlModelIds m :=
  List.concat (List.map mlFormulaIds (mlAxioms m)) ++
  List.concat (List.map mlEventIds (mlEvents m)) ++
  List.concat (List.map mlPathIds (mlClosures m)) ++
  (mlCheckIds (mlCheckWith m) (mlEvents m)).

Definition mlSorts m := 
  imap_filter isMLSortDec
    (mlModelIds m)
    (fun v h1 h2 => getMLSort v h1).

Definition mlAllVariables m: list mlVariable :=
  imap_filter isMLVarDec
    (mlModelIds m)
    (fun v h1 h2 => getMLVar v h1).

Definition mlVariables m s :=
  List.filter (fun v => if string_dec (mlVarSort v) s then true else false) (mlAllVariables m).

Definition mlAllConstants m: list mlConstant :=
  imap_filter isMLCstDec
    (mlModelIds m)
    (fun v h1 h2 => getMLCst v h1).

Definition mlConstants m s :=
  List.filter (fun v => if string_dec (mlCstSort v) s then true else false) (mlAllConstants m).

Definition mlRelations m: list mlRelation :=
  imap_filter isMLRelDec
    (mlModelIds m)
    (fun v h1 h2 => getMLRel v h1).

Lemma mlSortOfTermVarIn:
 forall v tm, In (MLV v) (mlTermIds tm) -> In (MLS (mlVarSort v)) (mlTermIds tm).
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
 forall c tm, In (MLC c) (mlTermIds tm) -> In (MLS (mlCstSort c)) (mlTermIds tm).
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
 forall v lt, In (MLV v) (mlLitIds lt) -> In (MLS (mlVarSort v)) (mlLitIds lt).
Proof.
  intros; destruct lt; simpl in *; intros; auto.
  destruct H; [left | right]; auto; try discriminate.
  revert H; apply In_app_imp_In_app; intros.
  exfalso; revert H; generalize (map mlTermSort args); simpl; intros; auto.
  apply in_map_iff in H; destruct H as [x [h1 h2]]; subst; auto; discriminate.
  revert H; apply In_cmap_In_cmap.
  apply mlSortOfTermVarIn.
Qed.

Lemma mlSortOfLitCstIn:
 forall c lt, In (MLC c) (mlLitIds lt) -> In (MLS (mlCstSort c)) (mlLitIds lt).
Proof.
  intros; destruct lt; simpl in *; intros; auto.
  destruct H; [left | right]; auto; try discriminate.
  revert H; apply In_app_imp_In_app; intros.
  exfalso; revert H; generalize (map mlTermSort args); simpl; intros; auto.
  apply in_map_iff in H; destruct H as [x [h1 h2]]; subst; auto; discriminate.
  revert H; apply In_cmap_In_cmap.
  apply mlSortOfTermCstIn.
Qed.

Lemma mlSortOfAtmVarIn:
 forall v a, In (MLV v) (mlAtomIds a) -> In (MLS (mlVarSort v)) (mlAtomIds a).
Proof.
  intros v a; destruct a; simpl; intros.
  revert H; apply mlSortOfLitVarIn.
  revert H; apply mlSortOfLitVarIn.
  revert H; apply In_app_imp_In_app; apply mlSortOfTermVarIn.
  revert H; apply In_app_imp_In_app; apply mlSortOfTermVarIn.
Qed.

Lemma mlSortOfAtmCstIn:
 forall c a, In (MLC c) (mlAtomIds a) -> In (MLS (mlCstSort c)) (mlAtomIds a).
Proof.
  intros v a; destruct a; simpl; intros.
  revert H; apply mlSortOfLitCstIn.
  revert H; apply mlSortOfLitCstIn.
  revert H; apply In_app_imp_In_app; apply mlSortOfTermCstIn.
  revert H; apply In_app_imp_In_app; apply mlSortOfTermCstIn.
Qed.

Lemma mlSortOfFormVarIn:
 forall v f, In (MLV v) (mlFormulaIds f) -> In (MLS (mlVarSort v)) (mlFormulaIds f).
Proof.
  induction f; simpl; intros; auto.
  revert H; apply mlSortOfAtmVarIn.
  revert H; apply In_app_imp_In_app; auto.
  revert H; apply In_app_imp_In_app; auto.

  destruct H; try discriminate.
  destruct H.
  injection H; intros; subst m; tauto.
  right; right; now auto.

  destruct H; try discriminate.
  destruct H.
  injection H; intros; subst m; tauto.
  right; right; now auto.  
Qed.

Lemma mlSortOfFormCstIn:
 forall c f, In (MLC c) (mlFormulaIds f) -> In (MLS (mlCstSort c)) (mlFormulaIds f).
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
  In s (mlRelArity r) -> In (MLR r) (mlTermIds tm) -> In (MLS s) (mlTermIds tm).
Proof.
  intros.
  destruct tm; simpl in *.
  destruct H0; try discriminate.
  destruct H0; try discriminate; tauto.
  destruct H0; try discriminate.
  destruct H0; try discriminate; tauto.
Qed.

Lemma mlSortOfRelRelIn: forall r1 r2 s,
  In s (mlRelArity r1) -> In (MLR r1) (mlRelIds r2) -> In (MLS s) (mlRelIds r2).
Proof.
  intros.
  unfold mlRelIds in *.
  destruct H0.
  injection H0; clear H0; intros; subst r2; simpl.
  right; apply in_map_iff; exists s; tauto.
  apply in_map_iff in H0.
  destruct H0 as [s' [H0 _]]; discriminate.
Qed.

Lemma mlSortOfLitRelIn: forall lt r s,
  In s (mlRelArity r) -> In (MLR r) (mlLitIds lt) -> In (MLS s) (mlLitIds lt).
Proof.
  intros.
  destruct lt; simpl in *.
  destruct H0.
  injection H0; clear H0; intros; subst r; simpl in *.
  right.
  apply in_app_iff.
  left.
  apply in_map_iff in H.
  destruct H as [x [h1 h2]]; subst.
  apply in_map_iff.
  exists (mlTermSort x); split; auto.
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
  In s (mlRelArity r) -> In (MLR r) (mlAtomIds a) -> In (MLS s) (mlAtomIds a).
Proof.
  intros.
  destruct a; simpl in *; intros; auto.
  revert H H0; apply mlSortOfLitRelIn.
  revert H H0; apply mlSortOfLitRelIn.
  revert H0; apply In_app_imp_In_app; apply mlSortOfTermRelIn; auto.
  revert H0; apply In_app_imp_In_app; apply mlSortOfTermRelIn; auto.
Qed.

Lemma mlSortOfFormRelIn: forall f r s,
  In s (mlRelArity r) -> In (MLR r) (mlFormulaIds f) -> In (MLS s) (mlFormulaIds f).
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
  forall v e, In (MLV v) (mlEventIds e) -> In (MLS (mlVarSort v)) (mlEventIds e).
Proof.
  unfold mlEventIds; intros.
  apply in_app_iff in H; destruct H.
  apply in_map_iff in H.
  destruct H as [x [h1 h2]].
  injection h1; clear h1; intros; subst x.
  apply in_app_iff; right.
  apply in_app_iff; left.
  apply in_map_iff.
  exists (mlVarSort v); split; auto.
  apply in_map_iff; exists v; now auto.
  
  apply in_app_iff in H; destruct H.
  
  apply in_map_iff in H.
  destruct H as [x [H _]]; discriminate.
  
  apply in_app_iff; right.
  
  apply in_app_iff; right.
  revert H; apply mlSortOfFormVarIn.
Qed.

Lemma mlSortOfEvtCstIn:
  forall c e, In (MLC c) (mlEventIds e) -> In (MLS (mlCstSort c)) (mlEventIds e).
Proof.
  unfold mlEventIds; intros.
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
  forall v p, In (MLV v) (mlPathIds p) -> In (MLS (mlVarSort v)) (mlPathIds p).
Proof.
  unfold mlPathIds; intros.
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
  forall c p, In (MLC c) (mlPathIds p) -> In (MLS (mlCstSort c)) (mlPathIds p).
Proof.
  unfold mlPathIds; intros.
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
  In (MLV v) (mlCheckIds (mlCheckWith m) (mlEvents m)) ->
  In (MLS (mlVarSort v)) (mlCheckIds (mlCheckWith m) (mlEvents m)).
Proof.
  unfold mlCheckIds; intros.
  revert H; apply In_app_imp_In_app.
  apply mlSortOfFormVarIn.
  apply In_app_imp_In_app.
  apply mlSortOfFormVarIn.
  generalize (mlChkUsing (mlCheckWith m)); intro u.
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
  injection H; clear H; intros; subst m1; simpl; tauto.
  destruct H; try discriminate.
  right; right; revert H; apply mlSortOfFormVarIn.
  revert H; apply In_cmap_In_cmap.
  intro; apply mlSortOfFormVarIn.
Qed.

Lemma mlSortOfChkCstIn: forall c m,
  In (MLC c) (mlCheckIds (mlCheckWith m) (mlEvents m)) ->
  In (MLS (mlCstSort c)) (mlCheckIds (mlCheckWith m) (mlEvents m)).
Proof.
  unfold mlCheckIds; intros.
  revert H; apply In_app_imp_In_app.
  apply mlSortOfFormCstIn.
  apply In_app_imp_In_app.
  apply mlSortOfFormCstIn.
  generalize (mlChkUsing (mlCheckWith m)); intro u.
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
  In (MLV v) (mlModelIds m) -> In (MLS (mlVarSort v)) (mlModelIds m).
Proof.
  intros.
  unfold mlModelIds in *.
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
  In (MLC c) (mlModelIds m) -> In (MLS (mlCstSort c)) (mlModelIds m).
Proof.
  intros.
  unfold mlModelIds in *.
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
  In s (mlRelArity r) -> In (MLR r) (mlEventIds e) -> In (MLS s) (mlEventIds e).
Proof.
  intros.
  unfold mlEventIds in *.
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
  In s (mlRelArity r) -> In (MLR r) (mlPathIds p) -> In (MLS s) (mlPathIds p).
Proof.
  intros.
  unfold mlPathIds in *.
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
  In s (mlRelArity r) -> In (MLR r) (mlUsingIds u (mlEvents m)) ->
    In (MLS s) (mlUsingIds u (mlEvents m)).
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
  In s (mlRelArity r) -> In (MLR r) (mlCheckIds (mlCheckWith m) (mlEvents m))
   -> In (MLS s) (mlCheckIds (mlCheckWith m) (mlEvents m)).
Proof.
  intros.
  unfold mlCheckIds in *.
  revert H0.
  apply In_app_imp_In_app.
  apply mlSortOfFormRelIn; now auto.
  apply In_app_imp_In_app.
  apply mlSortOfFormRelIn; now auto.
  apply mlSortOfRelUsingArityIn; now auto.
Qed.

Lemma mlSortOfRelArityIn: forall m r s,
  In (MLR r) (mlModelIds m) -> In s (mlRelArity r) -> In (MLS s) (mlModelIds m).
Proof.
  unfold mlModelIds; intros.
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
  In v (mlAllVariables m) -> In (mlVarSort v) (mlSorts m).
Proof.
  intros.
  unfold mlAllVariables in H; unfold mlSorts.
  apply imap_filiter_in_elim in H.
  destruct H as [u [h1 [h2 h3]]]; subst v.
  destruct u; simpl in *; try tauto.
  apply (imap_filter_In_intro _ _ isMLSortDec (mlModelIds m)
    (fun (v0 : mlIdent) (h0 : isMLSort v0) (_ : In v0 (mlModelIds m))
      => getMLSort v0 h0) (MLS (mlVarSort v)) I).
  apply mlSortOfVarIn; auto.
Qed.

Lemma mlSortOfCstsIn: forall m c,
  In c (mlAllConstants m) -> In (mlCstSort c) (mlSorts m).
Proof.
  intros.
  unfold mlAllConstants in H; unfold mlSorts.
  apply imap_filiter_in_elim in H.
  destruct H as [u [h1 [h2 h3]]]; subst c.
  destruct u; simpl in *; try tauto.
  apply (imap_filter_In_intro _ _ isMLSortDec (mlModelIds m)
    (fun (v0 : mlIdent) (h0 : isMLSort v0) (_ : In v0 (mlModelIds m))
      => getMLSort v0 h0) (MLS (mlCstSort c)) I).
  apply mlSortOfCstIn; auto.
Qed.

Lemma mlSortOfRelAritiesIn: forall m r,
  In r (mlRelations m) -> forall s, In s (mlRelArity r) -> In s (mlSorts m).
Proof.
  intros.
  unfold mlRelations in H; unfold mlSorts.
  apply imap_filiter_in_elim in H.
  destruct H as [u [h1 [h2 h3]]]; subst r.
  destruct u; simpl in *; try tauto.
  apply (imap_filter_In_intro _ _ isMLSortDec (mlModelIds m)
    (fun (v0 : mlIdent) (h0 : isMLSort v0) (_ : In v0 (mlModelIds m))
      => getMLSort v0 h0) (MLS s) I).
  revert H0; apply mlSortOfRelArityIn; auto.
Qed.

