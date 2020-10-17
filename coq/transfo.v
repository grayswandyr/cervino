Require Import ProofIrrelevance.
Import  EqNotations.
Require Import List.
Require Import String.

Require Import api.
Require Import api2coq.
Require Import foltl.
Require Import set.
Require Import finite.
Require abstraction.
Require closure.
Require Import coq2ml.
Require Import mlUtils.

Section Transfo.
  Variable mdl: mlModel.
  
  Definition mlConj l := List.fold_right (fun a r => MLAnd a r) MLFTrue l.

  Definition mlDisj l := List.fold_right (fun a r => MLOr a r) MLFFalse l.

  Definition mlArgs2Ex l f := List.fold_right (fun v r => MLEx v r) f l.
   
  Definition mlEvtSem e :=
    mlArgs2Ex (mlEvArgs e) (mlEvBody e).

  Definition mlAxmSem (m: mlModel) := mlConj (mlAxioms m).

  Lemma mlDisjIds: forall l F, (forall f, List.In f l -> List.incl (mlFormulaIds f) F)
    -> List.incl (mlFormulaIds (mlDisj l)) F.
  Proof.
    induction l; simpl; intros; auto.
    repeat intro.
    destruct H0.
    apply List.incl_app.
    apply H; tauto.
    apply IHl; intros.
    apply H; tauto.
  Qed.

  Lemma mlConjIds: forall l F, (forall f, List.In f l -> List.incl (mlFormulaIds f) F)
    -> List.incl (mlFormulaIds (mlConj l)) F.
  Proof.
    induction l; simpl; intros; auto.
    repeat intro.
    destruct H0.
    apply List.incl_app.
    apply H; tauto.
    apply IHl; intros.
    apply H; tauto.
  Qed.

  Lemma mlArgs2ExIds: forall l f,
    List.incl (mlFormulaIds (mlArgs2Ex l f)) (List.map (fun a => MLS (mlVarSort a)) l ++ List.map MLV l ++ mlFormulaIds f).
  Proof.
    induction l; simpl; intros; auto.
    apply incl_refl.
    apply incl_cons; simpl; try tauto.
    apply incl_cons; simpl.
    right.
    rewrite in_app_iff; right; simpl; tauto.
    specialize IHl with f.
    apply incl_tran with (map (fun a : mlVariable => MLS (mlVarSort a)) l ++
         map MLV l ++ mlFormulaIds f); auto; clear IHl.
    change (MLS (mlVarSort a)
       :: map (fun a0 : mlVariable => MLS (mlVarSort a0)) l ++
      MLV a :: map MLV l ++ mlFormulaIds f) with
      ((MLS (mlVarSort a)::nil)++
       (map (fun a0 : mlVariable => MLS (mlVarSort a0)) l) ++
      MLV a :: map MLV l ++ mlFormulaIds f).
    apply incl_appr.
    apply incl_app_app.
    apply incl_refl.
    change (MLV a :: map MLV l ++ mlFormulaIds f) with
      ((MLV a :: nil) ++ map MLV l ++ mlFormulaIds f).
    apply incl_appr.
    apply incl_refl.
  Qed.

  Lemma mlFormOfDisj_incl:
    incl 
      (mlFormulaIds (mlDisj (List.map mlEvtSem (mlEvents mdl))))
      (mlModelIds mdl).
  Proof.
    apply mlDisjIds; intros.
    apply List.in_map_iff in H.
    destruct H as [x [h1 h2]].
    unfold mlModelIds.
    apply List.incl_appr.
    apply List.incl_appl.
    apply utils.in_fnth in h2.
    destruct h2 as [i h2].
    apply utils.in_concat_map_intro.
    exists i.
    subst f; subst x.
    unfold mlEvtSem.
    generalize (utils.fnth (mlEvents mdl) i); intro f.
    generalize (mlArgs2ExIds (mlEvArgs f) (mlEvBody f)); intro.
    apply incl_tran with
      (map (fun a : mlVariable => MLS (mlVarSort a)) (mlEvArgs f) ++
        map MLV (mlEvArgs f) ++ mlFormulaIds (mlEvBody f)); auto.
    clear H.
    rewrite <-map_map.
    unfold mlEventIds.
    apply incl_app.
    apply List.incl_appr.
    apply List.incl_appl; apply List.incl_refl.
    
    apply incl_app.
    apply List.incl_appl; apply List.incl_refl.
    apply List.incl_appr; apply List.incl_appr; apply List.incl_refl.
  Qed.

  Lemma mlAxmBdy_incl:
    List.incl
      (mlFormulaIds (mlAxmSem mdl) ++ mlFormulaIds (mlChkBody (mlCheckWith mdl)))
     (mlModelIds mdl).
  Proof.
    unfold mlModelIds.
    apply incl_app.
    apply incl_appl.
    unfold mlAxmSem.
    apply (mlConjIds (mlAxioms mdl)); intros.
    apply utils.in_concat_map_intro.
    apply utils.in_fnth in H; destruct H as [i H]; subst f.
    exists i; apply incl_refl.

    repeat intro.
    apply in_app_iff; right.
    apply in_app_iff; right.
    apply in_app_iff; right.
    unfold mlCheckIds.
    apply in_app_iff; left; now auto.
  Qed.

  Program Definition applyTEA: option mlFormula :=
    let chk := mlCheckWith mdl in
    let f := mlDisj (List.map mlEvtSem (mlEvents mdl)) in
    let cf := mlFormula2formula mdl f mlFormOfDisj_incl in
    let fv s := vars.free (coqSig mdl) cf s in 
    let g := MLAnd (mlAxmSem mdl) (mlChkBody chk) in
    let cg := mlFormula2formula mdl g mlAxmBdy_incl in
    match isExAll_dec (coqSig mdl) cf with
      left exAll => 
        match all_dec (fun s => SV.emptyDec (fv s)) with
          inl ise => 
            let res := abstraction.abstract_G_EAf_and_g (coqSig mdl) cf cg exAll ise in
            Some (fm2ml _ (fun s => proj1_sig s) (fun _ v => mlVarName _) (fun _ c => (mlCstName _)) (fun r => _) res)
        | inr _ => None
        end
    | right _ => None
    end.
  Next Obligation.
    apply proj1_sig in v.
    exact v.
  Defined.
  Next Obligation.
    apply proj1_sig in c.
    exact c.
  Defined.
  Next Obligation.
    destruct r.
    destruct p.
    destruct x.
    exact mlRelName.
    destruct v.
    destruct x.
    exact (String.append ("E"%string)  mlVarName).
  Defined.

  Definition applyTEA_Sg :=
    abstraction.dstSig (coqSig mdl)
       (quantifiers.getExF
         (mlFormula2formula mdl
           (mlDisj (map mlEvtSem (mlEvents mdl)))
           mlFormOfDisj_incl)).

  Program Definition applyTTC (r: mlRelation) hr (v: mlVariable) hv (P: mlFormula) hP:
    option mlFormula :=
    let cr := mlRelation2Pred mdl r hr in
    let cls := mlClosures mdl in
    let lp := utils.imap cls (fun p h => 
      (mlRelation2Pred mdl (mlBase p) _, mlRelation2Pred mdl (mlTC p) _)) in 
    match dec.assoc cr lp with
      None => None
    | Some r' =>
      let cf: formula (coqSig mdl) := mlFormula2formula mdl P hP in
      let cv := mlVar2Var mdl v hv in
      match closure.ClosureSpec_dec (srcSg := coqSig mdl) cr r' cf cv with
        left cs => 
          let res := closure.absClosure cs in
          Some (fm2ml _ (fun s => proj1_sig s) (fun _ v => _) (fun _ c => mlCstName _) (fun r => mlRelName (proj1_sig r)) res)
      | right _ => None
      end
    end.
  Next Obligation.
    clear r hr v hv P hP.
    unfold mlRelations.
    apply (utils.imap_filter_In_intro _ _ isMLRelDec (mlModelIds mdl)
      (fun (v : mlIdent) (h1 : isMLRel v) (_ : In v (mlModelIds mdl)) =>
      getMLRel v h1) (MLR (mlBase p)) I ).
    unfold mlModelIds.
    apply in_app_iff; right.
    apply in_app_iff; right.
    apply in_app_iff; left.
    apply in_concat.
    exists (mlPathIds p); split.
    apply in_map_iff; exists p; split; now auto.
    unfold mlPathIds; simpl.
    right.
    apply in_app_iff; right.
    unfold mlRelIds; simpl; tauto.
  Qed.
  Next Obligation.
    unfold mlRelations.
    apply (utils.imap_filter_In_intro _ _ isMLRelDec (mlModelIds mdl)
      (fun (v : mlIdent) (h1 : isMLRel v) (_ : In v (mlModelIds mdl)) =>
      getMLRel v h1) (MLR (mlTC p)) I ).
    unfold mlModelIds.
    apply in_app_iff; right.
    apply in_app_iff; right.
    apply in_app_iff; left.
    apply in_concat.
    exists (mlPathIds p); split.
    apply in_map_iff; exists p; tauto.
    unfold mlPathIds.
    apply in_app_iff; left.
    unfold mlRelIds; left; now auto.
  Qed.
  Next Obligation.
    unfold dec.eqDom in v; simpl in v.
    unfold closure.dstVarT in v; simpl in v.
    destruct (finite.asDec_obligation_1 mlSort StrDec 
       (mlSorts mdl) H (mlSortOfVar mdl v0 hv)).
    destruct v.
    destruct a eqn:aux.
      exact "_X1"%string.
      exact "_X2"%string.
      exact "_Z1"%string.
      exact "_Z2"%string.
    destruct e0 as [v _].
    exact (mlVarName v).
    destruct v as [v _].
    exact (mlVarName v).
  Defined.
  Next Obligation.
    apply proj1_sig in c.
    exact c.
  Defined.
  
  Lemma TTC_r_In_rels: forall {r v P}, 
    TTC r v P = mlChkUsing (mlCheckWith mdl) -> In r (mlRelations mdl).
  Proof.
    intros.
    assert (In (MLR r) (mlModelIds mdl)).
    unfold mlModelIds.
      rewrite in_app_iff; right.
      rewrite in_app_iff; right.
      rewrite in_app_iff; right.
      unfold mlCheckIds.
      rewrite in_app_iff; right.
      rewrite in_app_iff; right.
      rewrite <-H; simpl; tauto.
    unfold mlRelations.
    apply (utils.imap_filter_In_intro _ _ isMLRelDec (mlModelIds mdl) 
      (fun (v0 : mlIdent) (h1 : isMLRel v0)
        (_ : In v0 (mlModelIds mdl)) => getMLRel v0 h1) (MLR r) I H0); intro.
  Qed.
  
  Lemma TTC_v_In_vars: forall {r v P},
    TTC r v P = mlChkUsing (mlCheckWith mdl) -> In v (mlAllVariables mdl).
  Proof.
    intros.
    assert (In (MLV v) (mlModelIds mdl)).
    unfold mlModelIds.
      rewrite in_app_iff; right.
      rewrite in_app_iff; right.
      rewrite in_app_iff; right.
      unfold mlCheckIds.
      rewrite in_app_iff; right.
      rewrite in_app_iff; right.
      rewrite <-H; simpl; auto.
      right.
      apply in_app_iff; right; simpl; now auto.
    unfold mlAllVariables.
    apply (utils.imap_filter_In_intro _ _ isMLVarDec (mlModelIds mdl) 
      (fun (v0 : mlIdent) (h1 : isMLVar v0)
        (_ : In v0 (mlModelIds mdl)) => getMLVar v0 h1) (MLV v) I H0).
  Qed.
  
  Lemma TTC_P_In_fms: forall {r v P},
     TTC r v P = mlChkUsing (mlCheckWith mdl) -> incl (mlFormulaIds P) (mlModelIds mdl).
  Proof.
    intros.
    intros id H0.
    unfold mlModelIds.
    rewrite in_app_iff; right.
    rewrite in_app_iff; right.
    rewrite in_app_iff; right.
    unfold mlCheckIds.
    rewrite in_app_iff; right.
    rewrite in_app_iff; right.
    rewrite <-H; simpl; auto.
    right.
    apply in_app_iff; right; simpl; tauto.
  Qed.
  
  Definition mlTransform : option mlFormula :=
    let chk := mlCheckWith mdl in
    match mlChkUsing chk as t return t = mlChkUsing chk -> _ with
      TEA => fun e => applyTEA
    | TTC r v P => fun e => applyTTC r (TTC_r_In_rels e) v (TTC_v_In_vars e) P (TTC_P_In_fms e)
    | _ => fun e => None
    end eq_refl.

End Transfo.
