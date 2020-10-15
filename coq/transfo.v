Require Import ProofIrrelevance.
Import  EqNotations.
Require Import List.

Require Import api.
Require Import api2coq.
Require Import foltl.
Require Import set.
Require Import finite.
Require abstraction.
Require closure.

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

  Program Definition applyTEA :=
    let chk := mlCheckWith mdl in
    let f := mlDisj (List.map mlEvtSem (mlEvents mdl)) in
    let cf := mlFormula2formula mdl f _ in
    let fv s := vars.free (coqSig mdl) cf s in 
    let g := MLAnd (mlAxmSem mdl) (mlChkBody chk) in
    let cg := mlFormula2formula mdl g _ in
    match isExAll_dec (coqSig mdl) cf with
      left exAll => 
        match all_dec (fun s => SV.emptyDec (fv s)) with
          inl ise => Some (abstraction.abstract_G_EAf_and_g (coqSig mdl) cf cg exAll ise)
        | inr _ => None
        end
    | right _ => None
    end.
  Next Obligation.
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
  Next Obligation.
    unfold mlModelIds.
    apply incl_app.
    apply incl_appl.
    unfold mlAxmSem.
    apply (mlConjIds (mlAxioms mdl)); intros.
    apply utils.in_concat_map_intro.
    apply utils.in_fnth in H; destruct H as [i H]; subst f.
    exists i; apply incl_refl.

    admit.
  Admitted.

  Definition applyTEA_Sg :=
    abstraction.dstSig (coqSig mdl)
       (quantifiers.getExF
         (mlFormula2formula mdl
           (mlDisj (map mlEvtSem (mlEvents mdl)))
           applyTEA_obligation_1)).

  Program Definition applyTTC (r: mlRelation) hr (v: mlVariable) hv (P: mlFormula) hP:
    option (formula (closure.dstSg (coqSig mdl) (mlSortOfVar mdl v hv))) :=
    let cr := mlRelation2Pred mdl r hr in
    let cls := mlClosures mdl in
    let lp := utils.imap cls (fun p h => 
      (mlRelation2Pred mdl (mlBase p) _, mlRelation2Pred mdl (mlTC p) _)) in 
    match dec.assoc cr lp with
      None => None
    | Some r' =>
      let cf: formula (coqSig mdl) := mlFormula2formula mdl P hP in
      let cv := mlVar2Var mdl v _ in
      match closure.ClosureSpec_dec (srcSg := coqSig mdl) cr r' cf cv with
        left cs => Some (closure.absClosure cs)
      | right _ => None
      end
    end.
  Next Obligation.
    unfold mlRelations.
    unfold mlModelIds.
  Admitted.
  Next Obligation.
  Admitted.
  
  Definition applyTTCSig v hv :=
    closure.dstSg (coqSig mdl) (mlSortOfVar mdl v hv).
  
  Definition mlTransform : option ( :=
    let chk := mlCheckWith mdl in
    match mlChkUsing chk with
      TEA => applyTEA
    | TTC r v P => applyTTC r _ v _ P _
    | _ => None
    end.

End Transfo.
