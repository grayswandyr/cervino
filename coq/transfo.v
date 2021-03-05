Require Import ProofIrrelevance.
Import  EqNotations.
Require Import List.
Require Import String.

Require Import api.
Require Import api2coq.
Require foltl.
Require Import set.
Require Import finite.
Require Import dec.
Require abstraction.
Require closure.
Require Import coq2ml.
Require Import mlUtils.

Section Transfo.
  Variable mdl: model.
  
  Definition mlConj l := List.fold_right (fun a r => And a r) api.True l.

  Definition mlDisj l := List.fold_right (fun a r => Or a r) api.False l.

  Definition mlArgs2Ex l f := List.fold_right (fun v r => Exists v r) f l.
   
  Definition mlEvtSem e :=
    mlArgs2Ex (ev_args e) (ev_body e).

  Definition mlAxmSem (m: model) := mlConj (axioms m).

  Lemma mlDisjIds: forall l F, (forall f, List.In f l -> List.incl (formulaIds f) F)
    -> List.incl (formulaIds (mlDisj l)) F.
  Proof.
    induction l; simpl; intros; auto.
    repeat intro.
    destruct H0.
    apply List.incl_app.
    apply H; tauto.
    apply IHl; intros.
    apply H; tauto.
  Qed.

  Lemma mlConjIds: forall l F, (forall f, List.In f l -> List.incl (formulaIds f) F)
    -> List.incl (formulaIds (mlConj l)) F.
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
    List.incl (formulaIds (mlArgs2Ex l f)) (List.map (fun a => MLS (var_sort a)) l ++ List.map MLV l ++ formulaIds f).
  Proof.
    induction l; simpl; intros; auto.
    apply incl_refl.
    apply incl_cons; simpl; try tauto.
    apply incl_cons; simpl.
    right.
    rewrite in_app_iff; right; simpl; tauto.
    specialize IHl with f.
    apply incl_tran with (map (fun a : variable => MLS (var_sort a)) l ++
         map MLV l ++ formulaIds f); auto; clear IHl.
    change (MLS (var_sort a)
       :: map (fun a0 : variable => MLS (var_sort a0)) l ++
      MLV a :: map MLV l ++ formulaIds f) with
      ((MLS (var_sort a)::nil)++
       (map (fun a0 : variable => MLS (var_sort a0)) l) ++
      MLV a :: map MLV l ++ formulaIds f).
    apply incl_appr.
    apply incl_app_app.
    apply incl_refl.
    change (MLV a :: map MLV l ++ formulaIds f) with
      ((MLV a :: nil) ++ map MLV l ++ formulaIds f).
    apply incl_appr.
    apply incl_refl.
  Qed.

  Lemma mlFormOfDisj_incl:
    incl 
      (formulaIds (mlDisj (List.map mlEvtSem (events mdl))))
      (modelIds mdl).
  Proof.
    apply mlDisjIds; intros.
    apply List.in_map_iff in H.
    destruct H as [x [h1 h2]].
    unfold modelIds.
    apply List.incl_appr.
    apply List.incl_appl.
    apply utils.in_fnth in h2.
    destruct h2 as [i h2].
    apply utils.in_concat_map_intro.
    exists i.
    subst f; subst x.
    unfold mlEvtSem.
    generalize (utils.fnth (events mdl) i); intro f.
    generalize (mlArgs2ExIds (ev_args f) (ev_body f)); intro.
    apply incl_tran with
      (map (fun a : variable => MLS (var_sort a)) (ev_args f) ++
        map MLV (ev_args f) ++ formulaIds (ev_body f)); auto.
    clear H.
    rewrite <-map_map.
    unfold eventIds.
    apply incl_app.
    apply List.incl_appr.
    apply List.incl_appl; apply List.incl_refl.
    
    apply incl_app.
    apply List.incl_appl; apply List.incl_refl.
    apply List.incl_appr; apply List.incl_appr; apply List.incl_refl.
  Qed.

  Lemma mlAxmBdy_incl:
    List.incl
      (formulaIds (mlAxmSem mdl) ++ formulaIds (chk_body (checkWith mdl)))
     (modelIds mdl).
  Proof.
    unfold modelIds.
    apply incl_app.
    apply incl_appl.
    unfold mlAxmSem.
    apply (mlConjIds (axioms mdl)); intros.
    apply utils.in_concat_map_intro.
    apply utils.in_fnth in H; destruct H as [i H]; subst f.
    exists i; apply incl_refl.

    repeat intro.
    apply in_app_iff; right.
    apply in_app_iff; right.
    apply in_app_iff; right.
    unfold checkIds.
    apply in_app_iff; left; now auto.
  Qed.

  Program Definition applyTEA: option formula :=
    let chk := checkWith mdl in
    let f := mlDisj (List.map mlEvtSem (events mdl)) in
    let cf := formula2formula mdl f mlFormOfDisj_incl in
    let fv s := vars.free (coqSig mdl) cf s in 
    let g := And (mlAxmSem mdl) (chk_body chk) in
    let cg := formula2formula mdl g mlAxmBdy_incl in
    match foltl.isExAll_dec (coqSig mdl) cf with
      left exAll => 
        match all_dec (fun s => SV.emptyDec (fv s)) with
          inl ise => 
            let res := abstraction.abstract_G_EAf_and_g (coqSig mdl) cf cg exAll ise in
            Some (fm2ml _ (fun s => proj1_sig s) (fun _ v => var_name _) (fun _ c => (cst_name _)) (fun r => _) res)
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
    exact rel_name.
    destruct v.
    destruct x.
    exact (String.append ("E"%string)  var_name).
  Defined.

  Definition applyTEA_Sg :=
    abstraction.dstSig (coqSig mdl)
       (quantifiers.getExF
         (formula2formula mdl
           (mlDisj (map mlEvtSem (events mdl)))
           mlFormOfDisj_incl)).

  Lemma In_base_rel: forall p, In p (closures mdl) -> In (base p) (relations mdl).
  Proof.
    unfold relations; intros.
    apply (utils.imap_filter_In_intro _ _ isMLRelDec (modelIds mdl)
      (fun (v : mlIdent) (h1 : isMLRel v) (_ : In v (modelIds mdl)) =>
      getMLRel v h1) (MLR (base p)) I ).
    unfold modelIds.
    apply in_app_iff; right.
    apply in_app_iff; right.
    apply in_app_iff; left.
    apply in_concat.
    exists (pathIds p); split.
    apply in_map_iff; exists p; split; now auto.
    unfold pathIds; simpl.
    right.
    apply in_app_iff; right.
    unfold mlRelIds; simpl; tauto.
  Qed.

  Lemma In_tc_rel: forall p, In p (closures mdl) -> In (tc p) (relations mdl).
  Proof.
    unfold relations; intros.
    apply (utils.imap_filter_In_intro _ _ isMLRelDec (modelIds mdl)
      (fun (v : mlIdent) (h1 : isMLRel v) (_ : In v (modelIds mdl)) =>
      getMLRel v h1) (MLR (tc p)) I ).
    unfold modelIds.
    apply in_app_iff; right.
    apply in_app_iff; right.
    apply in_app_iff; left.
    apply in_concat.
    exists (pathIds p); split.
    apply in_map_iff; exists p; tauto.
    unfold pathIds.
    apply in_app_iff; left.
    unfold mlRelIds; left; now auto.
  Qed.

  Definition TTC_var (v: variable) hv s' (w: foltl.variable (Sig:=closure.dstSg (coqSig mdl) (mlSortOfVar mdl v hv)) s'): string.
    simpl in *.
    destruct (finite.asDec_obligation_1 mlSort StrDec (mlSorts mdl) s' (mlSortOfVar mdl v hv)).
    destruct w.
    destruct a eqn:aux.
      exact "_X1"%string.
      exact "_X2"%string.
      exact "_Z1"%string.
      exact "_Z2"%string.
    destruct e0 as [w _].
    exact (var_name w).
    destruct w as [w _].
    exact (var_name w).
  Defined.
  
  Definition applyTTC (r: relation) hr (v: variable) hv (P: formula) hP:
    option formula :=
    let cr := relation2Pred mdl r hr in
    let cls := closures mdl in
    let lp := utils.imap cls (fun p h => 
      (relation2Pred mdl (base p) (In_base_rel _ h), relation2Pred mdl (tc p) (In_tc_rel _ h))) in 
    let sg := closure.dstSg (coqSig mdl) (mlSortOfVar mdl v hv) in
    match dec.assoc cr lp with
      None => None
    | Some r' =>
      let cf: foltl.formula (coqSig mdl) := formula2formula mdl P hP in
      let cv := mlVar2Var mdl v hv in
      match closure.ClosureSpec_dec (srcSg := coqSig mdl) cr r' cf cv with
        left cs => 
          let res := closure.absClosure cs in
          Some (fm2ml _ (fun s => proj1_sig s) (TTC_var v hv) 
                  (fun s (c: foltl.constant (Sig:=sg) s) => 
                    let c' : constant := proj1_sig c in cst_name c')
                  (fun r => rel_name (proj1_sig r)) res)
      | right _ => None
      end
    end.
  
  Lemma TTC_r_In_rels: forall {r v P}, 
    TTC r v P = chk_using (checkWith mdl) -> In r (relations mdl).
  Proof.
    intros.
    assert (In (MLR r) (modelIds mdl)).
    unfold modelIds.
      rewrite in_app_iff; right.
      rewrite in_app_iff; right.
      rewrite in_app_iff; right.
      unfold checkIds.
      rewrite in_app_iff; right.
      rewrite in_app_iff; right.
      rewrite <-H; simpl; tauto.
    unfold relations.
    apply (utils.imap_filter_In_intro _ _ isMLRelDec (modelIds mdl) 
      (fun (v0 : mlIdent) (h1 : isMLRel v0)
        (_ : In v0 (modelIds mdl)) => getMLRel v0 h1) (MLR r) I H0); intro.
  Qed.
  
  Lemma TTC_v_In_vars: forall {r v P},
    TTC r v P = chk_using (checkWith mdl) -> In v (mlAllVariables mdl).
  Proof.
    intros.
    assert (In (MLV v) (modelIds mdl)).
    unfold modelIds.
      rewrite in_app_iff; right.
      rewrite in_app_iff; right.
      rewrite in_app_iff; right.
      unfold checkIds.
      rewrite in_app_iff; right.
      rewrite in_app_iff; right.
      rewrite <-H; simpl; auto.
      right.
      apply in_app_iff; right; simpl; now auto.
    unfold mlAllVariables.
    apply (utils.imap_filter_In_intro _ _ isVarDec (modelIds mdl) 
      (fun (v0 : mlIdent) (h1 : isVar v0)
        (_ : In v0 (modelIds mdl)) => getVar v0 h1) (MLV v) I H0).
  Qed.
  
  Lemma TTC_P_In_fms: forall {r v P},
     TTC r v P = chk_using (checkWith mdl) -> incl (formulaIds P) (modelIds mdl).
  Proof.
    intros.
    intros id H0.
    unfold modelIds.
    rewrite in_app_iff; right.
    rewrite in_app_iff; right.
    rewrite in_app_iff; right.
    unfold checkIds.
    rewrite in_app_iff; right.
    rewrite in_app_iff; right.
    rewrite <-H; simpl; auto.
    right.
    apply in_app_iff; right; simpl; tauto.
  Qed.
  
  Definition mlTransform : option formula :=
    let chk := checkWith mdl in
    match chk_using chk as t return t = chk_using chk -> _ with
      TEA => fun e => applyTEA
    | TTC r v P => fun e => applyTTC r (TTC_r_In_rels e) v (TTC_v_In_vars e) P (TTC_P_In_fms e)
    | _ => fun e => None
    end eq_refl.

End Transfo.
