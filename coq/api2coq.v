
Require Import String.
Require Import List.
Require Coq.Arith.PeanoNat.
Require Import ProofIrrelevance.
Require Import Init.Logic.
Import  EqNotations.

Require api.
Require mlUtils.
Require foltl.
Require Import finite.
Require Import dec.
Require Import utils.

Instance StrDec : EqDec := {| eq_dec := string_dec |}.
Instance NatDec : EqDec := {| eq_dec := Coq.Arith.PeanoNat.Nat.eq_dec |}.

Section ML2Coq.
Variable mdl : api.model.

Definition mlSorts2Sort : foltl.SortT := asFinite (mlUtils.mlSorts mdl).
Definition mlSort2Sort (s: api.mlSort) (h: List.In s (mlUtils.mlSorts mdl)) : mlSorts2Sort :=
 exist _ s h.

Instance variableDec: @EqDec api.variable.
Proof.
  split; repeat intro.
  destruct x as [v1 h1]; destruct y as [v2 h2].
  destruct (string_dec v1 v2).
  subst v2.
  destruct (string_dec h1 h2).
  subst h2.
  left; reflexivity.
  right; intro.
  injection H; intros; subst.
  apply n; reflexivity.
  right; intro.
  injection H; clear H; intros.
  apply (n H0).
Defined.

Instance constantDec: @EqDec api.constant.
Proof.
  split; repeat intro.
  destruct x as [v1 h1]; destruct y as [v2 h2].
  destruct (string_dec v1 v2).
  subst v2.
  destruct (string_dec h1 h2).
  subst h2.
  left; reflexivity.
  right; intro.
  injection H; intros; subst.
  apply n; reflexivity.
  right; intro.
  injection H; clear H; intros.
  apply (n H0).
Defined.

Instance relationDec: @EqDec api.relation.
Proof.
  split; repeat intro.
  destruct x as [v1 h1]; destruct y as [v2 h2].
  destruct (string_dec v1 v2).
  subst v2.
  destruct (list_eq_dec string_dec h1 h2).
  subst h2.
  left; reflexivity.
  right; intro.
  injection H; intros; subst.
  apply n; reflexivity.
  right; intro.
  injection H; clear H; intros.
  apply (n H0).
Defined.

Program Definition coqSig : foltl.Sig := {|
  foltl.Sort := mlSorts2Sort;
  foltl.variable s := asFinite (mlUtils.variables mdl (proj1_sig s));
  foltl.constant s := asFinite (mlUtils.constants mdl (proj1_sig s));
  foltl.predicate := asFinite (mlUtils.relations mdl);
  foltl.pr_arity p := List.length (api.rel_profile (proj1_sig p));
  foltl.pr_args p i := exist _ (fnth (api.rel_profile (proj1_sig p)) i) _
|}.
Next Obligation.
  destruct p as [r h]; simpl in *.
  apply (mlUtils.mlSortOfRelAritiesIn mdl r h).
  apply fnth_In.
Defined.

Definition mlSortOfVar v h: foltl.Sort (Sig:=coqSig) :=
  (mlSort2Sort (api.var_sort v) (mlUtils.mlSortOfVarsIn mdl v h)).

Definition mlSortOfCst v h: foltl.Sort (Sig:=coqSig) :=
  (mlSort2Sort (api.cst_sort v) (mlUtils.mlSortOfCstsIn mdl v h)).

Program Definition mlSortOfTerm t: List.incl (mlUtils.termIds t) (mlUtils.modelIds mdl) -> foltl.Sort (Sig:=coqSig) := 
  match t return List.incl (mlUtils.termIds t) (mlUtils.modelIds mdl) -> _ with
    api.Var v => fun h => mlSortOfVar v _
  | api.Cst c => fun h => mlSortOfCst c _
  end.
Next Obligation.
  generalize (h (api.MLV v)); clear h; intro h.
  assert (In (api.MLV v) (mlUtils.mlVarIds v)) by (unfold mlUtils.mlVarIds; simpl; tauto).
  apply h in H; clear h.
  unfold mlUtils.mlAllVariables.
  apply (imap_filter_In_intro _ _ api.isVarDec (mlUtils.modelIds mdl)
   (fun (v0 : api.mlIdent) (h1 : api.isVar v0) (_ : In v0 (mlUtils.modelIds mdl))
      => api.getVar v0 h1) (api.MLV v) I H).
Qed.
Next Obligation.
  generalize (h (api.MLC c)); clear h; intro h.
  assert (In (api.MLC c) (mlUtils.mlCstIds c)) by (unfold mlUtils.mlCstIds; simpl; tauto).
  apply h in H; clear h.
  unfold mlUtils.mlAllConstants.
  apply (imap_filter_In_intro _ _ api.isCstDec (mlUtils.modelIds mdl)
   (fun (v0 : api.mlIdent) (h1 : api.isCst v0) (_ : In v0 (mlUtils.modelIds mdl))
      => api.getCst v0 h1) (api.MLC c) I H).
Qed.

Lemma mlSortOfTerm_mlSort2Sort: forall t h i,
  mlSortOfTerm t h = mlSort2Sort (api.termSort t) i.
Proof.
  intros.
  destruct t; simpl.
  destruct v as [v h1].
  unfold api.termSort, mlSortOfVar, mlSort2Sort in *; simpl in *.
  f_equal.
  apply proof_irrelevance.

  destruct c as [c h1].
  unfold api.termSort, mlSortOfCst, mlSort2Sort in *; simpl in *.
  f_equal.
  apply proof_irrelevance.
Qed.

Program Definition mlVar2Var (v: api.variable) h: foltl.variable (Sig:=coqSig) (mlSortOfVar v h) :=
  exist _ v _.
Next Obligation.
  unfold mlUtils.variables.
  apply filter_In.
  split; auto.
  destruct (string_dec (api.var_sort v) (api.var_sort v)); tauto.
Qed.

Program Definition mlCst2Cst (c: api.constant) h: foltl.constant (Sig:=coqSig) (mlSortOfCst c h) :=
  exist _ c _.
Next Obligation.
  unfold mlUtils.constants.
  apply filter_In.
  split; auto.
  destruct (string_dec (api.cst_sort c) (api.cst_sort c)); tauto.
Qed.

Definition term2Term t: forall h, foltl.term coqSig (mlSortOfTerm t h) :=
  match t return forall h, foltl.term coqSig (mlSortOfTerm t h) with
    api.Var v => fun h => foltl.Var coqSig _ (mlVar2Var v (mlSortOfTerm_obligation_1 v h))
  | api.Cst c => fun h => foltl.Cst coqSig _ (mlCst2Cst c (mlSortOfTerm_obligation_2 c h))
  end.

Definition relation2Pred p (h: List.In p (mlUtils.relations mdl)): foltl.predicate (Sig:=coqSig) :=
  exist _ p h.

Program Definition mlLiteral2Literal x p al (h: List.incl (mlUtils.mlLitIds p al) (mlUtils.modelIds mdl)): foltl.literal coqSig :=
    let r := {| api.rel_name := p; api.rel_profile := List.map api.termSort al |} in
      foltl.PApp coqSig x (relation2Pred r _) 
        (fun i => term2Term (fnth al i) _).
Next Obligation.
  revert h; set (r:={| api.rel_name := p; api.rel_profile := map api.termSort al |}); intros.
  unfold mlUtils.relations.
  unfold mlUtils.mlRelIds in h.
  generalize (h (api.MLR r) (or_introl eq_refl)); clear h; intro h.
  apply (imap_filter_In_intro _ _ api.isMLRelDec (mlUtils.modelIds mdl)
   (fun (v0 : api.mlIdent) (h1 : api.isMLRel v0) (_ : In v0 (mlUtils.modelIds mdl))
      => api.getMLRel v0 h1) (api.MLR r) I h).
Qed.
Next Obligation.
  apply map_length.
Qed.
Next Obligation.
  generalize (mlLiteral2Literal_obligation_2 p al h).
  generalize (mlLiteral2Literal_obligation_1 p al h); intros.
  apply incl_cons_inv in h; apply proj2 in h.
  apply incl_app_inv in h; apply proj2 in h.
  revert h; apply incl_tran.
  unfold relation2Pred in e; simpl in e.
  revert i; rewrite e; intro; simpl.
  apply incl_concat_r_intro with (i := (rew [Fin.t] (eq_sym (map_length mlUtils.termIds al)) in i)).
  rewrite fnth_map.
  generalize (map_length mlUtils.termIds al); intro.
  revert i i0 e; rewrite e0; intros; simpl.
  apply incl_refl.
Qed.
Next Obligation.
  generalize (mlLiteral2Literal_obligation_3 p al h i).
  generalize (mlLiteral2Literal_obligation_2 p al h).
  generalize (mlLiteral2Literal_obligation_1 p al h); intros.
  simpl in e.
  generalize (mlUtils.mlSortOfRelAritiesIn mdl {| api.rel_name := p; api.rel_profile := map api.termSort al |} i0
     (fnth (map api.termSort al) i) (fnth_In (map api.termSort al) i)); intro.
  simpl in i1.
  revert i2; rewrite fnth_map; intros.
  revert i2; generalize (map_length api.termSort al); intros.
  revert i2; rewrite (proof_irrelevance _ e0 e); clear e0; intro.
  change (fun H => Fin.t H) with Fin.t in *.
  revert i1 i2; generalize (fnth al (rew [Fin.t] e in i)); intros.
  rewrite mlSortOfTerm_mlSort2Sort with (i:=i2).
  reflexivity.
Qed.

Lemma termSortInIds: forall t, In (api.MLS (api.termSort t)) (mlUtils.termIds t).
Proof.
  intros.
  destruct t; simpl; tauto.
Qed.

Lemma termIn2termSortIn: forall t,
  incl (mlUtils.termIds t) (mlUtils.modelIds mdl) -> In (api.termSort t) (mlUtils.mlSorts mdl).
Proof.
  intros.
  generalize (termSortInIds t); intro.
  apply H in H0; clear H.
  apply (imap_filter_In_intro _ _ api.isMLSortDec (mlUtils.modelIds mdl)
   (fun (v0 : api.mlIdent) (h1 : api.isMLSort v0) (_ : In v0 (mlUtils.modelIds mdl))
      => api.getMLSort v0 h1) (api.MLS _) I H0).  
Qed.

Program Definition literal2Atom a : List.incl (mlUtils.mlAtomIds a) (mlUtils.modelIds mdl) -> foltl.formula coqSig :=
  match a return List.incl (mlUtils.mlAtomIds a) (mlUtils.modelIds mdl) -> foltl.formula coqSig with
  | api.Pos_app x r args => fun h => foltl.Atom _ (foltl.Literal coqSig (mlLiteral2Literal x r args h))
  | api.Neg_app x r args => fun h => foltl.Atom _ (foltl.NLiteral coqSig (mlLiteral2Literal x r args h))
  | api.Eq t1 t2 => fun h => let (h1,h2) := incl_app_inv _ _ h in
    match (string_dec (api.termSort t1) (api.termSort t2)) with
      left e => foltl.Atom coqSig (foltl.Eq coqSig (mlSortOfTerm t1 _) (term2Term t1 _) (term2Term t2 _))
    | right _ => foltl.FFalse coqSig
    end
  | api.Not_eq t1 t2 => fun h => let (h1,h2) := incl_app_inv _ _ h in
    match (string_dec (api.termSort t1) (api.termSort t2)) with
      left e => foltl.Atom coqSig (foltl.NEq coqSig (mlSortOfTerm t1 _) (term2Term t1 _) (term2Term t2 _))
    | right _ => foltl.FTrue coqSig
    end
  end.
Next Obligation.
  rewrite mlSortOfTerm_mlSort2Sort with (i:=termIn2termSortIn _ h1).
  rewrite mlSortOfTerm_mlSort2Sort with (i:=termIn2termSortIn _ h2).
  generalize (termIn2termSortIn t1 h1); rewrite e; intro.
  f_equal; apply proof_irrelevance.
Qed.
Next Obligation.
  rewrite mlSortOfTerm_mlSort2Sort with (i:=termIn2termSortIn _ h1).
  rewrite mlSortOfTerm_mlSort2Sort with (i:=termIn2termSortIn _ h2).
  generalize (termIn2termSortIn t1 h1); rewrite e; intro.
  f_equal; apply proof_irrelevance.
Qed.

Lemma  mlEx_Var_In: forall {v b},
  incl (mlUtils.formulaIds (api.Exists v b)) (mlUtils.modelIds mdl) ->
    In v (mlUtils.mlAllVariables mdl).
Proof.
  simpl; intros.
  apply incl_cons_inv in H; apply proj2 in H.
  apply incl_cons_inv in H; apply proj1 in H.
  unfold mlUtils.mlAllVariables.
  apply (imap_filter_In_intro _ _ api.isVarDec (mlUtils.modelIds mdl)
   (fun (v0 : api.mlIdent) (h1 : api.isVar v0) (_ : In v0 (mlUtils.modelIds mdl))
      => api.getVar v0 h1) (api.MLV _) I H).
Qed.

Lemma  mlEx_bdy_incl: forall {v b},
  incl (mlUtils.formulaIds (api.Exists v b)) (mlUtils.modelIds mdl) ->
    incl (mlUtils.formulaIds b) (mlUtils.modelIds mdl).
Proof.
  simpl; intros.
  apply incl_cons_inv in H; apply proj2 in H.
  apply incl_cons_inv in H; apply proj2 in H.
  apply H.
Qed.

Lemma  mlAll_Var_In: forall {v b},
  incl (mlUtils.formulaIds (api.All v b)) (mlUtils.modelIds mdl) ->
    In v (mlUtils.mlAllVariables mdl).
Proof.
  simpl; intros.
  apply incl_cons_inv in H; apply proj2 in H.
  apply incl_cons_inv in H; apply proj1 in H.
  unfold mlUtils.mlAllVariables.
  apply (imap_filter_In_intro _ _ api.isVarDec (mlUtils.modelIds mdl)
   (fun (v0 : api.mlIdent) (h1 : api.isVar v0) (_ : In v0 (mlUtils.modelIds mdl))
      => api.getVar v0 h1) (api.MLV _) I H).
Qed.

Lemma  mlAll_bdy_incl: forall {v b},
  incl (mlUtils.formulaIds (api.All v b)) (mlUtils.modelIds mdl) ->
    incl (mlUtils.formulaIds b) (mlUtils.modelIds mdl).
Proof.
  simpl; intros.
  apply incl_cons_inv in H; apply proj2 in H.
  apply incl_cons_inv in H; apply proj2 in H.
  apply H.
Qed.

Fixpoint formula2formula f: List.incl (mlUtils.formulaIds f) (mlUtils.modelIds mdl) -> foltl.formula coqSig := 
  match f return List.incl (mlUtils.formulaIds f) (mlUtils.modelIds mdl) -> foltl.formula coqSig with
    api.True => fun h => foltl.FTrue coqSig
  | api.False => fun h => foltl.FFalse coqSig
  | api.Lit a => literal2Atom a
  | api.And f1 f2 => fun h => 
    let (h1,h2) := incl_app_inv _ _ h in
    foltl.And coqSig (formula2formula f1 h1) (formula2formula f2 h2)
  | api.Or f1 f2 => fun h => 
    let (h1,h2) := incl_app_inv _ _ h in
    foltl.Or coqSig (formula2formula f1 h1) (formula2formula f2 h2)
  | api.Exists v b => fun h => foltl.Ex coqSig _ (mlVar2Var v (mlEx_Var_In h)) (formula2formula b (mlEx_bdy_incl h))
  | api.All v b => fun h => foltl.All coqSig _ (mlVar2Var v (mlAll_Var_In h)) (formula2formula b (mlAll_bdy_incl h))
  | api.F f' => fun h => foltl.F coqSig (formula2formula f' h)
  | api.G f' => fun h => foltl.G coqSig (formula2formula f' h)
  end.

End ML2Coq.
