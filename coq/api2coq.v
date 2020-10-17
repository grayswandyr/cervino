
Require Import String.
Require Import List.
Require Coq.Arith.PeanoNat.
Require Import ProofIrrelevance.
Require Import Init.Logic.
Import  EqNotations.

Require Import api.
Require Import mlUtils.
Require Import foltl.
Require Import finite.
Require Import dec.
Require Import utils.

Instance StrDec : EqDec := {| eq_dec := string_dec |}.
Instance NatDec : EqDec := {| eq_dec := Coq.Arith.PeanoNat.Nat.eq_dec |}.

Section ML2Coq.
Variable mdl : mlModel.

Definition mlSorts2Sort : SortT := asFinite (mlSorts mdl).
Definition mlSort2Sort (s: mlSort) (h: List.In s (mlSorts mdl)) : mlSorts2Sort :=
 exist _ s h.

Instance mlVariableDec: @EqDec mlVariable.
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

Instance mlConstantDec: @EqDec mlConstant.
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

Instance mlRelationDec: @EqDec mlRelation.
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

Program Definition coqSig : Sig := {|
  Sort := mlSorts2Sort;
  variable s := asFinite (mlVariables mdl (proj1_sig s));
  constant s := asFinite (mlConstants mdl (proj1_sig s));
  predicate := asFinite (mlRelations mdl);
  pr_arity p := List.length (mlRelArity (proj1_sig p));
  pr_args p i := exist _ (fnth (mlRelArity (proj1_sig p)) i) _
|}.
Next Obligation.
  destruct p as [r h]; simpl in *.
  apply (mlSortOfRelAritiesIn mdl r h).
  apply fnth_In.
Defined.

Definition mlSortOfVar v h: Sort (Sig:=coqSig) :=
  (mlSort2Sort (mlVarSort v) (mlSortOfVarsIn mdl v h)).

Definition mlSortOfCst v h: Sort (Sig:=coqSig) :=
  (mlSort2Sort (mlCstSort v) (mlSortOfCstsIn mdl v h)).

Program Definition mlSortOfTerm t: List.incl (mlTermIds t) (mlModelIds mdl) -> Sort (Sig:=coqSig) := 
  match t return List.incl (mlTermIds t) (mlModelIds mdl) -> _ with
    MLVar v => fun h => mlSortOfVar v _
  | MLCst c => fun h => mlSortOfCst c _
  end.
Next Obligation.
  generalize (h (MLV v)); clear h; intro h.
  assert (In (MLV v) (mlVarIds v)) by (unfold mlVarIds; simpl; tauto).
  apply h in H; clear h.
  unfold mlAllVariables.
  apply (imap_filter_In_intro _ _ isMLVarDec (mlModelIds mdl)
   (fun (v0 : mlIdent) (h1 : isMLVar v0) (_ : In v0 (mlModelIds mdl))
      => getMLVar v0 h1) (MLV v) I H).
Qed.
Next Obligation.
  generalize (h (MLC c)); clear h; intro h.
  assert (In (MLC c) (mlCstIds c)) by (unfold mlCstIds; simpl; tauto).
  apply h in H; clear h.
  unfold mlAllConstants.
  apply (imap_filter_In_intro _ _ isMLCstDec (mlModelIds mdl)
   (fun (v0 : mlIdent) (h1 : isMLCst v0) (_ : In v0 (mlModelIds mdl))
      => getMLCst v0 h1) (MLC c) I H).
Qed.

Lemma mlSortOfTerm_mlSort2Sort: forall t h i,
  mlSortOfTerm t h = mlSort2Sort (mlTermSort t) i.
Proof.
  intros.
  destruct t; simpl.
  destruct v as [v h1].
  unfold mlTermSort, mlSortOfVar, mlSort2Sort in *; simpl in *.
  f_equal.
  apply proof_irrelevance.

  destruct c as [c h1].
  unfold mlTermSort, mlSortOfCst, mlSort2Sort in *; simpl in *.
  f_equal.
  apply proof_irrelevance.
Qed.

Program Definition mlVar2Var (v: mlVariable) h: variable (Sig:=coqSig) (mlSortOfVar v h) :=
  exist _ v _.
Next Obligation.
  unfold mlVariables.
  apply filter_In.
  split; auto.
  destruct (string_dec (mlVarSort v) (mlVarSort v)); tauto.
Qed.

Program Definition mlCst2Cst (c: mlConstant) h: constant (Sig:=coqSig) (mlSortOfCst c h) :=
  exist _ c _.
Next Obligation.
  unfold mlConstants.
  apply filter_In.
  split; auto.
  destruct (string_dec (mlCstSort c) (mlCstSort c)); tauto.
Qed.

Definition mlTerm2Term t: forall h, term coqSig (mlSortOfTerm t h) :=
  match t return forall h, term coqSig (mlSortOfTerm t h) with
    MLVar v => fun h => Var coqSig _ (mlVar2Var v (mlSortOfTerm_obligation_1 v h))
  | MLCst c => fun h => Cst coqSig _ (mlCst2Cst c (mlSortOfTerm_obligation_2 c h))
  end.

Definition mlRelation2Pred p (h: List.In p (mlRelations mdl)): predicate (Sig:=coqSig) :=
  exist _ p h.

Program Definition mlLiteral2Literal l:  List.incl (mlLitIds l) (mlModelIds mdl) -> literal coqSig :=
  match l return List.incl(mlLitIds l) (mlModelIds mdl) -> literal coqSig with
    MLPApp x p al => fun h =>
      let r := {| mlRelName := p; mlRelArity := List.map mlTermSort al |} in
      PApp coqSig x (mlRelation2Pred r _) 
        (fun i => mlTerm2Term (fnth al i) _)
  end.
Next Obligation.
  revert h; set (r:={| mlRelName := p; mlRelArity := map mlTermSort al |}); intros.
  unfold mlRelations.
  unfold mlRelIds in h.
  generalize (h (MLR r) (or_introl eq_refl)); clear h; intro h.
  apply (imap_filter_In_intro _ _ isMLRelDec (mlModelIds mdl)
   (fun (v0 : mlIdent) (h1 : isMLRel v0) (_ : In v0 (mlModelIds mdl))
      => getMLRel v0 h1) (MLR r) I h).
Qed.
Next Obligation.
  apply map_length.
Qed.
Next Obligation.
  generalize (mlLiteral2Literal_obligation_2 x p al h).
  generalize (mlLiteral2Literal_obligation_1 x p al h); intros.
  apply incl_cons_inv in h; apply proj2 in h.
  apply incl_app_inv in h; apply proj2 in h.
  revert h; apply incl_tran.
  unfold mlRelation2Pred in e; simpl in e.
  revert i; rewrite e; intro; simpl.
  apply incl_concat_r_intro with (i := (rew [Fin.t] (eq_sym (map_length mlTermIds al)) in i)).
  rewrite fnth_map.
  generalize (map_length mlTermIds al); intro.
  revert i i0 e; rewrite e0; intros; simpl.
  apply incl_refl.
Qed.
Next Obligation.
  generalize (mlLiteral2Literal_obligation_3 x p al h i).
  generalize (mlLiteral2Literal_obligation_2 x p al h).
  generalize (mlLiteral2Literal_obligation_1 x p al h); intros.
  simpl in e.
  generalize (mlSortOfRelAritiesIn mdl {| mlRelName := p; mlRelArity := map mlTermSort al |} i0
     (fnth (map mlTermSort al) i) (fnth_In (map mlTermSort al) i)); intro.
  simpl in i1.
  revert i2; rewrite fnth_map; intros.
  revert i2; generalize (map_length mlTermSort al); intros.
  revert i2; rewrite (proof_irrelevance _ e0 e); clear e0; intro.
  change (fun H => Fin.t H) with Fin.t in *.
  revert i1 i2; generalize (fnth al (rew [Fin.t] e in i)); intros.
  rewrite mlSortOfTerm_mlSort2Sort with (i:=i2).
  reflexivity.
Qed.

Lemma mlTermSortInIds: forall t, In (MLS (mlTermSort t)) (mlTermIds t).
Proof.
  intros.
  destruct t; simpl; tauto.
Qed.

Lemma mlTermIn2mlTermSortIn: forall t,
  incl (mlTermIds t) (mlModelIds mdl) -> In (mlTermSort t) (mlSorts mdl).
Proof.
  intros.
  generalize (mlTermSortInIds t); intro.
  apply H in H0; clear H.
  apply (imap_filter_In_intro _ _ isMLSortDec (mlModelIds mdl)
   (fun (v0 : mlIdent) (h1 : isMLSort v0) (_ : In v0 (mlModelIds mdl))
      => getMLSort v0 h1) (MLS _) I H0).  
Qed.

Program Definition mlAtom2Atom a : List.incl (mlAtomIds a) (mlModelIds mdl) -> formula coqSig :=
  match a return List.incl (mlAtomIds a) (mlModelIds mdl) -> formula coqSig with
  | MLLiteral l => fun h => Atom _ (Literal coqSig (mlLiteral2Literal l h))
  | MLNLiteral l => fun h => Atom _ (NLiteral coqSig (mlLiteral2Literal l h))
  | MLEq t1 t2 => fun h => let (h1,h2) := incl_app_inv _ _ h in
    match (string_dec (mlTermSort t1) (mlTermSort t2)) with
      left e => Atom coqSig (Eq coqSig (mlSortOfTerm t1 _) (mlTerm2Term t1 _) (mlTerm2Term t2 _))
    | right _ => FFalse coqSig
    end
  | MLNEq t1 t2 => fun h => let (h1,h2) := incl_app_inv _ _ h in
    match (string_dec (mlTermSort t1) (mlTermSort t2)) with
      left e => Atom coqSig (NEq coqSig (mlSortOfTerm t1 _) (mlTerm2Term t1 _) (mlTerm2Term t2 _))
    | right _ => FTrue coqSig
    end
  end.
Next Obligation.
  rewrite mlSortOfTerm_mlSort2Sort with (i:=mlTermIn2mlTermSortIn _ h1).
  rewrite mlSortOfTerm_mlSort2Sort with (i:=mlTermIn2mlTermSortIn _ h2).
  generalize (mlTermIn2mlTermSortIn t1 h1); rewrite e; intro.
  f_equal; apply proof_irrelevance.
Qed.
Next Obligation.
  rewrite mlSortOfTerm_mlSort2Sort with (i:=mlTermIn2mlTermSortIn _ h1).
  rewrite mlSortOfTerm_mlSort2Sort with (i:=mlTermIn2mlTermSortIn _ h2).
  generalize (mlTermIn2mlTermSortIn t1 h1); rewrite e; intro.
  f_equal; apply proof_irrelevance.
Qed.

Lemma  mlEx_Var_In: forall {v b},
  incl (mlFormulaIds (MLEx v b)) (mlModelIds mdl) ->
    In v (mlAllVariables mdl).
Proof.
  simpl; intros.
  apply incl_cons_inv in H; apply proj2 in H.
  apply incl_cons_inv in H; apply proj1 in H.
  unfold mlAllVariables.
  apply (imap_filter_In_intro _ _ isMLVarDec (mlModelIds mdl)
   (fun (v0 : mlIdent) (h1 : isMLVar v0) (_ : In v0 (mlModelIds mdl))
      => getMLVar v0 h1) (MLV _) I H).
Qed.

Lemma  mlEx_bdy_incl: forall {v b},
  incl (mlFormulaIds (MLEx v b)) (mlModelIds mdl) ->
    incl (mlFormulaIds b) (mlModelIds mdl).
Proof.
  simpl; intros.
  apply incl_cons_inv in H; apply proj2 in H.
  apply incl_cons_inv in H; apply proj2 in H.
  apply H.
Qed.

Lemma  mlAll_Var_In: forall {v b},
  incl (mlFormulaIds (MLAll v b)) (mlModelIds mdl) ->
    In v (mlAllVariables mdl).
Proof.
  simpl; intros.
  apply incl_cons_inv in H; apply proj2 in H.
  apply incl_cons_inv in H; apply proj1 in H.
  unfold mlAllVariables.
  apply (imap_filter_In_intro _ _ isMLVarDec (mlModelIds mdl)
   (fun (v0 : mlIdent) (h1 : isMLVar v0) (_ : In v0 (mlModelIds mdl))
      => getMLVar v0 h1) (MLV _) I H).
Qed.

Lemma  mlAll_bdy_incl: forall {v b},
  incl (mlFormulaIds (MLAll v b)) (mlModelIds mdl) ->
    incl (mlFormulaIds b) (mlModelIds mdl).
Proof.
  simpl; intros.
  apply incl_cons_inv in H; apply proj2 in H.
  apply incl_cons_inv in H; apply proj2 in H.
  apply H.
Qed.

Fixpoint mlFormula2formula f: List.incl (mlFormulaIds f) (mlModelIds mdl) -> formula coqSig := 
  match f return List.incl (mlFormulaIds f) (mlModelIds mdl) -> formula coqSig with
    MLFTrue => fun h => FTrue coqSig
  | MLFFalse => fun h => FFalse coqSig
  | MLAtom a => mlAtom2Atom a
  | MLAnd f1 f2 => fun h => 
    let (h1,h2) := incl_app_inv _ _ h in
    And coqSig (mlFormula2formula f1 h1) (mlFormula2formula f2 h2)
  | MLOr f1 f2 => fun h => 
    let (h1,h2) := incl_app_inv _ _ h in
    Or coqSig (mlFormula2formula f1 h1) (mlFormula2formula f2 h2)
  | MLEx v b => fun h => Ex coqSig _ (mlVar2Var v (mlEx_Var_In h)) (mlFormula2formula b (mlEx_bdy_incl h))
  | MLAll v b => fun h => All coqSig _ (mlVar2Var v (mlAll_Var_In h)) (mlFormula2formula b (mlAll_bdy_incl h))
  | MLF f' => fun h => F coqSig (mlFormula2formula f' h)
  | MLG f' => fun h => G coqSig (mlFormula2formula f' h)
  end.

End ML2Coq.
