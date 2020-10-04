Add LoadPath "$HOME/COQ/FO-LTL" as Top.

Require Import String.
Require Import List.
Require Coq.Arith.PeanoNat.
Require Import ProofIrrelevance.
Require Import Init.Logic.
Import  EqNotations.

Require Import Top.api.
Require Import Top.foltl.
Require Import Top.finite.
Require Import Top.dec.
Require Import Top.utils.

Instance StrDec : EqDec := {| eq_dec := string_dec |}.
Instance NatDec : EqDec := {| eq_dec := Coq.Arith.PeanoNat.Nat.eq_dec |}.

Module ML2Coq (Sg: MLSignature).
Module Import Cervino := MLCervino(Sg).

Definition mlSorts2Sort : SortT := asFinite (mlSorts Sg.sg).
Definition mlSort2Sort (s: mlSort) (h: List.In s (mlSorts Sg.sg)) : mlSorts2Sort :=
 exist _ s h.

Instance mlVariableDec: @EqDec mlVariable.
Proof.
  split; repeat intro.
  destruct x as [v1 h1]; destruct y as [v2 h2].
  destruct (string_dec v1 v2); [left|right].
  subst v2.
  f_equal.
  apply proof_irrelevance.
  apply proof_irrelevance.

  intro.
  injection H; clear H; intro.
  apply (n H).
Defined.

Instance mlConstantDec: @EqDec mlConstant.
Proof.
  split; repeat intro.
  destruct x as [v1 h1]; destruct y as [v2 h2].
  destruct (string_dec v1 v2); [left|right].
  subst v2.
  f_equal.
  apply proof_irrelevance.
  apply proof_irrelevance.
  intro.
  injection H; clear H; intro.
  apply (n H).
Defined.

Instance mlRelationDec: @EqDec mlRelation.
Proof.
  split; repeat intro.
  destruct x as [v1 h1]; destruct y as [v2 h2].
  destruct (string_dec v1 v2); [left|right].
  subst v2.
  f_equal.
  apply proof_irrelevance.
  apply proof_irrelevance.
  intro.
  injection H; clear H; intro.
  apply (n H).
Defined.

(*
Definition mlRelDec : EqDec (T := mlRelation).
Proof.
  split; repeat intro.
  destruct x as [n1 a1 l1]; destruct y as [n2 a2 l2].
  destruct (string_dec n1 n2).
  subst n2; left.
Defined.

Definition mlRels2Rels : EqDec (T:=StrDec) :=
  (List.map mlRelName (mlConstants srcSig))).
*)

Definition coqSig : Sig := {|
  Sort := mlSorts2Sort;
  variable s := asFinite (mlVariables (proj1_sig s));
  constant s := asFinite (mlConstants (proj1_sig s));
  predicate := asFinite mlRelations;
  pr_arity p := List.length (mlRelArity (proj1_sig p));
  pr_args p i := 
    mlSort2Sort (fnth (mlRelArity (proj1_sig p)) i)
                  (mlRwf Sg.sg (mlRelName (proj1_sig p)) 
                                  _
                                  (mlRelationWF _)
                                  (fnth (mlRelArity (proj1_sig p)) i)
                                  (fnth_In _ i))
|}.

Definition mlSortOfVar v: Sort (Sig:=coqSig) :=
  (mlSort2Sort (mlVarSort v)
    (mlVwf Sg.sg (mlVarName v) (mlVarSort v) (mlVariableWF _) )).

Definition mlSortOfCst v: Sort (Sig:=coqSig) :=
  (mlSort2Sort (mlCstSort v)
    (mlCwf Sg.sg (mlCstName v) (mlCstSort v) (mlConstantWF _) )).

Definition mlSortOfTerm t: Sort (Sig:=coqSig) := 
  match t with
    MLVar v => mlSortOfVar v
  | MLCst c => mlSortOfCst c
  end.

Lemma mlSortOfTerm_mlSort2Sort: forall t i,
  mlSortOfTerm t = mlSort2Sort (mlTermSort t) i.
Proof.
  intros.
  destruct t; simpl.
  destruct v as [v h1 h2].
  unfold mlTermSort, mlSortOfVar, mlSort2Sort in *; simpl in *.
  f_equal.
  apply proof_irrelevance.

  destruct c as [c h1 h2].
  unfold mlTermSort, mlSortOfCst, mlSort2Sort in *; simpl in *.
  f_equal.
  apply proof_irrelevance.
Qed.

Program Definition mlVar2Var (v: mlVariable): variable (Sig:=coqSig) (mlSortOfVar v) :=
  exist _ v _.
Next Obligation.
  unfold mlVariables.
  apply filter_In.
  split.
  unfold mlAllVariables.
  set (f v h1 h2 := {| mlVarName := v; mlVar_dcl := h1; mlVar_in := h2 |}).
  assert (v = f (mlVarName v) (mlVar_dcl v) (mlVar_in v)). 
  destruct v; simpl; reflexivity.
  rewrite H.
  apply imap_filter_In_intro.
  destruct (string_dec (mlVarSort v) (mlVarSort v)); tauto.
Qed.

Program Definition mlCst2Cst (c: mlConstant): constant (Sig:=coqSig) (mlSortOfCst c) :=
  exist _ c _.
Next Obligation.
  unfold mlConstants.
  apply filter_In.
  split.
  unfold mlAllConstants.
  set (f v h1 h2 := {| mlCstName := v; mlCst_dcl := h1; mlCst_in := h2 |}).
  assert (c = f (mlCstName c) (mlCst_dcl c) (mlCst_in c)). 
  destruct c; simpl; reflexivity.
  rewrite H.
  apply imap_filter_In_intro.
  destruct (string_dec (mlCstSort c) (mlCstSort c)); tauto.
Qed.

Definition mlTerm2Term t : term coqSig (mlSortOfTerm t) :=
  match t return term coqSig (mlSortOfTerm t) with
    MLVar v => Var coqSig _ (mlVar2Var v)
  | MLCst c => Cst coqSig _ (mlCst2Cst c)
  end.

Program Definition mlRelation2Pred p : predicate (Sig:=coqSig) :=
  exist _ p _.
Next Obligation.
  unfold mlRelations.
  set (f v h1 h2 := {| mlRelName := v; mlRel_dcl := h1; mlRel_in := h2 |}).
  assert (p = f (mlRelName p) (mlRel_dcl p) (mlRel_in p)). 
  destruct p; simpl; reflexivity.
  rewrite H.
  apply imap_filter_In_intro.
Qed.

Program Definition mlLiteral2Literal l : literal coqSig :=
  match l with
    MLPApp x p al h => PApp coqSig x (mlRelation2Pred p) 
      (fun i => mlTerm2Term (fnth al i))
  end.
Next Obligation.
  rewrite h.
  apply map_length.
Qed.
Next Obligation.
  generalize ((mlRwf Sg.sg (mlRelName p) (mlRelArity p) (mlRelationWF p)
     (fnth (mlRelArity p) i) (fnth_In (mlRelArity p) i))); intro.
  generalize (mlLiteral2Literal_obligation_1 p al h); intro.
  unfold mlRelation2Pred in e; simpl in e.
  unfold isMLLit in h.
  revert i i0 e; rewrite h; intros; clear h p x.
  revert i0; rewrite (fnth_map mlTermSort al i); intro.
  revert i i0; generalize (map_length mlTermSort al); rewrite e; simpl; intros.
  rewrite <-mlSortOfTerm_mlSort2Sort.
  rewrite (proof_irrelevance _ e0 eq_refl); simpl; auto.
Qed.

Program Definition mlAtom2Atom a : atom coqSig :=
  match a with
  | MLLiteral l => Literal coqSig (mlLiteral2Literal l)
  | MLNLiteral l => NLiteral coqSig (mlLiteral2Literal l)
  | MLEq s t1 t2 h1 h2 => Eq coqSig (mlSort2Sort s _) (mlTerm2Term t1) (mlTerm2Term t2)
  | MLNEq s t1 t2 h1 h2 => NEq coqSig (mlSort2Sort s _)  (mlTerm2Term t1) (mlTerm2Term t2)
  end.
Next Obligation.
  apply mlTwf.
Defined.
Next Obligation.
  apply mlSortOfTerm_mlSort2Sort.
Defined.
Next Obligation.
  generalize (mlAtom2Atom_obligation_1 (mlTermSort t1) t1 t2 eq_refl h2).
  rewrite <-h2.
  apply mlSortOfTerm_mlSort2Sort.
Defined.
Next Obligation.
  apply mlTwf.
Defined.
Next Obligation.
  apply mlSortOfTerm_mlSort2Sort.
Defined.
Next Obligation.
  generalize (mlAtom2Atom_obligation_4 (mlTermSort t1) t1 t2 eq_refl h2).
  rewrite <-h2.
  apply mlSortOfTerm_mlSort2Sort.
Defined.

Fixpoint mlFormula2formula f: formula coqSig := 
  match f with
    MLFTrue => FTrue coqSig
  | MLFFalse => FFalse coqSig
  | MLAtom a => Atom coqSig (mlAtom2Atom a)
  | MLAnd f1 f2 => And coqSig (mlFormula2formula f1) (mlFormula2formula f2)
  | MLOr f1 f2 => Or coqSig (mlFormula2formula f1) (mlFormula2formula f2)
  | MLEx v b => Ex coqSig _ (mlVar2Var v) (mlFormula2formula b)
  | MLAll v b => Ex coqSig _ (mlVar2Var v) (mlFormula2formula b)
  | MLF f' => F coqSig (mlFormula2formula f')
  | MLG f' => G coqSig (mlFormula2formula f')
  end.

End ML2Coq.
