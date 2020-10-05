
Require Import foltl.
Require Import varset.
Require Import dec.
Require Import finite.
Require Import set.

Section Vars.

Context {Ts: Type} {Tv: Ts->Type} {Tc: Ts->Type} {Tp: Type}.
Variable Sg: @Sig Ts Tv Tc Tp.

Definition tm_vars {s'} (tm: term Sg s'): VarSet Sg :=
  match tm with
    Var _ _ v => vsSing Sg v
  | Cst _ _ s => vsEmpty Sg
  end.

Definition lt_vars lt: VarSet Sg :=
  match lt with
    PApp _ n p args => vsGUnion Sg (fun i => tm_vars (args i))
  end.

Definition at_vars a : VarSet Sg :=
  match a with
  | Literal _ a | NLiteral _ a => lt_vars a
  | Eq _ _ t1 t2 | NEq _ _ t1 t2 => vsUnion Sg (tm_vars t1) (tm_vars t2)
  end.

Fixpoint fm_vars f : VarSet Sg :=
  match f with
  | FTrue _ | FFalse _ => vsEmpty Sg
  | Atom _ a => at_vars a
  | And _ f1 f2 | Or _ f1 f2 => vsUnion Sg (fm_vars f1) (fm_vars f2)
  | Ex _ s v f | All _ s v f => fm_vars f
  | F _ f | G _ f => fm_vars f
  end.

Definition removeVars `{K: Finite} {sk: K->Sort} (vk: forall k, variable (sk k)) (e:VarSet Sg): VarSet Sg :=
  fun s => SV.Filter (fun (x:variable s) => NotDec (ExDecidable (ex_dec (fun k => isEq2 (U:=variable) s x (sk k) (vk k))))) (e s).
  
Definition at_free a: VarSet Sg :=
  match a with
  | Literal _ lt | NLiteral _ lt => lt_vars lt
  | Eq _ _ t1 t2 | NEq _ _ t1 t2 => vsUnion Sg (tm_vars t1) (tm_vars t2)
  end.

Fixpoint free f: VarSet Sg :=
  match f with
  | FTrue _ | FFalse _ => vsEmpty Sg
  | Atom _ a => at_vars a
  | And _ f1 f2 | Or _ f1 f2 => vsUnion Sg (free f1) (free f2)
  | Ex _ s v f | All _ s v f => vsRemove Sg v (free f)
  | F _ f | G _ f => free f
  end.

  Lemma lt_free_X: forall l, lt_vars (ltX Sg l) = lt_vars l.
  Proof.
    intro.
    destruct l; simpl in *; auto.
  Qed.
  
  Lemma at_free_X: forall a, at_vars (atX Sg a) = at_vars a.
  Proof.
    intro.
    destruct a; simpl; intros; auto.
    apply lt_free_X.
    apply lt_free_X.
  Qed.
  
  Lemma free_X: forall f, free (X Sg f) = free f.
  Proof.
    induction f; simpl; intros; auto.
    apply at_free_X.
    f_equal.
    apply IHf1.
    apply IHf2.
    rewrite IHf1, IHf2; auto.
    rewrite IHf; auto.
    rewrite IHf; auto.
  Qed.
  
  Lemma free_Ex: forall s (v: variable s) f, (free (Ex Sg s v f)) = (vsRemove Sg v (free f)).
  Proof.
    intros; reflexivity.
  Qed.
  
  Lemma free_And: forall f1 f2, free (And _ f1 f2) = (vsUnion Sg (free f1) (free f2)).
  Proof.
    intros.
    reflexivity.
  Qed.

  Lemma free_Or: forall f1 f2,  free (Or _ f1 f2) = (vsUnion Sg (free f1) (free f2)).
  Proof.
    intros; reflexivity.
  Qed.

  Lemma free_IAnd_sub: forall `(K: Finite) fk, vsSubset Sg (free (IAnd _ K fk)) (vsGUnion Sg (fun k => free (fk k))).
  Proof.
    intros; unfold IAnd, vsGUnion; simpl.
    induction fin_set; simpl; intros; auto.
    repeat intro.
    destruct H.
    
    repeat intro.
    apply vsUnion_elim in H.
    destruct H.
    apply SV.InCUnion_intro with (u:=a); simpl; now auto.
    apply IHs in H; clear IHs.
    apply SV.InCUnion_elim in H.
    destruct H as [u [h1 h2]].
    apply SV.InCUnion_intro with (u0:=u); simpl; intros; auto.
    apply h2.
    apply h1.
  Qed.
  
  Lemma free_IAnd_sup: forall `(K: Finite) fk, vsSubset Sg (vsGUnion Sg (fun k => free (fk k))) (free (IAnd Sg K fk)).
  Proof.
    intros; unfold IAnd, vsGUnion; simpl.
    induction fin_set; simpl; intros; auto.
    repeat intro.
    destruct H.
    
    repeat intro.
    apply SV.InCUnion_elim in H; simpl in H.
    destruct H as [u [h1 [h2 h3]]].
    apply h3 in h1; clear h3.
    destruct h2.
    subst u.
    apply vsUnion_l; now auto.
    apply vsUnion_r.
    apply IHs; auto.
    apply SV.InCUnion_intro with (u0:=u); auto.
  Qed.

  Lemma free_IOr_sub: forall `(K: Finite) fk, vsSubset Sg (free (IOr Sg K fk)) (vsGUnion Sg (fun k => free (fk k))).
  Proof.
    intros; unfold IOr, vsGUnion; simpl.
    induction fin_set; simpl; intros; auto.
    repeat intro.
    destruct H.
    
    repeat intro.
    apply vsUnion_elim in H.
    destruct H.
    apply SV.InCUnion_intro with (u:=a); simpl; now auto.
    apply IHs in H; clear IHs.
    apply SV.InCUnion_elim in H.
    destruct H as [u [h1 h2]].
    apply SV.InCUnion_intro with (u0:=u); simpl; intros; auto.
    apply h2.
    apply h1.
  Qed.
  
  Lemma free_IOr_sup: forall `(K: Finite) fk, vsSubset Sg (vsGUnion Sg (fun k => free (fk k))) (free (IOr Sg K fk)).
  Proof.
    intros; unfold IOr, vsGUnion; simpl.
    induction fin_set; simpl; intros; auto.
    repeat intro.
    destruct H.
    
    repeat intro.
    apply SV.InCUnion_elim in H; simpl in H.
    destruct H as [u [h1 [h2 h3]]].
    apply h3 in h1; clear h3.
    destruct h2.
    subst u.
    apply vsUnion_l; now auto.
    apply vsUnion_r.
    apply IHs; auto.
    apply SV.InCUnion_intro with (u0:=u); auto.
  Qed.
  
End Vars.

