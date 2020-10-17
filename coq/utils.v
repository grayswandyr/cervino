
Require Import ProofIrrelevance.

Require Import List.
Require Import Fin.
Require Import Init.Logic.
Import  EqNotations.

Fixpoint imap_filter {T U} {p: T->Prop} (P: forall x, {p x}+{not (p x)}) (l: list T):  (forall x, p x -> List.In x l -> U) -> list U :=
  match l return (forall x, p x -> List.In x l -> U) -> list U with
    nil => fun f => nil
  | cons x l' => match P x with 
    left hp => fun f => f x hp (or_introl eq_refl)::imap_filter P l' (fun x h1 h2 => f x h1 (or_intror h2))
   | right _ => fun f => imap_filter P l' (fun x h1 h2 => f x h1 (or_intror h2))
   end
  end.

Fixpoint imap {T U} (l: list T):  (forall x, List.In x l -> U) -> list U :=
  match l return (forall x, List.In x l -> U) -> list U with
    nil => fun f => nil
  | cons x l' => fun f => f x (or_introl eq_refl)::imap l' (fun x h => f x (or_intror h))
  end.

Fixpoint fmap {T} {n} : (Fin.t n -> T) -> list T :=
  match n return (Fin.t n -> T) -> list T with
    0 => fun f => nil
  | S p => fun f => cons (f F1) (fmap (fun x => f (FS x)))
  end.

Lemma imap_filter_In_intro: forall T U {p: T->Prop} (P: forall x, {p x}+{not (p x)}) (l: list T) (f: forall x, p x -> List.In x l -> U),
  forall x (h1: p x) (h2: In x l), List.In (f x h1 h2) (imap_filter P l f).
Proof.
  induction l; simpl; intros; auto.
  destruct (P a); try tauto.
  destruct h2.
  subst x.
  left.
  f_equal.
  apply proof_irrelevance.
  right.
  apply (IHl (fun x h1 h2 => f x h1 (or_intror h2)) x h1 i).
  destruct h2.
  subst x; destruct (n h1).
  apply (IHl (fun x h1 h2 => f x h1 (or_intror h2)) x h1 i).  
Qed.

Lemma imap_filiter_in_elim: forall T U {p: T->Prop} (P: forall x, {p x}+{not (p x)}) (l: list T) (f: forall x, p x -> List.In x l -> U),
  forall v, List.In v (imap_filter P l f) -> exists u h1 h2, v = f u h1 h2.
Proof.
  induction l; simpl; intros; auto.
  destruct H.
  destruct (P a).
  destruct H.
  exists a; exists p0; exists (or_introl eq_refl).
  symmetry; apply H.
  
  apply IHl in H.
  destruct H as [u [h1 [h2 h3]]].
  exists u; exists h1; exists (or_intror h2); auto.

  apply IHl in H.
  destruct H as [u [h1 [h2 h3]]].
  exists u; exists h1; exists (or_intror h2); auto.  
Qed.

Fixpoint map_filter {T U} {p: T->Prop} (P: forall x, {p x}+{not (p x)}) (f: forall x, p x -> U) (l: list T): list U :=
  match l with
    nil => nil
  | cons x l' => match P x with 
    left h => f x h::map_filter P f l'
   | right _ => map_filter P f l'
   end
  end.

Fixpoint fnth {T} (l: list T):  Fin.t (List.length l) -> T :=
  match l as l return Fin.t (List.length l) -> T with
    nil => case0 _
  | cons x l' => fun (i: Fin.t (S (List.length l'))) =>
    caseS' i (fun _ => T) x (fun j => fnth l' j)
  end.

Lemma fnth_In: forall {T} (l: list T) (i: Fin.t (List.length l)),
  List.In (fnth l i) l.
Proof.
  induction l; simpl; intros; auto.
  inversion i.
  apply (caseS' i); simpl; intros; auto.
Qed.

Lemma fnth_map: forall {T U} (f: T->U) (l: list T) (i: Fin.t (List.length (List.map f l))),
  fnth (map f l) i = f (fnth l (rew (map_length f l) in i)).
Proof.
  induction l; simpl; intros; auto.
  inversion i.
  
  apply (caseS' i); simpl; intros; auto.
  f_equal.
  generalize (map_length f (a::l)); simpl; intro.
  generalize (fun j : t (length l) => fnth l j) as g.
  injection e; intro e'.
  revert i e; rewrite <-e'; intros.
  rewrite (proof_irrelevance _ e eq_refl); simpl; now auto.
  
  rewrite IHl; clear IHl.
  f_equal.
  generalize (map_length f (a::l)); simpl; intro.
  injection e; intro e'.
  rewrite (proof_irrelevance _ _ e').
  assert ((rew [t] e in FS p) = FS (rew [t] e' in p)).
  revert e p; rewrite e'; simpl; intros.
  rewrite (proof_irrelevance _ e eq_refl); simpl; now auto.
  rewrite H; simpl; now auto.
Qed.

Lemma incl_concat_r_intro: forall T (l1: list T) l2 i, incl l1 (fnth l2 i) -> incl l1 (concat l2).
Proof.
  induction l2; simpl; intros; auto.
  inversion i.
  
  revert H; apply (caseS' i); simpl in *; intros.
  apply incl_appl; now auto.
  apply incl_appr.
  revert H; apply IHl2.
Qed.

Lemma in_fnth: forall T (l: list T) x, In x l -> exists i, x = fnth l i.
Proof.
  induction l; simpl; intros; auto; try tauto.
  destruct H.
  exists F1; subst x; simpl; now auto.
  apply IHl in H.
  destruct H as [i H].
  exists (FS i); simpl; auto.
Qed.

Lemma in_concat_map_intro: forall {T1 T2} (f:T1->list T2) l1 (l2: list T2), (exists i, incl l2 (f (fnth l1 i))) -> incl l2 (concat (map f l1)).
Proof.
  intros.
  destruct H.
  generalize (map_length f l1); intro.
  apply incl_concat_r_intro with (i := rew [Fin.t] (eq_sym H0) in x).
  rewrite fnth_map.
  generalize (map_length f l1); intro.
  rewrite (proof_irrelevance _ H0 e); clear H0.
  rewrite e; simpl; auto.
Qed.

Lemma In_app_imp_In_app: forall {T1 T2} (x1:T1) (x2:T2) l1 m1 l2 m2,
  (List.In x1 l1 -> List.In x2 l2) ->
  (List.In x1 m1 -> List.In x2 m2) ->
  (List.In x1 (l1 ++ m1) -> List.In x2 (l2 ++ m2)).
Proof.
  intros.
  rewrite in_app_iff in H1; apply in_app_iff.
  destruct H1; [left|right]; auto.
Qed.

Lemma In_cmap_In_cmap: forall T1 T2 (f: T1-> list T2) x1 x2 l,
  (forall x, In x1 (f x) -> In x2 (f x)) ->
  (In x1 (List.concat (map f l)) -> In x2 (List.concat (map f l))).
Proof.
  induction l; simpl; intros; auto.
  apply in_app_iff in H0; apply in_app_iff.
  destruct H0; [left|right]; auto.
Qed.
