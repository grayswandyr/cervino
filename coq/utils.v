
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

