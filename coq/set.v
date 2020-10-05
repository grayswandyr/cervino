Set Implicit Arguments.

Require List.
Require Import dec.
Require Ensembles.
Require Import Morphisms.
Require Import Setoid.
Require Import ProofIrrelevance.  

Definition uniq {T} (l: list T) :=
  forall l1 l2, app l1 l2 = l -> forall x, List.In x l1 -> not (List.In x l2).

Lemma uniq_tl: forall {T} {a:T} {l: list T},
  uniq (cons a l) -> uniq l.
Proof.
  repeat intro.
  apply (H (cons a l1) l2) with (x:=x); auto.
  simpl.
  rewrite H0; auto.
  right; auto.
Qed.

Lemma uniq_tl_intro: forall {T} {a:T} {l: list T},
  not (List.In a l) -> uniq l -> uniq (cons a l).
Proof.
  repeat intro.
  destruct l1; simpl in *.
  destruct H2.
  injection H1; clear H1; intros.
  subst t.
  destruct H2.
  subst a.
  assert (List.In x l).
  rewrite <-H1.
  apply (proj2 (List.in_app_iff l1 l2 x)); tauto.
  tauto.
  apply (H0 l1 l2 H1 x); auto.
Qed.

Module SV.
  Import List.
  Import ListNotations.
  
  Instance InPred `(T:EqDec) (l: list T) (x:T): Decidable := {| 
     dcPred := In x l;
     dc_dec := in_dec eq_dec x l
  |}.

  Definition set `(T: EqDec) := list T.
  Definition empty `(T: EqDec): set T := [].
  Definition sing `(T: EqDec) (x:T) := [x]. (*single set*)
  Definition pair `{T: EqDec} (x y: T) := if eq_dec x y then [x] else [x;y].
  Definition card `{T: EqDec} (s: set T) := length s.

  Definition set_eq_dec `{T: EqDec} (s1 s2: set T) := List.list_eq_dec eq_dec s1 s2.

  Definition setDec `(T: EqDec): @EqDec (set T) := {| eq_dec := set_eq_dec |}.
  
  Definition set_In_dec `{T:EqDec} x (l: set T) := in_dec eq_dec x l.

  Fixpoint add `(T : EqDec) (x : T) (s : set T) : set T :=
    match s with
    | [] => sing _ x
    | hd :: tl =>
      if eq_dec x hd then
        hd :: tl
      else
        hd :: add x tl
    end.

  Fixpoint list2set `(T : EqDec) (l: list T): set T :=
    match l with
      [] => []
    | x::r => add x (list2set T r)
    end.

  Fixpoint remove `(T : EqDec) (x : T) (s : set T) : set T :=
    match s with
    | [] => []
    | hd :: tl =>
      if eq_dec x hd then
        remove x tl (* manque hyp pas de duplications *)
      else
        hd :: remove x tl
    end.

  Lemma InRemove_l: forall `{T: EqDec} (x y:T) (s: set T), In x (remove y s) -> x <> y.
  Proof.
    induction s; simpl; intros; auto.
    destruct (eq_dec y a); subst; auto.
    destruct H; auto.
    intro; subst a y; tauto.
  Qed.

  Lemma InRemove_r: forall `{T: EqDec} (x y:T) (s: set T), In x (remove y s) -> In x s.
  Proof.
    induction s; simpl; intros; auto.
    destruct (eq_dec y a); subst; auto.
    destruct H; auto.
  Qed.

  Lemma InRemove: forall `{T: EqDec} (x y:T) (s: set T), x <> y -> In x s -> In x (remove y s).
  Proof.
    induction s; simpl; intros; auto.
    destruct H0.
    subst a.
    destruct (eq_dec y x).
    subst y; tauto.
    left; reflexivity.
    destruct (eq_dec y a); auto.
    destruct (eq_dec x a).
    left; auto.
    right; auto.
  Qed.
  
  Lemma all_dec `{T: EqDec} (p: T->Decidable) (s: set T): (forall x, In x s -> p x)+{x | In x s /\ not (p x)}.
  Proof.
    induction s; simpl; intros; auto.
    left; intros.
    destruct H.
    destruct (@dc_dec (p a)).
    destruct IHs; [left|right]; intros; auto.
    destruct H.
    subst; easy.
    apply d0; apply H.
    destruct s0.
    exists x.
    split; auto.
    right; easy.
    easy.
    right.
    exists a.
    split; auto.
  Qed.

  Lemma ex_dec `{T: EqDec} (p: T->Decidable) (s: set T): {x | In x s /\ p x} + {forall x, In x s -> not (p x)}.
  Proof.
    induction s; simpl; intros; auto.
    destruct IHs.
    left.
    destruct s0 as [x [h1 h2]].
    exists x.
    split; [right; auto | apply h2].
    destruct (@dc_dec (p a)).
    left; exists a; split; [left; apply eq_refl | apply d].
    right; intros.
    destruct H.
    destruct H; apply n0.
    apply (n x H).
  Defined.

  Fixpoint first_dec `{T: EqDec} (p: T->Decidable) (s: set T): {x | In x s /\ p x} + {forall x, In x s -> not (p x)} :=
    match s with
      [] => inright (fun x h => match (h : In x []) with end)
    | x::s' => match @dc_dec (p x) with
                left d => inleft (exist _ x (conj (or_introl eq_refl) d))
               | right n =>
                  match first_dec p s' with
                    inright no => inright (fun y h => 
                      match h with
                        | or_introl h' => match h' in (_ = y) return (~ p y) with
                                                | eq_refl => n
                                          end
                        | or_intror h' => no y h'
                      end)
                  | inleft (exist _ x (conj hi hp)) => inleft (exist _ x (conj (or_intror hi) hp)) 
                  end
               end
    end.

  Fixpoint last_dec `{T: EqDec} (p: T->Decidable) (s: set T): {x | In x s /\ p x} + {forall x, In x s -> not (p x)} :=
    match s with
      [] => inright (fun x h => match (h : In x []) with end)
    | x::s' => 
        match last_dec p s' with
        | inleft (exist _ x (conj hi hp)) => inleft (exist _ x (conj (or_intror hi) hp)) 
        | inright no =>
          match @dc_dec (p x) with
            left d => inleft (exist _ x (conj (or_introl eq_refl) d))
          | right n => inright (fun y h => 
                      match h with
                        | or_introl h' => match h' in (_ = y) return (~ p y) with
                                                | eq_refl => n
                                          end
                        | or_intror h' => no y h'
                      end)
          end
       end
    end.
  
  Fixpoint Isexist `(T : EqDec) (x : T) (s : set T) : bool :=
    match s with
    | [] => false
    | hd :: tl =>
      if eq_dec x hd then
        true
      else
        Isexist x tl
    end.

  Fixpoint inter `(T : EqDec) (s1 s2 : set T) : set T :=
    match s1 with
    | [] => []
    | hd :: tl =>
      if in_dec eq_dec hd s2 then
        hd :: inter tl s2
      else
        inter tl s2
    end.

  Fixpoint union `(T : EqDec) (s1 s2 : set T) : set T :=
    match s1 with
    | [] => s2
    | hd :: tl => add hd (union tl s2)
    end.

  Fixpoint diff `(T : EqDec) (s1 s2 : set T) : set T :=
    match s1 with
    | [] => []
    | hd :: tl =>
      if in_dec eq_dec hd s2 then
        diff tl s2
      else
        hd :: diff tl s2
    end.

  Definition set_In `(T : EqDec): T -> set T -> Prop := In (A := T).
  (*Definition set_In {U} (T : EqDec U) (x : T) (s : set T) : Prop := List.In x s. *)

  Definition is_empty  `(T: EqDec) (s: set T) : Prop := forall v, ~In v s.
  Definition subset  `(T: EqDec) (s1 s2: set T) : Prop := forall v, In v s1 -> In v s2.
  Definition set_eq  `(T: EqDec) (s1 s2: set T) : Prop := forall v, In v s1 <-> In v s2.
  Definition disjoint  `(T: EqDec) (s1 s2: set T) : Prop := forall v, not (In v s1 /\ In v s2).

  Program Instance emptyDec `(T:EqDec) (s: set T) : Decidable := {| 
     dcPred := is_empty s
  |}.
  Next Obligation.
    destruct s; [left | right]; repeat intro; auto.
    apply (H e); left; reflexivity.
  Defined.

  Lemma empty_is_empty: forall `(T:EqDec), is_empty (empty T).
  Proof.
    repeat intro.
    destruct H.
  Qed.

  Definition choose `{T: EqDec} (s: set T) : not (is_empty s) -> T :=
  match s return ~ (is_empty s) -> T with
    [] => fun h => match h (@empty_is_empty _ T) with end
  | x::_ => fun h => x
  end.
  
  Definition choose_In: forall `{T: EqDec} {s: set T} (h: not (is_empty s)),
    set_In (choose h) s.
  Proof.
    unfold choose; simpl; intros.
    destruct s; auto.
    destruct (h (empty_is_empty (T:=T))).
    left; auto.
  Qed.

  Lemma InSing: forall `{T: EqDec} (x y: T), set_In x (sing T y) <-> x=y.
  Proof.
    intros; split; intros.
    destruct H; auto; destruct H.
    subst x; left; auto.
  Qed.

  Lemma InPair: forall `{T: EqDec} (x y1 y2: T), set_In x (pair y1 y2) <-> x=y1 \/ x=y2.
  Proof.
    intros; split; intros.
    unfold pair in H.
    destruct (eq_dec y1 y2).
    left; destruct H; auto; destruct H.
    destruct H; [left; auto | right].
    destruct H; auto; destruct H.

    unfold pair.
    destruct (eq_dec y1 y2).
    subst y2.
    destruct H; subst x; left; auto.
    destruct H; [left|right]; auto.
    left; auto.
  Qed.

  Lemma InAdd_l : forall `(T : EqDec) (x : T) (s : set T), set_In x (add x s).
  Proof.
    unfold set_In; induction s; simpl; intros; auto.
    destruct (eq_dec x a); auto.
    subst a.
    left; auto.
    right; auto.
  Qed.

  Lemma InAdd_r : forall `(T : EqDec) (x y : T) (s : set T), set_In x s -> set_In x (add y s).
  Proof.
    unfold set_In; simple induction s; simpl.
    intro H; right; assumption.
    intros a l H [H0 | H1].
    elim (eq_dec y a); left; assumption.
    elim (eq_dec y a); right; [assumption | apply H; assumption].
  Qed.

  Lemma InAdd_ne : forall `(T : EqDec) (x y : T) (s : set T), set_In x (add y s) -> y <> x -> set_In x s.
  Proof.
    induction s; simpl; intros; auto.
    destruct H; tauto.

    destruct (eq_dec y a).
    subst y.
    right.
    destruct H; tauto.

    destruct H.
    left; tauto.
    right; tauto.
  Qed.
  
  Lemma InAdd : forall `(T : EqDec) (x y : T) (s : set T), set_In x (add y s) -> {x = y}+{set_In x s}.
  Proof.
    induction s; simpl; intros; auto.
    elim (eq_dec x y); intros.
    left; auto.
    right.
    apply b; clear b; destruct H; auto.
    destruct H.
    destruct (eq_dec y a).
    subst y.
    destruct (eq_dec x a).
    left; auto.
    right.
    right.
    destruct H; auto.
    subst a; tauto.
    
    destruct (eq_dec x y).
    left; auto.
    right.
    destruct H.
    left; auto.
    elim (IHs H); intros.
    tauto.
    right; auto.
  Defined.

  Lemma InL2S: forall `{T: EqDec} (l: list T) x,
    In x l <-> In x (SV.list2set T l).
  Proof.
    induction l; simpl; intros; try tauto.
    split; intro.
    destruct H.
    subst a.
    apply InAdd_l.
    apply InAdd_r.
    apply IHl; now auto.
    
    apply InAdd in H; destruct H.
    left; symmetry; now auto.
    right; apply IHl in s; auto.
  Qed.

  Lemma uniq_empty: forall `{T: EqDec}, uniq (empty T).
  Proof.
    repeat intro.
    destruct l1; simpl in *; try tauto.
    discriminate.
  Qed.

  Lemma uniq_sing: forall `{T: EqDec} (a:T), uniq (sing T a).
  Proof.
    repeat intro.
    destruct l1; simpl in *; try tauto.
    injection H; clear H; simpl; intros; auto.
    destruct l1; simpl in *; try tauto.
    subst l2; destruct H1.
    discriminate.
  Qed.

  Lemma uniq_add: forall `{T: EqDec} {a:T} {l: set T},
    uniq l -> uniq (add a l).
  Proof.
    induction l; simpl; intros; auto.
    apply uniq_sing.
    
    destruct (eq_dec a a0); auto.
    apply uniq_tl_intro; auto.
    intro.
    apply InAdd in H0; destruct H0; try tauto.
    subst a0; tauto.
    apply (H (cons a0 nil) l eq_refl a0); simpl; now auto.
    apply IHl.
    apply uniq_tl in H; auto.
  Qed.

  Lemma uniq_l2s: forall `{T:EqDec} (l: list T), uniq (list2set T l).
  Proof.
    induction l; simpl; intros; auto.
    apply uniq_empty.
    apply uniq_add.
    apply IHl.
  Qed.

  Lemma InUnion : forall `(T : EqDec) (x : T) (s1 s2 : set T), set_In x (union s1 s2) ->  {set_In x s1}+{set_In x s2}.
  Proof.
    induction s1; intros; auto.
    simpl in H.
    apply InAdd in H.
    destruct H.
    left.
    left.
    symmetry; apply e.
    
    elim (IHs1 _ s); intros.
    left; right; apply a0.
    right; apply b.
  Defined.

  Lemma InUnion_l : forall `(T : EqDec) (x : T) (s1 s2 : set T), set_In x s1 -> set_In x (union s1 s2).
  Proof.
    induction s1; intros; auto.
    destruct H.
    simpl.
    destruct H.
    subst.
    unfold set_In.
    induction (union s1 s2); simpl; intros; auto.
    destruct (eq_dec x a); simpl; auto.
    apply InAdd_r; auto.
  Qed.

  Lemma InUnion_r : forall `(T : EqDec) (x : T) (s1 s2 : set T), set_In x s2 -> set_In x (union s1 s2).
  Proof.
    induction s1; simpl; intros; auto.
    apply InAdd_r; auto.
  Qed.

  Fixpoint CUnion `(U: EqDec) `(T: EqDec) (P: U -> Decidable) (Q: set U) (f: forall v:U, P v -> set T) : set T :=
    match Q with
      [] => []
    | x::r => match @dc_dec (P x) with left h => f x h ++ CUnion P r f | _ => CUnion P r f end
    end.

  Lemma InCUnion_intro: forall `(U: EqDec) `(T: EqDec) (P: U->Decidable) (Q: set U) (f: forall v:U, P v -> set T) v (u:U),
    set_In u Q -> P u -> (forall h, set_In v (f u h)) -> set_In v (CUnion P Q f).
  Proof.
    intros.
    induction Q; intros; auto.
    simpl in *.
    destruct H; auto.
    subst u.
    destruct (@dc_dec (P a)); simpl.
    apply in_or_app.
    left; apply H1.
    elim (n H0).
    destruct (@dc_dec (P a)).
    apply in_or_app.
    right.
    apply (IHQ H).
    apply (IHQ H).
  Qed.
  
  Lemma InCUnion_elim: forall `(U: EqDec) `(T: EqDec) (P: U->Decidable) (Q: set U) (f: forall v:U, P v -> set T) v,
      set_In v (CUnion P Q f) -> exists u, List.In u Q  /\ P u /\ (forall h, set_In v (f u h)).
  Proof.
    intros.
    induction Q; intros; auto.
    simpl in *.
    destruct H.
    simpl in H.
    destruct (@dc_dec (P a)); simpl.
    apply in_app_or in H.
    destruct H.
    exists a; repeat split; auto.
    intro.
    rewrite (proof_irrelevance _ h d); now auto.
    
    destruct (IHQ H); intros.
    exists x; repeat split; auto; try tauto.
    
    destruct (IHQ H); intros.
    exists x; repeat split; auto; try tauto.
  Qed.

  Lemma CUnion_empty: forall `(U: EqDec) `(T: EqDec) (P: U->Decidable) (Q: set U) (f: forall v:U, P v -> set T),
    (forall v h, is_empty (f v h)) -> is_empty (CUnion P Q f).
  Proof.
    intros.
    induction Q; simpl; intros; auto.
    intros v h; destruct h.
    destruct dc_dec.
    intros v h.
    generalize (H a d); intro.
    destruct (f a d).
    simpl in h; apply IHQ in h; destruct h.
    apply (H0 e); simpl; now auto.
    apply IHQ.
  Qed.

  Definition GUnion `{T1: EqDec} `{T2: EqDec} (d s: set T1) (f: forall v, In v d -> set T2) : set T2 := CUnion (InPred _ d) s f.
  
  Definition uniq `{T: EqDec} (l: list T): Prop :=
    forall l1 l2, l=l1++l2 -> disjoint l1 l2.

  Lemma set_eq_refl: forall `{T:EqDec} (s: set T), set_eq s s.
  Proof.
    repeat intro; split; intro; auto.
  Qed.
  Global Notation "s1 == s2" := (set_eq s1 s2) (at level 70).

  Lemma set_eq_sym: forall `{T:EqDec} (s1 s2: set T), set_eq s1 s2 -> set_eq s2 s1.
  Proof.
    repeat intro; split; intro; apply H; auto.
  Qed.
  
  Lemma set_eq_trans: forall `{T:EqDec} (s1 s2 s3: set T), s1 == s2 -> s2 == s3 -> s1 == s3.
  Proof.
    repeat intro; split; intro; auto.
    apply H in H1.
    apply H0 in H1; auto.
    apply H.
    apply H0.
    auto.
  Qed.

Add Parametric Relation T U : (set U) (@set_eq T U)
  reflexivity proved by set_eq_refl
  symmetry proved by set_eq_sym
  transitivity proved by set_eq_trans as set_eq_rel.

  
  Lemma subset_dec `{T: EqDec} (s1 s2: set T): {subset s1 s2}+{~subset s1 s2}.
  Proof.
    induction s1; intros; simpl; auto.
    left; repeat intro; auto.
    destruct H.
    destruct (@In_dec _ eq_dec a s2); intros.
    destruct IHs1.
    left; simpl; repeat intro.
    destruct H.
    subst a; apply i.
    apply s.
    apply H.
    right; intro.
    apply n; clear n.
    repeat intro.
    apply H.
    right.
    apply H0.
    
    right; intro.
    apply n.
    apply H.
    left; auto.
  Defined.

  Lemma subset_trans: forall `{T:EqDec} {s1 s2 s3: set T}, subset s1 s2 -> subset s2 s3 -> subset s1 s3.
  Proof.
    repeat intro.
    apply H0.
    apply H.
    apply H1.
  Qed.

  Lemma is_empty_dec `{T: EqDec} (s: set T): {is_empty s}+{~is_empty s}.
  Proof.
    intros.
    destruct s.
    left.
    abstract (repeat intro; destruct H).
    right; intro.
    abstract (destruct (H e); left; apply eq_refl).
  Defined.

  Lemma disjoint_dec: forall `{T: EqDec} (s1 s2: set T), {disjoint s1 s2}+{~disjoint s1 s2}.
  Proof.
    induction s1; intros.
    left.
    repeat intro.
    abstract (destruct (proj1 H)).
    destruct (@In_dec _ eq_dec a s2); intros.
    right; intro.
    destruct (H a); split; auto.
    left; apply eq_refl.
    destruct (IHs1 s2); clear IHs1; intros.
    left.
    repeat intro.
    destruct H.
    destruct H.
    subst; tauto.
    destruct (d v); tauto.
    right; intro.
    apply n0; clear n0.
    repeat intro.
    elim (H v); intros.
    destruct H0.
    split; auto.
    right; auto.
  Defined.

  Lemma IsSubset `(T: EqDec) (s1 s2: set T) : {subset s1 s2}+{~subset s1 s2}.
  Proof.
    unfold subset; generalize dependent s2.
    induction s1.
    - 
      intro s2.
      left; intros.
      inversion H.
    -
      intro s2.
      destruct (in_dec eq_dec a s2).
      +
        destruct (IHs1 s2).
        *
          left; intros.
          inversion H.
          subst; assumption.
          apply i0; apply H0.
        *
          right; intros.
          intro H.
          apply n.
          intros.
          apply H.
          right; apply H0.
      +
        right; intro.
        apply n; apply H.
        left; reflexivity.
  Qed.

  Lemma subset_hd: forall `{T:EqDec} x l (s: set T), subset (x::l) s -> In x s.
  Proof.
    intros.
    apply H.
    left; auto.
  Qed.

  Lemma subset_tl: forall `{T:EqDec} x l (s: set T), subset (x::l) s -> subset l s.
  Proof.
    repeat intro.
    apply H.
    right; auto.
  Qed.
  
  Lemma empty_subset: forall `{T:EqDec} (s: set T), subset [] s.
  Proof.
    repeat intro.
    inversion H.
  Qed.

  Lemma subset_refl: forall `{T:EqDec} (s: set T), subset s s.
  Proof.
    repeat intro; auto.
  Qed.
  
  Lemma sing_subset: forall `{T: EqDec} x (s:set T), set_In x s -> subset (sing T x) s.
  Proof.
    intros.
    repeat intro.
    destruct H0.
    subst.
    apply H.
    inversion H0.
  Qed.

  Lemma subset_sing: forall `{T: EqDec} x (s:set T), subset (sing T x) s -> set_In x s.
  Proof.
    intros.
    repeat intro.
    apply H.
    left; auto.
  Qed.

  Lemma subset_union_l: forall `{U: EqDec} {s1 s2: set U}, subset s1 (union s1 s2).
  Proof.
    repeat intro.
    apply InUnion_l.
    apply H.
  Qed.

  Lemma subset_union_r: forall `{U: EqDec} {s1 s2: set U}, subset s2 (union s1 s2).
  Proof.
    repeat intro.
    apply InUnion_r.
    apply H.
  Qed.

  Lemma subset_union_mono: forall `{U: EqDec} {s1 s2 t1 t2: set U}, subset s1 t1 -> subset s2 t2 -> subset (union s1 s2) (union t1 t2).
  Proof.
    repeat intro.
    apply InUnion in H1; destruct H1.
    apply H in s.
    apply InUnion_l; auto.
    apply H0 in s.
    apply InUnion_r; auto.
  Qed.
  
  Lemma subset_CUnion_elim: forall `(U: EqDec) `(T: EqDec) (P: U->Decidable) (Q: set U) (f: forall v:U, P v -> set T) e,
    subset (CUnion P Q f) e -> forall u h, List.In u Q  -> subset (f u h) e.
  Proof.
    repeat intro.
    apply (H v); clear H.
    apply InCUnion_intro with (u0:=u); intros; auto.
    rewrite (proof_irrelevance _ h0 h); auto.
  Qed.

  Lemma subset_add_l: forall `{U: EqDec} {x:U} {s: set U}, subset s (add x s).
  Proof.
    repeat intro.
    apply InAdd_r.
    apply H.
  Qed.

  Lemma subset_add_mono: forall `{U: EqDec} (x:U) {s1 s2: set U},
    subset s1 s2 -> subset (add x s1) (add x s2).
  Proof.
    repeat intro.
    apply InAdd in H0; destruct H0.
    subst x; apply InAdd_l.
    apply InAdd_r.
    apply H; auto.
  Qed.

  Lemma subset_union_empty_r: forall `{U: EqDec} {s:set U},
    subset (union s (empty _)) s.
  Proof.
    repeat intro.
    apply InUnion in H; destruct H; auto.
    destruct s0.
  Qed.

  Lemma subset_union_sing_add_r: forall `{U: EqDec} {v:U} {s:set U},
    subset (union s (sing _ v)) (add v s).
  Proof.
    repeat intro.
    apply InUnion in H; destruct H; auto.
    apply InAdd_r; auto.
    destruct s0.
    subst v0.
    apply InAdd_l.
    destruct H.
  Qed.

  Lemma subset_union_rl: forall `{U:EqDec} (s1 s2 s3: set U),
    SV.subset s1 (SV.union s2 (SV.union s1 s3)).
  Proof.
    repeat intro.
    apply InUnion_r.
    apply InUnion_l.
    auto.
  Qed.

  Lemma subset_union_rr: forall `{U:EqDec} (s1 s2 s3: set U),
    SV.subset s1 (SV.union s2 (SV.union s3 s1)).
  Proof.
    repeat intro.
    apply InUnion_r.
    apply InUnion_r.
    auto.
  Qed.

  Lemma subset_union_r_intro: forall `{U:EqDec} (s1 s2 s: set U),
    subset s1 s -> subset s2 s -> subset (union s1 s2) s.
  Proof.
    repeat intro.
    apply SV.InUnion in H1; destruct H1.
    apply H; auto.
    apply H0; auto.
  Qed.
  
  Lemma subset_union_l_elim: forall `{U:EqDec} (s1 s2 s: set U),
    subset (union s1 s2) s -> subset s1 s.
  Proof.
    repeat intro.
    apply H.
    apply InUnion_l; auto.
  Qed.

  Lemma subset_union_r_elim: forall `{U:EqDec} (s1 s2 s: set U),
    subset (union s1 s2) s -> subset s2 s.
  Proof.
    repeat intro.
    apply H.
    apply InUnion_r; auto.
  Qed.
  
  Lemma subset_union_l_mono: forall `{U:EqDec} (s1 s2 s: set U),
    subset s1 s2 -> subset (union s s1) (union s s2).
  Proof.
    repeat intro.
    apply InUnion in H0; destruct H0.
    apply InUnion_l; apply s0.
    apply InUnion_r; apply H; apply s0.
  Qed.
  
  Definition bset_eq `(T: EqDec) (s1 s2: set T) :=
    if IsSubset s1 s2 then if IsSubset s2 s1 then true else false else false.

  Lemma NotInLRNotInUnion: forall `(T: EqDec) (v: T) s1 s2, ~set_In v s1 -> ~set_In v s2 -> ~In v (union s1 s2).
  Proof.
    simple induction s1; intros.
    -
      simpl.
      intro H1.
      apply H0; assumption.
    -
      simpl.
      intro H2.
      apply InAdd in H2.
      inversion H2.
      + 
        subst.
        apply H0; left; reflexivity.
      +
        revert H3.
        (*generalize dependent H3.*)
        apply H.
        intro H3; apply H0; right; assumption.
        apply H1.
  Qed.
 
 Lemma InInter_l: forall `{T:EqDec} (v:T) s1 s2, set_In v (inter s1 s2) -> set_In v s1.
  Proof.
    unfold set_In; simple induction s1; simpl.
    -
      intros H H0; apply H0.
    -
      do 3 intro.
      intro s2.
      elim (in_dec eq_dec a s2); intros; auto.
      destruct H0.
      left; now auto.
      right; auto.
      apply H with s2; now auto.
      
      right.
      apply H in H0; auto.
  Qed.

 Lemma InInter_r: forall `{T: EqDec} (v:T) s1 s2, set_In v (inter s1 s2) -> set_In v s2.
  Proof.
    unfold set_In; induction s1; simpl; intros; auto.
    destruct H.
    
    destruct (in_dec eq_dec a s2).
    destruct H.
    subst a; now auto.
    apply IHs1 in H; now auto.
    apply IHs1 in H; now auto.
  Qed.

  Lemma InInter : forall `{T: EqDec} (v:T) s1 s2,  set_In v s1 ->  set_In v s2 -> set_In v (inter s1 s2).
  Proof.
     induction s1; simpl; intros; auto.
     destruct (in_dec eq_dec a s2).
     simpl.
     destruct H.
     left; auto.
     right.
     apply IHs1; now auto.
     
     destruct H.
     subst a.
     destruct (n H0).
     apply IHs1; auto.
  Qed.

  Lemma InDiff_l: forall `(T: EqDec) (v:T) s1 s2, set_In v (diff s1 s2) -> set_In v s1.
  Proof.
    unfold set_In; induction s1; simpl; intros; auto.
    destruct (in_dec eq_dec a s2); auto.
    right.
    apply IHs1 in H; now auto.

    destruct H.
    left; now auto.
    apply IHs1 in H; right; auto.
  Qed.
  
  Lemma InDiff : forall `{T: EqDec} (v:T) s1 s2,  set_In v s1 ->  ~set_In v s2 -> set_In v (diff s1 s2).
  Proof.
     induction s1; simpl; intros; auto.
     destruct (in_dec eq_dec a s2).
     simpl.
     destruct H.
     subst.
     tauto.
     apply IHs1; now auto.
     
     destruct H.
     subst a.
     left; now auto.
     simpl; right.
     apply IHs1; auto.
  Qed.

  Lemma subset_diff_empty_r: forall `{T: EqDec} (s1 s2: set T),
    subset s1 s2 -> subset s1 (diff s2 (empty _)).
  Proof.
    repeat intro.
    apply SV.InDiff.
    apply H in H0; easy.
    intro e; destruct e.
  Qed.
  
  Lemma subset_diff_elim: forall `{T: EqDec} (s s1 s2: set T),
    subset (diff s1 s2) s -> subset s1 (union s s2).
  Proof.
    repeat intro.
    destruct (In_dec eq_dec v s2).
    apply InUnion_r; easy.
    apply InUnion_l.
    apply H.
    apply InDiff; auto.
  Qed.
  
  Lemma no_exist_no_In : forall `(T:EqDec) (v:T) s2,  Isexist v s2 = false <-> ~set_In v s2.
  Proof.
    unfold set_In; simple induction s2; simpl.
    -
      split; auto.
    -
      do 3 intro.
      destruct (eq_dec v a) eqn : H0.
      +
        split.
        *
          intro H1; inversion H1.
        *
          subst.
          intro H1.
          exfalso; apply H1; left; reflexivity.
      +
        split.
        intro H1; intros [H2 | H3].
        * 
          subst.
          apply n; reflexivity.
        *
          revert H3.
          rewrite <- H.
          assumption.
        *
          intro H1.
          rewrite -> H.
          intro H2; apply H1.
          right; assumption.
  Qed.
  
  Lemma InDiff_r: forall `(T: EqDec) (v:T) s1 s2, set_In v (diff s1 s2) -> ~set_In v s2.
  Proof.
    unfold set_In; simple induction s1; simpl.
    -
      intros s2 F; intro; assumption.
    -
      do 3 intro.
      intro s2.
      destruct (in_dec eq_dec a s2) eqn : H0.
      +
        intro;  apply H; assumption.
      +
        intros [H1 | H2].
        subst; auto.
        apply H; auto.
  Qed.

  Lemma In_dec: forall `(T: EqDec) (v:T) s, {set_In v s}+{~set_In  v s}.
  Proof.
   intros.
   apply (in_dec eq_dec).
  Defined.

  Lemma InUnionNotl: forall `(T: EqDec) (v:T) s1 s2, set_In v (union s1 s2) -> ~set_In v s1 -> set_In v s2.
  Proof.
    unfold set_In; simple induction s1; simpl.
    -
      intros; assumption.
    -
      do 3 intro; intros.
      apply InAdd in H0.
      destruct (eq_dec v a).
      +
        subst.
        exfalso; apply H1; left; reflexivity.
      +
        destruct H0.
        *
          tauto.
        *
          apply InUnion in s.
          destruct s.
          exfalso; apply H1; right; assumption.
          assumption.
  Qed.
  
  Lemma NotInLDiff: forall `(T: EqDec) (v:T) s1 s2, ~set_In v s1 -> ~set_In v (diff s1 s2).
  Proof.
    unfold set_In; simple induction s1; simpl.
    -
      intros; assumption.
    -
      do 3 intro; intros.
      destruct (in_dec eq_dec a s2).
      +
        apply H; intro; apply H0; right; assumption.
      +
        intros [H1 | H2].
        apply H0; left; assumption.
        revert H2; apply H; intro; apply H0; right; assumption.
  Qed.

  Fixpoint image `{T1: EqDec} `{T2: EqDec} (f: T1->T2) (s: set T1): set T2 :=
    match s with
      [] => []
    | x::s' => add (f x) (image f s')
    end.

  Lemma InImage_elim: forall `{T1: EqDec} `{T2: EqDec} (f: T1->T2) (s: set T1) (v:T2), set_In v (image f s) -> {w | v=f w /\ In w s}.
  Proof.
    induction s; intros.
    destruct H.
    simpl in H.
    apply SV.InAdd in H; destruct H.
    exists a.
    split; auto.
    left; apply eq_refl.
    destruct (IHs _ s0); intros.
    exists x.
    destruct a0.
    split; auto.
    right; auto.
  Defined.

  Lemma InImage_intro: forall `{T1: EqDec} `{T2: EqDec} (f: T1->T2) (s: set T1) (v:T2) w, v=f w -> set_In w s -> set_In v (image f s).
  Proof.
    induction s; intros.
    destruct H0.
    subst v.
    simpl in *.
    destruct H0.
    subst a.
    apply InAdd_l.
    apply InAdd_r.
    apply IHs with (w:=w); auto.
  Qed.

  Lemma subset_image_mono: forall `{T1: EqDec} `{T2: EqDec} (f: T1->T2) (s1 s2: set T1), 
    subset s1 s2 -> subset (image f s1) (image f s2).
  Proof.
    repeat intro.
    apply InImage_elim in H0.
    destruct H0 as [w [h1 h2]]; subst.
    apply InImage_intro with (w0:=w); auto.
    apply H; auto.
  Qed.

  Definition sProduct `{T1: EqDec} `{T2: EqDec} (s1: set T1) (s2: set T2): set (eProduct T1 T2) :=
    List.flat_map (fun x1 => List.map (fun x2 => (x1,x2)) s2) s1.

  Lemma InsProduct: forall `{T1: EqDec} `{T2: EqDec} (s1: set T1) (s2: set T2) v1 v2,
    set_In v1 s1 -> set_In v2 s2 -> @set_In _ (eProduct T1 T2) (v1,v2) (sProduct s1 s2).
  Proof.
    intros.
    unfold sProduct.
    apply in_flat_map.
    exists v1.
    split; auto.
    apply in_map_iff.
    exists v2.
    split; auto.
  Qed.

  Lemma sProduct_l: forall `{T1: EqDec} `{T2: EqDec} (s1: set T1) (s2: set T2) v1 v2,
    @set_In _ (eProduct T1 T2) (v1,v2) (sProduct s1 s2) -> set_In v1 s1.
  Proof.
    intros.
    unfold sProduct, set_In in H.
    apply in_flat_map in H.
    destruct H as [x [h1 h2]].
    apply in_map_iff in h2.
    destruct h2 as [y [h3 h4]].
    injection  h3; clear h3; intros; subst.
    auto.
  Qed.

  Lemma sProduct_r: forall `{T1: EqDec} `{T2: EqDec} (s1: set T1) (s2: set T2) v1 v2,
    @set_In _ (eProduct T1 T2) (v1,v2) (sProduct s1 s2) -> set_In v2 s2.
  Proof.
    intros.
    unfold sProduct, set_In in H.
    apply in_flat_map in H.
    destruct H as [x [h1 h2]].
    apply in_map_iff in h2.
    destruct h2 as [y [h3 h4]].
    injection  h3; clear h3; intros; subst.
    auto.
  Qed.

  Definition filter `{T: EqDec} (P: T -> bool) (s: set T): set T := List.filter P s.
  
  Lemma Infilter: forall  `{T: EqDec} (P: T -> bool) (s: set T) x, set_In x s -> P x = true -> set_In x (filter P s).
  Proof.
    induction s; intros; auto.
    destruct H.
    subst.
    simpl.
    rewrite H0.
    left; reflexivity.
    generalize (IHs _ H H0); intro.
    simpl.
    destruct (P a); auto.
    right; auto.
  Qed.

  Lemma filter_l: forall  `{T: EqDec} (P: T -> bool) (s: set T) x, set_In x (filter P s) -> P x = true.
  Proof.
    induction s; intros; auto.
    simpl in H.
    destruct (P a) eqn:e; auto.
    destruct H; auto.
    subst a; auto.
  Qed.

  Lemma filter_r: forall  `{T: EqDec} (P: T -> bool) (s: set T) x, set_In x (filter P s) -> set_In x s.
  Proof.
    induction s; intros; auto.
    simpl in H.
    destruct (P a) eqn:e; auto.
    destruct H; auto.
    subst a; auto.
    left; auto.
    right; auto.
    right; auto.
  Qed.

  Fixpoint Filter `{T: EqDec} (P: T->Decidable) (s: set T): set T :=
  match s with
    [] => []
  | x::s' => if (@dc_dec (P x)) then (x::Filter P s') else Filter P s'
  end.
  
  Lemma InFilter_P: forall `{T: EqDec} (P: T->Decidable) (s: set T),
    forall x, set_In x (Filter P s) -> P x.
  Proof.
    induction s; simpl; intros; auto; try tauto.
    destruct dc_dec.
    destruct H.
    subst; tauto.
    apply IHs; auto.
    apply IHs; auto.
  Qed.

  Lemma FilterSubset: forall `{T: EqDec} (P: T->Decidable) (s: set T),
    subset (Filter P s) s.
  Proof.
    induction s; simpl; intros; auto; try tauto.
    repeat intro; auto.
    
    destruct dc_dec.
    repeat intro.
    destruct H.
    subst v; left; auto.
    apply IHs in H.
    right; auto.
    repeat intro.
    apply IHs in H.
    right; auto.
  Qed.

  Lemma InFilter_P_intro: forall `{T: EqDec} (P: T->Decidable) (s: set T),
    forall x, set_In x s -> P x -> set_In x (Filter P s).
  Proof.
    induction s; simpl; intros; auto; try tauto.
    destruct H.
    subst a.
    destruct dc_dec; auto.
    left; auto.
    destruct (n H0).
    destruct (eq_dec x a).
    subst a.
    destruct dc_dec; auto.
    left; auto.
    destruct dc_dec; auto.
    right; auto.
  Qed.
  
Add Parametric Morphism T U: (@union T U) with signature (@set_eq T U) ==> (@set_eq T U) ==> (@set_eq T U) as union_m.
Proof.
  intros.
  split; intro.
  apply InUnion in H1.
  destruct H1.
  apply InUnion_l.
  apply H; auto.
  apply InUnion_r.
  apply H0; auto.
  
  apply InUnion in H1.
  destruct H1.
  apply InUnion_l.
  apply H; auto.
  apply InUnion_r.
  apply H0; auto.  
Qed.

Add Parametric Morphism T U: (@inter T U) with signature (@set_eq T U) ==> (@set_eq T U) ==> (@set_eq T U) as inter_m.
Proof.
  intros.
  split; intro.
  apply InInter; intros.
  apply H.
  apply InInter_l in H1; auto.
  apply H0.
  apply InInter_r in H1; auto.

  apply InInter; intros.
  apply H.
  apply InInter_l in H1; auto.
  apply H0.
  apply InInter_r in H1; auto.
Qed.

Add Parametric Morphism {T} (U: @EqDec T): (@add T U) with signature (@eq U) ==> (@set_eq T U) ==> (@set_eq T U) as add_m.
Proof.
  intros.
  split; intro.
  apply InAdd in H0.
  destruct H0.
  subst y.
  apply InAdd_l.
  apply InAdd_r.
  apply H; auto.
  
  apply InAdd in H0.
  destruct H0.
  subst y.
  apply InAdd_l.
  apply InAdd_r.
  apply H; auto.
Qed.

  Lemma Add_Cons_eq: forall `{T:EqDec} a (s: set T), add a s == a::s.
  Proof.
    induction s; simpl; intros; auto.
    split; intro; auto.
    destruct (eq_dec a a0).
    subst a0.
    split; intro; auto.
    destruct H.
    subst.
    left; auto.
    right; right; auto.
    destruct H; auto.
    subst v.
    left; auto.
    
    split; intro.
    destruct H.
    subst a0.
    right; left; auto.
    apply IHs in H.
    destruct H.
    subst v.
    left; auto.
    right; right; auto.
    
    destruct H.
    subst a.
    right.
    apply IHs.
    left; auto.
    destruct H.
    subst a0.
    left; auto.
    right.
    apply IHs.
    right; auto.
  Qed.

  Lemma add_comm: forall `{T:EqDec} a1 a2 (s: set T), add a1 (add a2 s) == add a2 (add a1 s).
  Proof.
    intros; split; intro.
    apply InAdd in H.
    destruct H.
    apply InAdd_r.
    subst v.
    apply InAdd_l.
    apply InAdd in s0.
    destruct s0.
    subst v.
    apply InAdd_l.
    apply InAdd_r.
    apply InAdd_r; auto.
    
    apply InAdd in H.
    destruct H.
    apply InAdd_r.
    subst v.
    apply InAdd_l.
    apply InAdd in s0.
    destruct s0.
    subst v.
    apply InAdd_l.
    apply InAdd_r.
    apply InAdd_r; auto.    
  Qed.

  Lemma Union_add_r: forall `{T:EqDec} a s1 s2,
    (union s1 (a :: s2)) == (add a (union s1 s2)).
  Proof.
    induction s1; simpl; intros; auto.
    symmetry.
    apply Add_Cons_eq.
    rewrite IHs1.
    apply add_comm.
  Qed.

  Lemma Union_empty_r: forall `{T:EqDec} (s: set T), union s (empty _) == s.
  Proof.
    repeat intro; split; intro.
    apply InUnion in H.
    destruct H; auto.
    destruct s0.
    apply InUnion_l; auto.
  Qed.
  
  Lemma Union_Diff: forall `{T:EqDec} (s1 s2: set T), union (diff s1 s2) s2 == union s1 s2.
  Proof.
    repeat intro; split; intro.
    apply InUnion in H.
    destruct H.
    apply InDiff_l in s.
    apply InUnion_l; auto.
    apply InUnion_r; auto.
    
    apply InUnion in H.
    destruct (in_dec eq_dec v s2).
    apply InUnion_r; auto.
    destruct H; try tauto.
    apply InUnion_l.
    apply InDiff; auto.
  Qed.
  
  Lemma remove_union: forall `{V: EqDec} v (s1 s2: set V), remove v (union s1 s2) == union (remove v s1) (remove v s2).
  Proof.
    repeat (split || intro).
    generalize (InRemove_l _ H); intro.
    generalize (InRemove_r _ _ _ H); intro.
    apply InUnion in H1; destruct H1.
    apply InUnion_l.
    apply InRemove; auto.

    apply InUnion_r.
    apply InRemove; auto.
    
    apply InUnion in H; destruct H.
    apply InRemove.
    apply InRemove_l in s; auto.
    apply InUnion_l.
    apply InRemove_r in s; auto.

    apply InRemove.
    apply InRemove_l in s; auto.
    apply InUnion_r.
    apply InRemove_r in s; auto.
  Qed. 
  
  Lemma subset_remove_mono: forall `{U: EqDec} {x: U} {s1 s2: set U}, subset s1 s2 -> subset (remove x s1) (remove x s2).
  Proof.
    repeat intro.
    generalize H0; intro H1.
    apply InRemove_l in H0.
    apply InRemove_r in H1.
    apply InRemove; auto.
  Qed.

  
  Lemma Exists_union: forall `{V: EqDec} (s1 s2: set V) P, Exists P (union s1 s2) <-> Exists P s1 \/ Exists P s2.
  Proof.
    intros.
    repeat rewrite Exists_exists.
    split; intro.
    destruct H as [x [h1 h2]].
    apply InUnion in h1.
    destruct h1; [left|right]; exists x; auto.
    destruct H; destruct H as [x [h1 h2]]; exists x; split; auto.
    apply InUnion_l; auto.
    apply InUnion_r; auto.
  Qed.

  Fixpoint pow `{T: EqDec} (s: set T): set (setDec T) :=
    match s with
      [] => [[]]
    | x::s' => union (pow s') (image (fun (u: setDec T) => (add x u: setDec T)) (pow s')) 
    end.
 
 Lemma InPow_elim: forall `{T: EqDec} (s: set T) x, set_In x (pow s) -> subset x s.
 Proof.
  induction s; simpl; intros; auto.
  destruct H; try tauto; subst x.
  repeat intro; tauto.

  apply InUnion in H; destruct H.
  apply IHs in s0.
  repeat intro.
  right; apply s0; apply H.
  apply InImage_elim in s0.
  destruct s0 as [w [h1 h2]].
  apply IHs in h2; clear IHs.
  subst x.
  repeat intro.
  apply InAdd in H; destruct H.
  subst v; left; now auto.
  right; apply h2; apply s0.
 Qed.

 Lemma InEmptyPow_intro: forall `{T: EqDec} (s: set T), set_In (T:= setDec T) [] (pow s).
 Proof.
  induction s; simpl; intros; auto.
  apply InUnion_l; auto.
 Qed.
 
 Lemma InSingPow_intro: forall `{T: EqDec} (s: set T) x, set_In x s -> set_In (T:= setDec T) (sing T x) (pow s).
 Proof.
  intros.
  induction s; simpl; intros.
  destruct H.
  destruct H.
  subst x.
  apply InUnion_r.
  apply InImage_intro with (w:=[]).
  reflexivity.
  apply InEmptyPow_intro.
  apply InUnion_l; auto.
 Qed.
 
 Lemma pow_union: forall `{T: EqDec} (s1 s2 s: set T),
  set_In (T:=setDec T) s1 (pow s) -> set_In (T:=setDec T) s2 (pow s) -> set_In (T:=setDec T) (union s1 s2) (pow s).
 Proof.
 Admitted.
 
 Lemma InPow_intro: forall `{T: EqDec} (s: set T) x, subset x s -> exists (y: setDec T), set_eq x y /\ set_In y (pow s).
 Admitted. 
End SV.
