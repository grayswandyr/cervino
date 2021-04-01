
Require Import Classical.
Require Import Eqdep_dec.
Require Import Fin.
Require Import List.

Require Import dec.
Require Import set.

Inductive isFinite `(T: EqDec): Prop :=
  isFinite_intro: forall s: SV.set T, (forall x, SV.set_In x s) -> isFinite T.

Class Finite {T} := {
  fin_dec : @EqDec T;
  fin_set: SV.set fin_dec;
  fin_all: forall x, SV.set_In x fin_set;
}.
Coercion fin_dec: Finite >-> EqDec.
Arguments fin_set _ _ : assert.

Fixpoint fin2list n : list (Fin.t n) :=
  match n with
    0 => nil
  | S m => cons F1 (List.map FS (fin2list m))
  end.

Lemma fin2list_all: forall n, forall x, SV.set_In x (fin2list n).
Proof.
  intros.
  destruct n.
  inversion x.
  revert n x.
  apply rectS; intros; try (simpl; now auto).
  right.
  induction (fin2list (S n)); simpl; auto.
  destruct H.
  subst p; left; now auto.
  right; apply IHl; auto.
Qed.

Instance uptoFinite n: @Finite (Fin.t n) := {|
  fin_dec := uptoDec n;
  fin_set := fin2list n;
  fin_all := fin2list_all n
|}.

Lemma FiniteIsFinite: forall `(F: Finite), isFinite F.
Proof.
  intros.
  apply isFinite_intro with (s:= fin_set).
  apply fin_all.
Qed.

Program Definition subDec `{T:EqDec} (P:T->Prop): @EqDec {x:T | P x} := {|
  eq_dec := _
|}.
Next Obligation.
  repeat intro.
  destruct x as [x hx].
  destruct y as [y hy].
  destruct (eq_dec x y).
  subst y.
  left.
  f_equal.
  apply proof_irrelevance.
  right; intro.
  apply n; clear n.
  injection H; clear H; intros; auto.
Qed.

Definition asDec `{T:EqDec} (s: SV.set T): @EqDec {x : T | SV.set_In x s} := subDec (fun x => SV.set_In x s).

Program Definition subFinite `(T:Finite) (P: T->Decidable): @Finite {x : T | P x} := {|
  fin_dec := subDec P;
  fin_set := SV.GUnion (T1 := T) (T2 := subDec P)
      fin_set  fin_set
      (fun x _ => match @dc_dec (P x) with
        left h => SV.sing (subDec P) (exist _ x h)
      | right _ => SV.empty (subDec P)
      end)
|}.
Next Obligation.
  destruct x.
  eapply SV.InCUnion_intro with (u:= x); intros; auto.
  apply fin_all.
  apply fin_all.
  destruct dc_dec; try tauto.
  apply SV.InSing.
  f_equal; apply proof_irrelevance.
Qed.

Program Definition asFinite `{T:EqDec} (s: SV.set T): @Finite {x : T | SV.set_In x s} := {|
  fin_dec := asDec s;
  fin_set := SV.GUnion (T1 := T) (T2 := asDec s)
      s s
      (fun x h => SV.sing (asDec s) (exist _ x h))
|}.
Next Obligation.
  destruct x.
  eapply SV.InCUnion_intro with (u:= x); intros; auto.
  left.
  f_equal; apply proof_irrelevance.
Qed.

Definition DepPairSet `{T1: EqDec} {U: T1 -> Type} {T2: forall t, @EqDec (U t)}  {e1: SV.set T1} (e2: forall x, SV.set (T2 x)): SV.set (DepPairDec T1 T2) :=
    SV.GUnion (T1 := T1) (T2 := DepPairDec T1 T2)
      e1 e1
      (fun s h => 
          SV.image (T1 := T2 s) (T2 := DepPairDec T1 T2)
            (fun d => (existT _ s d))
            (e2 s)).

Program Definition DepPairFin `(F1: Finite) {U2:F1->Type} (F2: forall t, @Finite (U2 t)): Finite := {|
  fin_dec := DepPairDec F1 F2;
  fin_set := DepPairSet (T1:=F1) (T2:=F2) (e1:=@fin_set _ F1) (fun x => @fin_set _ (F2 x))
|}.
Next Obligation.
  intros.
  destruct x.
  apply SV.InCUnion_intro with (u:= x); simpl; intros.
  apply fin_all.
  apply fin_all.
  apply (SV.InImage_intro (T1:=F2 x) (T2 := DepPairDec F1 F2)) with (w:=e); auto.
  apply fin_all.
Qed.

Definition PairSet `{T1: EqDec} `{T2: EqDec}  {e1: SV.set T1} (e2: SV.set T2): SV.set (PairDec T1 T2) :=
    SV.GUnion (T1 := T1) (T2 := PairDec T1 T2)
      e1 e1
      (fun s h => 
          SV.image (T1 := T2) (T2 := PairDec T1 T2)
            (fun d => (s, d))
            e2).

Program Definition PairFin `(F1: Finite) `(F2: Finite): Finite := {|
  fin_dec := PairDec F1 F2;
  fin_set := @PairSet _ _ _ _ (@fin_set _ F1) (@fin_set _ F2)
|}.
Next Obligation.
  intros.
  destruct x.
  apply SV.InCUnion_intro with (u:= e); simpl; intros.
  apply fin_all.
  apply fin_all.
  apply (SV.InImage_intro (T1:=F2) (T2 := PairDec F1 F2)) with (w:=e0); auto.
  apply fin_all.
Qed.

Definition SumSet `{T1: EqDec} `{T2: EqDec} (e1: SV.set T1) (e2: SV.set T2): SV.set (SumDec T1 T2) :=
  SV.union 
    (SV.image (T1:=T1) (T2:=SumDec T1 T2) inl e1)
    (SV.image (T1:=T2) (T2:=SumDec T1 T2) inr e2).

Program Definition SumFin `(F1: Finite) `(F2: Finite): Finite := {|
  fin_dec := SumDec F1 F2;
  fin_set := SumSet (T1:=F1) (T2:=F2) (@fin_set _ F1) (@fin_set _ F2)
|}.
Next Obligation.
  intros; simpl in *.
  destruct x.
  apply SV.InUnion_l.
  apply SV.InImage_intro with (w:=e); auto.
  apply fin_all.
  apply SV.InUnion_r.
  apply SV.InImage_intro with (w:=e); auto.
  apply fin_all.
Qed.

Require Import FunctionalExtensionality.

Lemma len_CUnion_all: forall `(T: EqDec) (P: T->Decidable) (s: SV.set T),
  (forall x, In x s -> P x) ->
  length
    (SV.CUnion P s (fun (x:T) (h: P x) => SV.sing (subDec P) (exist P x h))) = length s.
Proof.
  intros until P.
  induction s; simpl; intros; auto.
  destruct dc_dec.
  simpl.
  f_equal.
  rewrite IHs; auto.
  
  exfalso; apply n; apply H; auto.
Qed.

Lemma asFinite_len: forall `(T: EqDec) (s: list T), length s = length (fin_set (Finite:=asFinite s)).
Proof.
  induction s; intros; auto.
  simpl.
  unfold SV.GUnion; simpl.
  destruct (eq_dec a a); try tauto.
  simpl.
  f_equal.
  rewrite IHs; clear IHs.
  unfold fin_set, asFinite, SV.GUnion; simpl.
  generalize (len_CUnion_all T (SV.InPred T s)); intros; auto.
  rewrite H; clear H.
  generalize (len_CUnion_all T (SV.InPred T (a::s))); intros; auto.
  rewrite H; clear H; auto.
  intros; right; now auto.
  intros; now auto.
  exfalso; tauto.
Qed.


Lemma CUnion_imp: forall `(T: Finite) (P Q1 Q2: T -> Decidable) s e
  (imp1: forall x, Q2 x -> Q1 x)
  (imp2: forall x, In x s -> Q1 x -> Q2 x),
  (@SV.CUnion T0 T {x : T | P x} (@subDec T0 T (fun x : T => P x))
     Q1 s e) =
  (@SV.CUnion T0 T {x : T | P x} (@subDec T0 T (fun x : T => P x))
     Q2 s (fun x h => e x (imp1 _ h))).
Proof.
  induction s; simpl; intros; auto.
  destruct (@dc_dec (Q2 a)).
  destruct (@dc_dec (Q1 a)).
  rewrite (proof_irrelevance _ (imp1 a d) d0).
  rewrite <-IHs.
  reflexivity.
  
  intros.
  apply imp2; now auto.

  exfalso; apply imp1 in d; tauto.
  
  rewrite <-IHs; clear IHs; auto.
  destruct (@dc_dec (Q1 a)); auto.
  exfalso; apply imp2 in d; tauto.
Qed.

Lemma CUnion_cons: forall `(T: Finite) (P: T -> Decidable) a s e,
  (@SV.CUnion T0 T {x : T | P x} (@subDec T0 T (fun x : T => P x))
     (@SV.InPred T0 T (a :: s)) s e) =
  (@SV.CUnion T0 T {x : T | P x} (@subDec T0 T (fun x : T => P x))
     (@SV.InPred T0 T s) s (fun v h => e v (or_intror h))).
Proof.
  intros.
  generalize (CUnion_imp _ P (@SV.InPred T0 T (a :: s)) (@SV.InPred T0 T s)); intro.
  rewrite <-H; clear H; auto.
Qed.

Lemma subFinite_len: forall `(T:Finite) (P: T->Decidable), length (fin_set (Finite:= subFinite T P)) = length (filter (fun x => if (@dc_dec (P x)) then true else false) (fin_set (Finite:=T))).
Proof.
  intros.
  unfold subFinite; simpl.
  induction (@fin_set T0 T); simpl; intros; auto.
  destruct (@dc_dec (P a)); simpl; auto.
  rewrite <-IHs; clear IHs.
  unfold SV.GUnion; simpl.
  destruct (@dc_dec (P a)); try tauto.
  destruct (@eq_dec T0 T a a); try (exfalso; tauto).
  rewrite app_length; simpl.
  f_equal.
  rewrite CUnion_cons; simpl.
  reflexivity.

  unfold SV.GUnion; simpl.
  destruct (@eq_dec T0 T a a); try (exfalso; tauto).
  destruct (@dc_dec (P a)); try tauto.
  unfold SV.empty; simpl.
  rewrite CUnion_cons; apply IHs.
Qed.

Lemma len_filter: forall T (l: list T) (P: T->bool), length (filter P l) <= length l.
Proof.
  induction l; simpl; intros; auto.
  destruct (P a); simpl; auto with arith.
Qed.

Program Instance FunDec `(T1: Finite) `(T2: EqDec) : @EqDec (T1->T2) := {| eq_dec := _ |}.
Next Obligation.
  repeat intro.
  set (n := List.length fin_set).
  assert (length fin_set <= n) by apply le_n; clearbody n.
  revert T T1 x y H.
  induction n; simpl; intros; auto.
  left.
  apply functional_extensionality; intro.
  generalize (fin_all x0); intro.
  destruct fin_set.
  inversion H0.
  inversion H.

  destruct fin_set eqn:fs.
  left.
  apply functional_extensionality; intro.
  generalize (fin_all x0); intro.
  rewrite fs in H0; destruct H0.
  
  destruct (eq_dec (x e) (y e)).
  set (T1s := (subFinite T1 (fun x => isNEq x e))).
  set (x1 := fun (i:T1s) => x (proj1_sig i)).
  set (y1 := fun (i:T1s) => y (proj1_sig i)).

  generalize (IHn _ (subFinite T1 (fun x => isNEq x e)) x1 y1); intro.
  destruct H0.

  clear x1 y1 IHn T1s.
  rewrite subFinite_len.
  rewrite fs; clear fs.
  simpl.
  destruct (@eq_dec T T1 e e); try (exfalso; tauto).
  simpl in H.
  assert (@length T1 s <= n) by auto with arith.
  apply Le.le_trans with (m := length s); auto.
  apply len_filter.
  
  left.
  apply functional_extensionality; intro.
  destruct (@dc_dec (isNEq x0 e)).
  assert (x1 (exist _ x0 d) = y1 (exist _ x0 d)).
  rewrite e1; reflexivity.
  apply H0.
  
  assert (x0=e).
  destruct (eq_dec x0 e); auto.
  exfalso; apply n0; simpl; apply n1.
  subst x0; now auto.
  
  right; intro; apply n0; clear n0.
  unfold x1,y1; subst; now auto.
  
  right; intro.
  apply n0; subst y; now auto.
Qed.

Lemma in_tl: forall `(T: EqDec) {x i} {e: SV.set T},
  In i (x::e) -> i <> x -> In i e.
Proof.
  intros.
  destruct H; auto.
  subst x; tauto.
Qed.

Fixpoint FunSet `{T1: Finite} `{T2: Finite} (e1: SV.set T1) (e2: SV.set T2): SV.set (FunDec (asFinite e1) T2) :=
  match e1 return SV.set (FunDec (asFinite e1) T2) with
    nil => SV.sing (FunDec (asFinite nil) T2) (fun v => let '(exist _ i h) := v in match h with end)
  | x::e => 
    SV.CUnion
      (U := FunDec (asFinite e) T2)
      (T0 := FunDec (asFinite (x::e)) T2)
      (fun _ => TrueDec)
      (FunSet e e2)
      (fun f h =>
        SV.CUnion 
          (U := T2)
          (T0 := FunDec (asFinite (x::e)) T2)
          (fun _ => TrueDec)
          e2
          (fun y _ => SV.sing (FunDec (asFinite (x::e)) T2) (fun v => let '(exist _ i hi) := v in
            match eq_dec i x with
              left e => y
            | right n => f (exist _ i (in_tl T1 hi n))
            end)))
  end.

Program Definition FunFin `(F1: Finite) `(F2: Finite): Finite := {|
  fin_dec := FunDec F1 F2;
  fin_set := 
    List.map (fun f i => f (exist _ i (fin_all i)))
      (FunSet (T1:=F1) (T2:=F2) (@fin_set _ F1) (@fin_set _ F2))
|}.
Next Obligation.
  change (fix In (a : F1) (l : list F1) {struct l} : Prop :=
                  match l with
                  | nil => False
                  | b :: m => b = a \/ In a m
                  end) with (@In F1).
  apply in_map_iff; intros.
  exists (fun v => let '(exist _ i h) := v in x i).
  split; auto.
  match goal with |- @In _ ?v _ => generalize v; clear x end.
  induction (@fin_set T F1); intros; auto.

  simpl; left.
  apply functional_extensionality; intro i.
  destruct i; tauto.
  
  unfold FunSet.
  set (e0 := fun v => let ' (exist _ i h) := v in e (exist _ i (or_intror h))).
  apply SV.InCUnion_intro with (u:=e0); simpl; auto.
  apply IHs.
  
  intro.
  eapply SV.InCUnion_intro with (u:= e (exist _ a (or_introl eq_refl))); simpl; auto.
  apply fin_all.
  intro.
  left.
  apply functional_extensionality; intro v.
  destruct v; simpl; auto.
  destruct (eq_dec a x).
  subst x.
  destruct (@eq_dec T F1 a a); try (exfalso; tauto).
  rewrite (proof_irrelevance _ _ o).
  reflexivity.
  destruct (@eq_dec T F1 x a); simpl; auto.
  exfalso; subst x; tauto.
  rewrite (proof_irrelevance _ _ o).
  reflexivity.
Qed.

Program Instance DepFunDec {T1: Type} (F1: @Finite T1) {T2: T1 -> Type} (F2: forall x, @Finite (T2 x)) : @EqDec (forall x, F2 x) := {| eq_dec := _ |}.
Next Obligation.
  repeat intro.
  set (n := List.length (fin_set (Finite:=F1))).
  assert (length (fin_set (Finite:=F1)) <= n) by apply le_n; clearbody n.
  revert T1 F1 T2 F2 x y H.
  induction n; simpl; intros; auto.
  left.
  apply functional_extensionality_dep; intro.
  generalize (fin_all (Finite:=F1) x0); intro.
  destruct (fin_set (Finite:=F1)).
  inversion H0.
  inversion H.

  destruct (fin_set (Finite:=F1)) eqn:fs.
  left.
  apply functional_extensionality_dep; intro.
  generalize (fin_all (Finite:=F1) x0); intro.
  rewrite fs in H0; destruct H0.
  
  destruct (eq_dec (x e) (y e)).
  set (T1s := (subFinite F1 (fun x => isNEq x e))).
  set (x1 := fun (i:T1s) => x (proj1_sig i)).
  set (y1 := fun (i:T1s) => y (proj1_sig i)).

  generalize (IHn _ (subFinite F1 (fun x => isNEq x e)) _ _ x1 y1); intro.
  destruct H0.

  clear x1 y1 IHn T1s.
  rewrite subFinite_len.
  rewrite fs; clear fs.
  simpl.
  destruct (@eq_dec T1 F1 e e); try (exfalso; tauto).
  simpl in H.
  assert (@length T1 s <= n) by auto with arith.
  apply Le.le_trans with (m := length s); auto.
  apply len_filter.
  
  left.
  apply functional_extensionality_dep; intro.
  destruct (@dc_dec (isNEq x0 e)).
  assert (x1 (exist _ x0 d) = y1 (exist _ x0 d)).
  rewrite e1; reflexivity.
  apply H0.
  
  assert (x0=e).
  destruct (eq_dec x0 e); auto.
  exfalso; apply n0; simpl; apply n1.
  subst x0; now auto.
  
  right; intro; apply n0; clear n0.
  unfold x1,y1; subst; now auto.
  
  right; intro.
  apply n0; subst y; now auto.
Qed.

Fixpoint DepFunSet {T1:Type} `{F1: @Finite T1} {T2: T1->Type} {F2: forall x, @Finite (T2 x)} (e1: SV.set F1) (e2: forall x, SV.set (F2 x)): SV.set (DepFunDec (asFinite e1) (fun i => F2 (proj1_sig i))) :=
  match e1 return SV.set (DepFunDec (asFinite e1) (fun i => F2 (proj1_sig i))) with
    nil => SV.sing (DepFunDec (asFinite nil) (fun i => F2 (proj1_sig i))) (fun '(exist _ i h) => match h with end)
  | x::e => 
    SV.CUnion
      (U := DepFunDec (asFinite e) (fun i => F2 (proj1_sig i)))
      (T0 := DepFunDec (asFinite (x::e)) (fun  i => F2 (proj1_sig i)))
      (fun _ => TrueDec)
      (DepFunSet e e2)
      (fun f h =>
        SV.CUnion 
          (U := F2 x)
          (T0 := DepFunDec (asFinite (x::e)) (fun i => F2 (proj1_sig i)))
          (fun _ => TrueDec)
          (e2 x)
          (fun y _ => SV.sing (DepFunDec (asFinite (x::e)) (fun i => F2 (proj1_sig i))) 
            (fun '(exist _ i hi) =>
              match eq_dec i x return F2 i with
                left e => match eq_sym e in _=a return F2 a with eq_refl => y end
              | right n => f (exist (fun i => In i e) i (in_tl F1 hi n))
              end)))
  end.

Program Definition DepFunFin  {T1} (F1: @Finite T1) {T2:T1->Type} (F2: forall x:T1, @Finite (T2 x)): Finite := {|
  fin_dec := DepFunDec F1 F2;
  fin_set := 
    List.map (fun f i => f (exist _ i (fin_all i)))
      (DepFunSet (T1:=F1) (T2:=F2) (@fin_set F1 F1) (fun i => @fin_set _ (F2 i)))
|}.
Next Obligation.
  apply in_map_iff; intros.
  exists (fun v => x (proj1_sig v)).
  split; auto.
  match goal with |- @In _ ?v _ => generalize v; clear x end.
  induction (@fin_set F1 F1); intros; auto.

  simpl; left.
  apply functional_extensionality_dep; intro i.
  destruct i; tauto.
  
  set (e0 := fun (v: {i:T1 | In i s}) => match v return F2 (proj1_sig v) with (exist _ i h) => e (exist _ i (or_intror h)) end).
  apply SV.InCUnion_intro with (u:=e0); simpl; auto.
  apply IHs.
  
  intro.
  eapply SV.InCUnion_intro with (u:= e (exist _ a (or_introl eq_refl))); simpl; auto.
  apply fin_all.
  intro.
  left.
  apply functional_extensionality_dep; intro v.
  destruct v; simpl; auto.
  destruct (eq_dec a x).
  subst x.
  match goal with |- match ?cnd with _=>_ end = _ => destruct cnd; try (exfalso; tauto) end.
  rewrite (proof_irrelevance _ _ eq_refl).
  rewrite (proof_irrelevance _ _ o).
  reflexivity.
  match goal with |- match ?cnd with _=>_ end = _ => destruct cnd end.
  exfalso; subst x; tauto.
  rewrite (proof_irrelevance _ _ o).
  reflexivity.
Qed.

Program Definition OneFin: Finite := {| fin_dec := OneDec; fin_set := SV.sing OneDec one |}.
Next Obligation.
  destruct x; left; reflexivity.
Qed.

Program Definition TwoFin: Finite := {| fin_dec := TwoDec; fin_set := SV.add (T:=TwoDec) true (SV.sing TwoDec false) |}.
Next Obligation.
  destruct x; tauto.
Qed.

Lemma ex_dec: forall `{F:Finite} (P: F -> Decidable), {k | P k}+{forall k, not (P k)}.
Proof.
  intros.
  destruct (SV.ex_dec P (@fin_set _ F)); [left|right]; intros.
  destruct s.
  exists x; tauto.
  apply (n k); clear n.
  apply fin_all.
Defined.

Lemma first_dec: forall `{F:Finite} (P: F -> Decidable), {k | P k}+{forall k, SV.set_In k fin_set -> not (P k)}.
Proof.
  intros.
  destruct (SV.first_dec P (@fin_set _ F)); [left|right]; intros.
  destruct s.
  exists x; tauto.
  apply (n k H).
Defined.

Lemma last_dec: forall `{F:Finite} (P: F -> Decidable), {k | P k}+{forall k, SV.set_In k fin_set -> not (P k)}.
Proof.
  intros.
  destruct (SV.last_dec P (@fin_set _ F)); [left|right]; intros.
  destruct s.
  exists x; tauto.
  apply (n k H).
Defined.

Lemma all_dec `{F: Finite} (P: F -> Decidable): (forall k, P k) + {k | not (P k)}.
Proof.
  destruct (ex_dec (fun x => NotDec (P x))).
  right; apply s.
  left; intro.
  apply NNPP; intro.
  apply (n k).
  apply H.
Defined.

Program Instance ExDecidable {T} {P: T -> Prop} (ch: {k:T | P k}+{forall k, not (P k)}): Decidable :=
{|
  dcPred := exists k, P k
|}.
Next Obligation.
  destruct ch; [left|right].
  destruct s as [k h]; exists k; auto.
  intro.
  destruct H as [k h]; apply (n k h).
Defined.

Program Instance AllDecidable {T} {P: T -> Prop} (ch: ((forall k, P k)+{k:T | not (P k)})): Decidable :=
{|
  dcPred := forall k, P k
|}.
Next Obligation.
  destruct ch; [left|right]; intros; auto.
  destruct s as [k h].
  intro.
  apply h; apply (H k).
Defined.

Lemma all1_dec `{F: Finite} (P: F -> Decidable): Decidable.
Proof.  
  exists (forall x, @dcPred (P x)).
  destruct (all_dec (fun x => P x)); [left; auto|right; repeat intro].
  destruct s as [x h]; simpl in h.
  apply (h (H x)).
Defined.

Lemma all2_dec `{F: Finite} (P: F -> F -> Decidable): Decidable.
Proof.  
  exists (forall x y, @dcPred (P x y)).
  destruct (all_dec (fun x => AllDecidable (all_dec (fun y => P x y)))); [left|right].
  apply d.
  intro.
  destruct s as [x h]; simpl in h.
  apply (h (H x)).
Defined.
