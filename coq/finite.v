Add LoadPath "$HOME/COQ/FO-LTL" as Top.

Require Import Classical.
Require Import Eqdep_dec.

Require Import Top.dec.
Require Import Top.set.

Inductive isFinite `(T: EqDec): Prop :=
  isFinite_intro: forall s: SV.set T, (forall x, SV.set_In x s) -> isFinite T.

Class Finite {T} := {
  fin_dec : @EqDec T;
  fin_set: SV.set fin_dec;
  fin_all: forall x, SV.set_In x fin_set;
}.
Coercion fin_dec: Finite >-> EqDec.
Arguments fin_set _ _ : assert.

Lemma FiniteIsFinite: forall `(F: Finite), isFinite F.
Proof.
  intros.
  apply isFinite_intro with (s:= fin_set).
  apply fin_all.
Qed.

Program Definition asDec `{T:EqDec} (s: SV.set T): @EqDec {x : T | SV.set_In x s} := {|
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

Definition PairSet `{T1: EqDec} {U: T1 -> Type} {T2: forall t, @EqDec (U t)}  {e1: SV.set T1} (e2: forall x, SV.set (T2 x)): SV.set (PairDec T1 T2) :=
    SV.GUnion (T1 := T1) (T2 := PairDec T1 T2)
      e1 e1
      (fun s h => 
          SV.image (T1 := T2 s) (T2 := PairDec T1 T2)
            (fun d => (existT _ s d))
            (e2 s)).

Program Definition PairFin `(F1: Finite) {U2:F1->Type} (F2: forall t, @Finite (U2 t)): Finite := {|
  fin_dec := PairDec F1 F2;
  fin_set := PairSet (T1:=F1) (T2:=F2) (e1:=@fin_set _ F1) (fun x => @fin_set _ (F2 x))
|}.
Next Obligation.
  intros.
  destruct x.
  apply SV.InCUnion_intro with (u:= x); simpl; intros.
  apply fin_all.
  apply fin_all.
  apply (SV.InImage_intro (T1:=F2 x) (T2 := PairDec F1 F2)) with (w:=e); auto.
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
