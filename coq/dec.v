
Require Import Eqdep_dec.
Require Import Coq.Logic.JMeq.
Require Import Program.Tactics.
Require Import ProofIrrelevance.
Require Import Coq.Bool.Bool.
Require Import Fin.

Definition EqDecType T := forall x y: T, {x=y}+{x<>y}.

Class EqDec {T: Type} := {
  eqDom: Type := T;
  eq_dec: EqDecType eqDom
}.
Coercion eqDom: EqDec >-> Sortclass.

Class Decidable := {
  dcPred: Prop;
  dc_dec: {dcPred }+{not dcPred}
}.
Coercion dcPred: Decidable >-> Sortclass.

Definition TrueDec: Decidable := {|
  dcPred := True;
  dc_dec := left I
|}.

Definition FalseDec: Decidable := {|
  dcPred := False;
  dc_dec := right (fun h:False => match h with end)
|}.

Program Definition NotDec (P: Decidable): Decidable := {|
  dcPred := not P
|}.
Next Obligation.
  destruct (@dc_dec P); simpl.
  right.
  intro.
  apply (H d).
  left.
  apply n.
Defined.

Program Definition AndDec (P Q: Decidable) : Decidable := {|
  dcPred := P /\ Q;
|}.
Next Obligation.
  destruct (@dc_dec P).
  destruct (@dc_dec Q); [left; auto | right; intro; tauto].
  right; intro; tauto.
Defined.

Program Definition OrDec (P Q: Decidable) : Decidable := {|
  dcPred := P \/ Q;
|}.
Next Obligation.
  destruct (@dc_dec P).
  left; left; tauto.
  destruct (@dc_dec Q); [left; right; auto | right; intro; tauto].
Defined.

Program Definition ImpDec (P Q: Decidable) : Decidable := {|
  dcPred := P -> Q;
|}.
Next Obligation.
  destruct (@dc_dec P).
  destruct (@dc_dec Q).
  left; intro; tauto.
  right; intro; tauto.
  left; intro; tauto.
Defined.

Program Definition IffDec (P Q: Decidable) : Decidable := {|
  dcPred := P <-> Q;
|}.
Next Obligation.
  destruct (@dc_dec P).
  destruct (@dc_dec Q).
  left; intros; tauto.
  right; intros; tauto.
  destruct (@dc_dec Q).
  right; intros; tauto.
  left; intros; tauto.
Defined.

Program Definition AndThenDec (P: Decidable) (Q: P -> Decidable): Decidable := {|
  dcPred := exists p: P, Q p;
|}.
Next Obligation.
  destruct (@dc_dec P).
  destruct (@dc_dec (Q d)); [left | right].
  exists d; auto.
  intro.
  destruct H as [p h].
  rewrite (proof_irrelevance _ p d) in h.
  apply (n h).
  right; intro.
  destruct H as [p _].
  apply (n p).
Defined.

Instance isEq `{T: EqDec} (x y:T) : Decidable := {
  dcPred := x=y;
  dc_dec := eq_dec x y
}.

Instance isEqF (T1: Type) `{T2: EqDec} (f: T1->T2) (x: T2) (y:T1) : Decidable := {
  dcPred := x=f y;
  dc_dec := eq_dec x (f y)
}.

Lemma inj_pairT1
     : forall {U : Type} {P : U -> Type} {p q x y},
       existT P p x = existT P q y -> p = q.
Proof.
  intros.
  injection H; intros; auto.
Qed.

Program Instance isEq2 `{T1: EqDec} {T2: T1->Type} {U: forall t, @EqDec (T2 t)} (x1:T1) (y1: U x1) (x2:T1) (y2: U x2) : Decidable := {
  dcPred := existT U x1 y1 = existT U x2 y2; 
  dc_dec := _
}.
Next Obligation.
  intros.
  destruct (eq_dec x1 x2).
  subst x2.
  destruct (eq_dec y1 y2).
  subst y2.
  left; easy.
  right; intro.
  apply n; clear n.
  apply inj_pair2_eq_dec in H; auto.
  intros; apply eq_dec.

  right; intro.
  inversion H.
  apply (n H1).
Qed.

Program Instance uptoDec n: @EqDec (Fin.t n) := {| eq_dec := Fin.eq_dec |}.


Program Instance PairDec `(T1: EqDec) {T2: T1->Type} (U: forall t, @EqDec (T2 t)): @EqDec {x:T1 & U x} := {| eq_dec := _ |}.
Next Obligation.
  repeat intro.
  destruct x; destruct y.
  apply isEq2.
Defined.

Program Definition SumDec `(T1: EqDec) `(T2: EqDec) : @EqDec (T1+T2) := {|
  eq_dec := _;
|}.
Next Obligation.
  repeat intro; decide equality; apply eq_dec.
Qed.

Inductive IncType T :=
  New: IncType T
| Old: T -> IncType T.

Program Definition IncDec `(T: EqDec) : @EqDec (IncType T) := {| eq_dec := _ |}.
Next Obligation.
  repeat intro; decide equality; apply eq_dec.
Qed.

Definition eProduct `(T1: EqDec) `(T2: EqDec): @EqDec (T1*T2).
  Proof.
    split; repeat intro.
    destruct x as [x1 x2].
    destruct y as [y1 y2].
    destruct (eq_dec x1 y1).
    destruct (eq_dec x2 y2).
    left.
    rewrite e,e0; reflexivity.
    right; intro.
    injection H; clear H; intros.
    apply (n H).
    right; intro.
    injection H; clear H; intros.
    apply (n H0).
  Defined.

  Inductive One: Type := one: One.
  
  Definition OneDec: @EqDec One := {| 
    eq_dec x y := left (match x,y with one,one => eq_refl end)
  |}.

  Definition TwoDec: @EqDec bool := {| eq_dec := Bool.bool_dec |}.
  
