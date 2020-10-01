Add LoadPath "$HOME/COQ/FO-LTL" as Top.

Require Import Eqdep_dec.
Require Import Coq.Logic.FunctionalExtensionality.
Import EqNotations.
Require Import Coq.Logic.JMeq.
Require Import ProofIrrelevance.
Require Import Classical.

Require Import Top.dec.
Require Import Top.finite.
Require Import Top.set.

(*
http://people.mpi-inf.mpg.de/~mvoigt/files/LICS2016_slides.pdf
http://web.cs.wpi.edu/~tn/publications/finite-model-osl-TR.pdf
https://hal.inria.fr/tel-02406821/document
http://people.mpi-inf.mpg.de/~mvoigt/files/Dissertation_with_hyperref.pdf
  => p 13
*)

SubClass SortT {Ts} := @Finite Ts.
SubClass VariableT {Tv} := @Finite Tv.
SubClass ConstantT {Tc} := @Finite Tc.
SubClass PredicateT {Tp} := @EqDec Tp.
SubClass ArityT {Ta} := @Finite Ta.

Class Sig {Ts: Type} {Tv: Ts->Type} {Tc: Ts->Type} {Tp} {Ta: Tp -> Type} := {
  Sort: @SortT Ts;
  variable: forall (s:Sort), @VariableT (Tv s);
  constant: forall (s:Sort), @ConstantT (Tc s);
  predicate: @PredicateT Tp;
  pr_arity: forall (p: predicate), @ArityT (Ta p);
  pr_args: forall p, pr_arity p -> Sort;
}.

Class Dom {Ts Tv Tc Tp Ta} (Sg: @Sig Ts Tv Tc Tp Ta) := {
  ssemT : Sort -> Type;
  ssem : forall s, @EqDec (ssemT s);
  domType: EqDec := PairDec Sort ssem;
  neDom: forall s, ssem s
}.
Coercion domType : Dom >-> EqDec.

Definition sem_eq `{Sg: Sig} {s1 s2: Sort} {D: Dom Sg}: ssem s1 -> ssem s2 -> Prop :=
  match eq_dec s1 s2 return ssem s1 -> ssem s2 -> Prop with
    left h => 
      match h in _=s2 return ssem _ -> ssem s2 -> Prop with
        eq_refl => fun d1 d2 => d1 = d2
      end
  | right _ => fun d1 d2 => False
  end.

Lemma sem_eq_s: forall `{Sg: Sig} s (D: Dom Sg) (d1 d2: ssem s),
  sem_eq d1 d2 <-> d1=d2.
Proof.
  intros.
  unfold sem_eq.
  destruct (eq_dec s s); try tauto.
  rewrite (proof_irrelevance _ e eq_refl); tauto.
Qed.

Class Interp `{Sg: Sig} (D: Dom Sg) := {
  csem {s: Sort} (c: constant s): ssem s;
  psem (p: predicate): nat -> (forall i, ssem (pr_args p i)) -> Prop;
}.

Section FO.
  Context {Ts: Type} {Tv: Ts->Type} {Tc: Ts->Type} {Tp: Type} {Ta: Tp -> Type}.
  Variable mySig: @Sig Ts Tv Tc Tp Ta.
  Existing Instance mySig.

Definition Env (D: Dom mySig) := forall s, variable s -> ssem s.

Definition add {D: Dom mySig} {s} (v: variable s) (d: ssem s) (env: Env D): Env D:=
  fun s' =>
    match eq_dec s s' with
      left h =>
        match h in _=s' return variable s' -> _ with  
          eq_refl => fun w => if eq_dec v w then d else env s w
        end
    | right _ => fun w => env s' w
    end.

Definition iadd {D: Dom mySig} `(K: Finite) 
  (sk: K->Sort) (vk: forall k:K, variable (sk k)) (dk: forall k:K, ssem (sk k)) (env: Env D): Env D :=
  fun (s: Sort) (v: variable s) =>
    match ex_dec (fun k => isEq2 (U:=variable) (sk k) (vk k) s v) with
      inleft (exist _ k h) =>
        match h in _=sv return ssem (projT1 sv) with
          eq_refl => dk k
        end
    | inright h => env s v
    end.

Lemma iaddOne: forall (D: Dom mySig) s (v: variable s) (dk: OneFin -> ssem s) env,
  iadd OneFin (fun _ => s) (fun _ => v) dk env = add v (dk one) env.
Proof.
  intros.
  apply functional_extensionality_dep; intro s';
  apply functional_extensionality_dep; intro v'.
  unfold iadd.
  match goal with |- match ?cnd with _=>_ end=_ => destruct cnd end.
  destruct s0.
  injection d; intros; subst s'.
  generalize d; intro d'.
  apply inj_pair2_eq_dec in d; try apply eq_dec; subst v'.
  rewrite (proof_irrelevance _ d' eq_refl).
  unfold add.
  destruct (eq_dec s s); try tauto.
  rewrite (proof_irrelevance _ e eq_refl).
  destruct (eq_dec v v); try tauto.
  destruct x; tauto.

  unfold add.
  destruct (eq_dec s s'); auto.
  subst s'.
  destruct (eq_dec v v'); auto.
  subst v'.
  exfalso; apply (n one); reflexivity.
Qed.

Lemma add_eq: forall (D: Dom mySig) (env: Env D) s v d,
  add v d env s v = d.
Proof.
  intros.
  unfold add.
  destruct (eq_dec s s); try tauto.
  rewrite (proof_irrelevance _ e eq_refl).
  destruct (eq_dec v v); tauto.
Qed.

Lemma add_ne: forall (D: Dom mySig) (env: Env D) s v w d,
  v <> w -> add v d env s w = env s w.
Proof.
  intros.
  unfold add.
  destruct (eq_dec s s); try tauto.
  rewrite (proof_irrelevance _ e eq_refl).
  destruct (eq_dec v w); tauto.
Qed.

Lemma add_ne2: forall (D: Dom mySig) (env: Env D) s v s' w d,
  ~ isEq2 s v s' w -> add v d env s' w = env s' w.
Proof.
  intros.
  unfold add.
  destruct (eq_dec s s'); auto.
  subst s'.
  destruct (eq_dec v w); auto.
  subst w.
  exfalso; apply H; reflexivity.
Qed.

Lemma add_upd: forall (D: Dom mySig) (env: Env D) s v w,
  add v (env s w) env s w = env s w.
Proof.
  intros.
  unfold add.
  destruct (eq_dec s s); try tauto.
  rewrite (proof_irrelevance _ e eq_refl).
  destruct (eq_dec v w); tauto.  
Qed.

Lemma add_id: forall (D: Dom mySig) (env: Env D) s v,
  add v (env s v) env = env.
Proof.
  intros.
  unfold add.
  apply functional_extensionality_dep; intro s'.
  apply functional_extensionality_dep; intro w.
  destruct (eq_dec s s'); try tauto.
  subst s'.
  destruct (eq_dec v w); try tauto.
  subst w; auto.
Qed.

Lemma add_add_eq: forall (D: Dom mySig) (env: Env D) s (v: variable s) d d',
  add v d (add v d' env) = add v d env.
Proof.
  intros.
  apply functional_extensionality_dep; intro s'.
  apply functional_extensionality_dep; intro w.
  
  unfold add.
  destruct (eq_dec s s'); try tauto.
  subst s'.
  destruct (eq_dec s s); try tauto.
  rewrite (proof_irrelevance _ e eq_refl).
  destruct (eq_dec v w); tauto.
Qed.

Lemma add_add_ne_swp: forall (D: Dom mySig) (env: Env D) {s1} (v1: variable s1) {s2} (v2: variable s2) d1 d2,
  not (isEq2 (U:=variable) s1 v1 s2 v2) ->
    add v1 d1 (add v2 d2 env) = add v2 d2 (add v1 d1 env).
Proof.
  intros.
  apply functional_extensionality_dep; intro s'.
  apply functional_extensionality_dep; intro w.
  
  unfold add.
  destruct (eq_dec s1 s'); try tauto.
  subst s'.
  destruct (eq_dec s2 s1); try tauto.
  subst s2.
  destruct (eq_dec s1 s1); try tauto.
  rewrite (proof_irrelevance _ e eq_refl).
  destruct (eq_dec v1 w); try tauto.
  subst w.
  destruct (eq_dec v2 v1); auto.
  subst v2.
  destruct (H eq_refl).
  
  destruct (eq_dec s2 s'); try tauto.
  subst s'.
  destruct (eq_dec s1 s2); tauto.
Qed.

Inductive term (s: Sort): Type :=
  Var: variable s -> term s
| Cst: constant s -> term s.

Lemma tm_dec: forall s, EqDecType (term s).
Proof.
  unfold EqDecType; intros.
  decide equality; apply eq_dec.
Qed.

Definition tmDec s := {| eq_dec := tm_dec s |}.

Fixpoint tm_sem {D: Dom mySig} {Itp: Interp D} {s} (env: Env D) (tm: term s): ssem s :=
  match tm with
    Var _ v => env _ v
  | Cst _ c => csem c
  end.

Inductive literal: Type :=
  PApp: nat -> forall (p: predicate), (forall i, term (pr_args p i)) -> literal.

Lemma lt_dec: EqDecType literal.
Proof.
  unfold EqDecType; intros.
  destruct x; destruct y.
  destruct (eq_dec p p0).
  subst p0.
  destruct (PeanoNat.Nat.eq_dec n n0).
  subst n0.
  destruct (all_dec (F:=pr_arity p) (fun i => isEq (T:=tmDec (pr_args p i)) (t i) (t0 i))).
  left.
  f_equal.
  apply functional_extensionality_dep; intro i.
  apply d.
  right; intro.
  destruct s as [k h]; apply h; clear h.
  injection H; intros; subst.
  apply inj_pair2_eq_dec in H0; try apply eq_dec.
  subst t0; apply eq_refl.
  right; intro.
  injection H; intros; subst n0; tauto.
  right; intro.
  injection H; intros; subst p0; tauto.
Qed.

Definition ltDec := {| eq_dec := lt_dec |}.

Fixpoint lt_sem {D: Dom mySig} {Itp: Interp D} (env: Env D) (lt: literal) (t:nat): Prop :=
  match lt with
  | PApp n p args => psem p (n+t) (fun i => tm_sem env (args i))
  end.

Inductive atom: Type :=
| Literal: literal -> atom
| NLiteral: literal -> atom
| Eq: forall s, term s -> term s -> atom
| NEq: forall s, term s -> term s -> atom.

Lemma at_dec: EqDecType atom.
Proof.
  unfold EqDecType; intros.
  destruct x; destruct y; try (right; discriminate).
  destruct (lt_dec l l0); [left; subst; tauto | right].
  intro h; apply n; injection h; intros; subst; now auto.
  
  destruct (lt_dec l l0); [left; subst; tauto | right].
  intro h; apply n; injection h; intros; subst; now auto.

  destruct (eq_dec s s0); [subst s0 | right; intro].
  destruct (tm_dec s t t1); [subst t1 | right; intro].
  destruct (tm_dec s t0 t2); [subst t2;left;auto | right; intro].
  injection H; intros; subst; auto.
  apply inj_pair2_eq_dec in H0; try apply eq_dec; subst; tauto.
  injection H; intros; subst; auto.
  apply inj_pair2_eq_dec in H1; try apply eq_dec; subst; tauto.
  injection H; intros; subst; auto.

  destruct (eq_dec s s0); [subst s0 | right; intro].
  destruct (tm_dec s t t1); [subst t1 | right; intro].
  destruct (tm_dec s t0 t2); [subst t2;left;auto | right; intro].
  injection H; intros; subst; auto.
  apply inj_pair2_eq_dec in H0; try apply eq_dec; subst; tauto.
  injection H; intros; subst; auto.
  apply inj_pair2_eq_dec in H1; try apply eq_dec; subst; tauto.
  injection H; intros; subst; auto.
Qed.

Definition atDec := {| eq_dec := at_dec |}.

Inductive formula: Type :=
  FTrue: formula
| FFalse: formula
| Atom: atom -> formula
| And: formula -> formula -> formula 
| Or: formula -> formula -> formula
| Ex: forall s, variable s -> formula -> formula
| All: forall s, variable s -> formula -> formula
| F: formula -> formula
| G: formula -> formula.

Lemma fm_dec: EqDecType formula.
Proof.
  intros f1 f2.
  revert f1 f2; double induction f1 f2; clear f1 f2; try (right; intros; discriminate);
    try (left; reflexivity).
  - intros.
    destruct (at_dec a a0); [left|right].
    subst a0; now auto.
    intro h; injection h; intros; subst a0; tauto.
  - intros.
    destruct (X1 f); [subst f | right; intros].
    destruct (X2 f0); [subst f0; left; auto | right; intros].
    intro h; injection h; intros; subst; tauto.
    intro h; injection h; intros; subst; tauto.
  - intros.
    destruct (X1 f); [subst f | right; intros].
    destruct (X2 f0); [subst f0; left; auto | right; intros].
    intro h; injection h; intros; subst; tauto.
    intro h; injection h; intros; subst; tauto.
  - intros.
    destruct (eq_dec s s0); [subst s0 | right; intros].
    destruct (eq_dec e e0); [subst e0 | right; intros].
    destruct (X0 f); [subst f0; auto | right; intros].
    intro h; injection h; intros; subst; tauto.
    intro h.
    injection h; intros.
    apply inj_pair2_eq_dec in H0; try apply eq_dec; subst e0; tauto.
    intro h; injection h; intros; subst; tauto.
  - intros.
    destruct (eq_dec s s0); [subst s0 | right; intros].
    destruct (eq_dec e e0); [subst e0 | right; intros].
    destruct (X0 f); [subst f0; auto | right; intros].
    intro h; injection h; intros; subst; tauto.
    intro h.
    injection h; intros.
    apply inj_pair2_eq_dec in H0; try apply eq_dec; subst e0; tauto.
    intro h; injection h; intros; subst; tauto.
  - intros.
    destruct (X0 f); [left; subst f0; auto | right; intros].
    intro h; injection h; intros; subst; tauto.
  - intros.
    destruct (X0 f); [left; subst f0; auto | right; intros].
    intro h; injection h; intros; subst; tauto.
Qed.

Definition fmDec := {| eq_dec := fm_dec |}.

Definition IAnd `(K: Finite) (fk: K -> formula): formula :=
  List.fold_right (fun k r => And (fk k) r) FTrue fin_set.

Definition IOr `(K: Finite) (fk: K -> formula): formula :=
  List.fold_right (fun k r => Or (fk k) r) FFalse fin_set.

Definition IEx `(K:Finite) (sk: K->Sort) (vk:forall k, variable (sk k)) (f: formula): formula :=
  List.fold_right (fun k r => Ex (sk k) (vk k) r) f fin_set.

Definition IAll `(K:Finite) (sk: K->Sort) (vk:forall k, variable (sk k)) (f: formula): formula :=
  List.fold_right (fun k r => All (sk k) (vk k) r) f fin_set.

Definition at_sem {D: Dom mySig} {Itp: Interp D} (env: Env D) (a: atom) t: Prop :=
  match a with
  | Literal a => lt_sem env a t
  | NLiteral a => not (lt_sem env a t)
  | Eq _ t1 t2 => tm_sem env t1 = tm_sem env t2
  | NEq _ t1 t2 => tm_sem env t1 <> tm_sem env t2
  end.

Fixpoint fm_sem {D: Dom mySig} {Itp: Interp D} (env: Env D) (f: formula) t: Prop :=
  match f with
  | FTrue => True
  | FFalse => False
  | Atom a => at_sem env a t
  | And f1 f2 => fm_sem env f1 t /\ fm_sem env f2 t
  | Or f1 f2 => fm_sem env f1 t \/ fm_sem env f2 t
  | Ex s v f => exists (d: ssem s), fm_sem (add v d env) f t
  | All s v f => forall (d: ssem s), fm_sem (add v d env) f t
  | F f => exists t', t' >= t /\ fm_sem env f t'
  | G f => forall t', t' >= t -> fm_sem env f t'
  end.

Ltac fm_semTac :=
    match goal with
      H: fm_sem ?e1 ?f ?t |- fm_sem ?e2 ?f ?t => assert (e1 = e2) as eeq;
        try (rewrite eeq in H; assumption); 
        apply functional_extensionality_dep; intro; 
        apply functional_extensionality_dep; intro
    end.

Lemma F_sem: forall {D: Dom mySig} {Itp: Interp D} (env: Env D) (f: formula) t,
  fm_sem env (F f) t <-> (exists t', t' >= t /\ fm_sem env f t').
Proof.
  intros; reflexivity.  
Qed.

Lemma G_sem: forall {D: Dom mySig} {Itp: Interp D} (env: Env D) (f: formula) t,
  fm_sem env (G f) t <-> (forall t', t' >= t -> fm_sem env f t').
Proof.
  intros; reflexivity.  
Qed.

Definition atNot (a: atom): atom :=
  match a with
    Literal a => NLiteral a
  | NLiteral a => Literal a
  | Eq s t1 t2 => NEq s t1 t2
  | NEq s t1 t2 => Eq s t1 t2
  end.

Fixpoint Not (f: formula): formula :=
  match f with
  | FTrue => FFalse
  | FFalse => FTrue
  | Atom a => Atom (atNot a)
  | And f1 f2 => Or (Not f1) (Not f2)
  | Or f1 f2 => And (Not f1) (Not f2)
  | Ex s v f => All s v (Not f)
  | All s v f => Ex s v (Not f)
  | F f => G (Not f)
  | G f => F (Not f)
  end.

Lemma atNot_sem: forall {D: Dom mySig} {Itp: Interp D} (a: atom) (env: Env D) t,
  at_sem env (atNot a) t <-> not (at_sem env a t).
Proof.
  intros.
  destruct a; simpl; tauto.
Qed.

Lemma Not_sem: forall {D: Dom mySig} {Itp: Interp D} (f: formula) (env: Env D) t,
  fm_sem env (Not f) t <-> not (fm_sem env f t).
Proof.
  induction f; simpl; intros; auto; try tauto.
 - apply atNot_sem.
 - rewrite IHf1, IHf2.
   tauto.
 - rewrite IHf1, IHf2.
   tauto.
 - setoid_rewrite IHf; split; intros.
   intro.
   destruct H0 as [k H0].
   apply (H k H0).
   intro; apply H; clear H.
   exists d; auto.
 - setoid_rewrite IHf; split; intros.
   destruct H as [d H].
   intro.
   apply (H (H0 d)).
   apply not_all_ex_not in H.
   destruct H as [d H].
   exists d; auto.
 - setoid_rewrite IHf; split; intros.
   intro.
   destruct H0 as [t' [h1 h2]].
   apply (H t' h1 h2).
   intro.
   apply H; exists t'; tauto.
 - setoid_rewrite IHf; split; intros.
   intro.
   destruct H as [t' [h1 h2]].
   apply (h2 (H0 t' h1)).
   apply not_all_ex_not in H.
   destruct H as [t' H].
   exists t'; tauto.
Qed.

Lemma IAnd_sem: forall D (Itp: Interp D) env `(K: Finite) fk t,
  fm_sem env (IAnd K fk) t <-> forall k, fm_sem env (fk k) t.
Proof.
  intros; simpl.
  unfold IAnd.
  assert ((forall k : K, fm_sem env (fk k) t) <-> (forall k : K, SV.set_In k fin_set -> fm_sem env (fk k) t)).
    generalize fin_all; repeat (split || intro); now auto.
  rewrite H; clear H.    
      
  induction fin_set; simpl; intros; auto.
  - split; intros; tauto.
  - rewrite IHs; clear IHs.
    split; intros; try tauto.
    destruct H0; try subst a; try tauto.
    apply H; now auto.
    
    split; auto.
Qed.

Lemma IOr_sem: forall D (Itp: Interp D) env `(K: Finite) fk t,
  fm_sem env (IOr K fk) t <-> exists k, fm_sem env (fk k) t.
Proof.
  intros; simpl.
  unfold IOr.
  assert ((exists k : K, fm_sem env (fk k) t) <-> (exists k : K, SV.set_In k fin_set /\ fm_sem env (fk k) t)).
    generalize fin_all; repeat (split || intro).
    destruct H0 as [k H0]; exists k; now auto.
    destruct H0 as [k H0]; exists k; now auto.
  rewrite H; clear H.    
      
  induction fin_set; simpl; intros; auto.
  - split; intros; try tauto.
    destruct H as [k H]; tauto.
  - rewrite IHs; clear IHs.
    split; intros.
    destruct H.
    exists a; split; auto; left; now auto.
    destruct H as [k [h1 h2]].
    exists k; split; auto; right; now auto.
    
    destruct H as [k [h1 h2]].
    destruct h1; [subst;left|right;exists k]; auto.
Qed.

Definition ltX l :=
  match l with
    PApp n p args => PApp (S n) p args
  end.

Definition atX a :=
  match a with
    Literal l => Literal (ltX l)
  | NLiteral l => NLiteral (ltX l)
  | e => e
  end.

Fixpoint X (f: formula): formula :=
  match f with
  | FTrue => FTrue
  | FFalse => FFalse
  | Atom a => Atom (atX a)
  | And f1 f2 => And (X f1) (X f2)
  | Or f1 f2 => Or (X f1) (X f2)
  | Ex s v f => Ex s v (X f)
  | All s v f => All s v (X f)
  | F f => F (X f)
  | G f => G (X f)
  end.

Lemma ltX_sem: forall {D: Dom mySig} {Itp: Interp D} (l: literal) (env: Env D) t,
  lt_sem env (ltX l) t <-> lt_sem env l (S t).
Proof.
  intros.
  destruct l; simpl; try tauto.
  rewrite plus_n_Sm.
  reflexivity.
Qed.

Lemma atX_sem: forall {D: Dom mySig} {Itp: Interp D} (a: atom) (env: Env D) t,
  at_sem env (atX a) t <-> at_sem env a (S t).
Proof.
  intros.
  destruct a; simpl; try tauto.
  apply ltX_sem.
  apply not_iff_compat.
  apply ltX_sem.
Qed.

Lemma X_sem: forall {D: Dom mySig} {Itp: Interp D} (f: formula) (env: Env D) t,
  fm_sem env (X f) t <-> fm_sem env f (S t).
Proof.
  induction f; simpl; intros; try tauto;
    try (apply atX_sem);
    try (setoid_rewrite H; reflexivity);
    try (setoid_rewrite IHf; reflexivity).
  rewrite IHf1, IHf2; reflexivity.
  rewrite IHf1, IHf2; reflexivity.
  setoid_rewrite IHf.
  split; intro.
  destruct H as [t' [h1 h2]].
  exists (S t'); split; auto.
  apply Le.le_n_S; auto.

  destruct H as [t' [h1 h2]].
  destruct t'; try (now inversion h1).
  exists t'; split; simpl; auto.
  apply le_S_n in h1; apply h1.

  setoid_rewrite IHf.
  split; intros.
  destruct t'; try (now inversion H0).
  apply H; now auto with arith.

  apply H.
  auto with arith.
Qed.

Definition isX (f: formula) := (exists g, f = X g).

Lemma ltX_dec (l: literal) : { l' | l = ltX l'} + (forall l', l <> ltX l').
Proof.
  destruct l; simpl.
  destruct n; [right | left]; repeat intro.
  destruct l'; discriminate.
  exists (PApp n p t); reflexivity.
Qed.

Lemma atX_dec (a: atom) : { b | a = atX b} + (forall b, a <> atX b).
Proof.
  destruct a; simpl.
  destruct (ltX_dec l).
  left; auto.
  destruct s as [l' h]; subst.
  exists (Literal l'); reflexivity.
  right; repeat intro.
  destruct b; simpl in H; try discriminate.
  injection H; clear H; intros; subst.
  apply (n l0); now auto.

  destruct (ltX_dec l).
  destruct s as [l' h]; subst.
  left; exists (NLiteral l'); reflexivity.
  right; repeat intro.
  destruct b; simpl in H; try discriminate.
  injection H; clear H; intros; subst.
  apply (n l0); now auto.

  left; exists (Eq s t t0); reflexivity.
  left; exists (NEq s t t0); reflexivity.
Qed.

Lemma isX_dec (f: formula) : { g | f = X g} + (forall g, f <> X g).
Proof.
  induction f; intros.
  - left; exists FTrue; reflexivity.
  - left; exists FFalse; reflexivity.
  - destruct (atX_dec a); [left | right]; repeat intro.
   destruct s as [b H]; subst.
   exists (Atom b); reflexivity.
   destruct g; try discriminate; simpl in H.
   injection H; clear H; intros; subst.
   apply (n a0); now auto.
  - destruct IHf1.
    destruct s as [g1 H1]; subst.
    destruct IHf2.
    destruct s as [g2 H2]; subst.
    left; exists (And g1 g2); reflexivity.
    right; repeat intro.
    destruct g; try discriminate; simpl in H.
    injection H; clear H; intros; subst.
    apply (n g3); now auto.
    right; repeat intro.
    destruct g; try discriminate; simpl in H.
    injection H; clear H; intros; subst.
    apply (n g1); now auto.
  - destruct IHf1.
    destruct s as [g1 H1]; subst.
    destruct IHf2.
    destruct s as [g2 H2]; subst.
    left; exists (Or g1 g2); reflexivity.
    right; repeat intro.
    destruct g; try discriminate; simpl in H.
    injection H; clear H; intros; subst.
    apply (n g3); now auto.
    right; repeat intro.
    destruct g; try discriminate; simpl in H.
    injection H; clear H; intros; subst.
    apply (n g1); now auto.
  - destruct IHf.
    destruct s0 as [g h]; subst.
    left; exists (Ex s e g); reflexivity.
    right; repeat intro.
    destruct g; simpl in *; try discriminate.
    injection H; clear H; intros; subst.
    apply inj_pair2_eq_dec in H0; try apply eq_dec.
    apply (n g); now auto.
  - destruct IHf.
    destruct s0 as [g h]; subst.
    left; exists (All s e g); reflexivity.
    right; repeat intro.
    destruct g; simpl in *; try discriminate.
    injection H; clear H; intros; subst.
    apply inj_pair2_eq_dec in H0; try apply eq_dec.
    apply (n g); now auto.
  - destruct IHf.
    destruct s as [g h]; subst.
    left; exists (F g); reflexivity.
    right; repeat intro.
    destruct g; simpl in *; try discriminate.
    injection H; clear H; intros; subst.
    apply (n g); now auto.
  - destruct IHf.
    destruct s as [g h]; subst.
    left; exists (G g); reflexivity.
    right; repeat intro.
    destruct g; simpl in *; try discriminate.
    injection H; clear H; intros; subst.
    apply (n g); now auto.
Qed.

Lemma ltX_inj: forall l1 l2, ltX l1 = ltX l2 -> l1 = l2.
Proof.
  intros; destruct l1; destruct l2; try discriminate; auto.
  simpl in H.
  injection H; clear H; intros; subst.
  apply inj_pair2_eq_dec in H; try apply eq_dec; subst; auto.
Qed.

Lemma atX_inj: forall a1 a2, atX a1 = atX a2 -> a1 = a2.
Proof.
  intros; destruct a1; destruct a2; intros; try discriminate; simpl in *; auto.
  injection H; clear H; intros.
  apply ltX_inj in H; subst; auto.
  injection H; clear H; intros.
  apply ltX_inj in H; subst; auto.
Qed.

Lemma X_inj: forall f1 f2, X f1 = X f2 -> f1 = f2.
Proof.
  double induction f1 f2; intros; try discriminate; simpl in *; auto.
  injection H; clear H; intros.
  apply atX_inj in H; subst; now auto.

  injection H3; clear H3; intros.
  apply H2 in H3; apply H1 in H4; subst; now auto.

  injection H3; clear H3; intros.
  apply H2 in H3; apply H1 in H4; subst; now auto.

  injection H1; clear H1; intros; subst.
  apply H0 in H1; subst.
  apply inj_pair2_eq_dec in H2; try apply eq_dec; subst;now auto.

  injection H1; clear H1; intros; subst.
  apply H0 in H1; subst.
  apply inj_pair2_eq_dec in H2; try apply eq_dec; subst;now auto.

  injection H1; clear H1; intros; subst.
  apply H0 in H1; subst; now auto.

  injection H1; clear H1; intros; subst.
  apply H0 in H1; subst; now auto.
Qed.

Definition Imp (f1 f2: formula): formula := Or (Not f1) f2.

Lemma And_sem: forall {D: Dom mySig} {Itp: Interp D} (f1 f2: formula) (env: Env D) t,
  fm_sem env (And f1 f2) t <-> (fm_sem env f1 t /\ fm_sem env f2 t).
Proof.
  intros; reflexivity.
Qed.

Lemma Or_sem: forall {D: Dom mySig} {Itp: Interp D} (f1 f2: formula) (env: Env D) t,
  fm_sem env (Or f1 f2) t <-> (fm_sem env f1 t \/ fm_sem env f2 t).
Proof.
  intros; reflexivity.
Qed.

Lemma Imp_sem: forall {D: Dom mySig} {Itp: Interp D} (f1 f2: formula) (env: Env D) t,
  fm_sem env (Imp f1 f2) t <-> (fm_sem env f1 t -> fm_sem env f2 t).
Proof.
  intros.
  unfold Imp.
  rewrite Or_sem.
  rewrite Not_sem.
  tauto.
Qed.

Lemma Ex_sem: forall D (Itp: Interp D) env s v f t,
  fm_sem env (Ex s v f) t <-> exists (d: ssem s), fm_sem (add v d env) f t.
Proof.
  intros; reflexivity.
Qed.

Lemma All_sem: forall D (Itp: Interp D) env s v f t,
  fm_sem env (All s v f) t <-> forall (d: ssem s), fm_sem (add v d env) f t.
Proof.
  intros; reflexivity.
Qed.

Lemma Not_IAll: forall `(K:Finite) (sk: K->Sort) (vk:forall k, variable (sk k)) (f: formula),
  Not (IAll K sk vk f) = IEx K sk vk (Not f).
Proof.
  intros.
  unfold IAll, IEx.
  revert f; induction fin_set; simpl; intros; auto.
  rewrite IHs.
  reflexivity.
Qed.

Lemma Not_IEx: forall `(K:Finite) (sk: K->Sort) (vk:forall k, variable (sk k)) (f: formula),
  Not (IEx K sk vk f) = IAll K sk vk (Not f).
Proof.
  intros.
  unfold IAll, IEx.
  revert f; induction fin_set; simpl; intros; auto.
  rewrite IHs.
  reflexivity.
Qed.

Definition isSat f :=
  exists D, exists (Itp: Interp D), exists env, exists t, fm_sem env f t.

Definition equi_sat f1 f2 := isSat f1 <-> isSat f2.

Notation "f1 =s= f2" := (equi_sat f1 f2) (at level 50, no associativity).

Lemma isSat_And_elim: forall (f1 f2: formula),
  isSat (And f1 f2) -> isSat f1 /\ isSat f2.
Proof.
  intros.
  destruct H as [D [itp [env [t h]]]].
  apply And_sem in h; destruct h as [h1 h2].
  split.
  exists D; exists itp; exists env; exists t; apply h1.
  exists D; exists itp; exists env; exists t; apply h2.
Qed.

Fixpoint noEx f :=
  match f with
  | And f1 f2 | Or f1 f2 => noEx f1 /\ noEx f2
  | Ex s v f => False
  | All s v f => noEx f
  | F f | G f => noEx f
  | _ => True
  end.

Fixpoint noFO f :=
  match f with
  | And f1 f2 | Or f1 f2 => noFO f1 /\ noFO f2
  | Ex s v f | All s v f => False
  | F f | G f => noFO f
  | _ => True
  end.

Definition lt_noX l :=
  match l with
    PApp n p args => n = 0
  end.

Definition at_noX a :=
  match a with
  | Literal l => lt_noX l
  | NLiteral l => lt_noX l
  | _ => True
  end.

Fixpoint isFO f :=
  match f with
  | And f1 f2 | Or f1 f2 => isFO f1 /\ isFO f2
  | Ex s v f | All s v f => isFO f
  | F f | G f => False
  | Atom a => at_noX a
  | _ => True
  end.

Fixpoint isProp f :=
  match f with
  | And f1 f2 | Or f1 f2 => isProp f1 /\ isProp f2
  | Ex s v f | All s v f => False
  | F f | G f => False
  | _ => True
  end.

Lemma isFO_Not: forall f, isFO (Not f) <-> isFO f.
Proof.
  induction f; simpl; intros; try tauto.
  destruct a; simpl; tauto.
Qed.

Lemma isFO_And: forall f1 f2, isFO (And f1 f2) <-> isFO f1 /\ isFO f2.
Proof.
  intros.
  reflexivity.
Qed.

Lemma isFO_Or: forall f1 f2, isFO (Or f1 f2) <-> isFO f1 /\ isFO f2.
Proof.
  intros.
  reflexivity.
Qed.

Lemma isFO_IAnd: forall `(K: Finite) (fk: K -> formula), isFO (IAnd K fk) <-> (forall k, isFO (fk k)).
Proof.
  intros.
  unfold IAnd.
  assert ((forall k : K, isFO (fk k)) <-> (forall k : K, SV.set_In k fin_set -> isFO (fk k))).
    generalize (fin_all); intro.
    split; intros; now auto.
  rewrite H; clear H.
  induction fin_set; simpl; intros; auto.
  split; intros; tauto.
  rewrite IHs; clear IHs.
  split; intros; auto.
  destruct H0; try subst; try tauto.
  apply H; auto.
Qed.

Lemma isFO_IOr: forall `(K: Finite) (fk: K -> formula), isFO (IOr K fk) <-> (forall k, isFO (fk k)).
Proof.
  intros.
  unfold IOr.
  assert ((forall k : K, isFO (fk k)) <-> (forall k : K, SV.set_In k fin_set -> isFO (fk k))).
    generalize (fin_all); intro.
    split; intros; auto; tauto.
  setoid_rewrite H; clear H.
  induction fin_set; simpl; intros; auto.
  split; intros; tauto.
  rewrite IHs; clear IHs.
  split; intros; auto.
  destruct H0; try subst; try tauto.
  apply H; auto.
Qed.

Lemma isFO_Ex: forall s (v: variable s) f, isFO (Ex s v f) <-> isFO f.
Proof.
  intros.
  reflexivity.
Qed.

Lemma isFO_IEx: forall `(K:Finite) (sk: K->Sort) (vk:forall k, variable (sk k)) (f: formula),
  isFO (IEx K sk vk f) <-> isFO f.
Proof.
  intros.
  unfold IEx.
  induction fin_set; simpl; intros; auto; tauto.
Qed.

Lemma isFO_All: forall s (v: variable s) f, isFO (All s v f) <-> isFO f.
Proof.
  intros.
  reflexivity.
Qed.

Lemma isFO_Imp: forall f1 f2, isFO (Imp f1 f2) <-> isFO f1 /\ isFO f2.
Proof.
  intros.
  unfold Imp.
  rewrite isFO_Or.
  simpl.
  rewrite isFO_Not.
  reflexivity.
Qed.

Fixpoint isAll f :=
  match f with
  | All s v f => isAll f
  | _ => isProp f
  end.

Fixpoint isExAll f :=
  match f with
  | Ex s v f => isExAll f
  | f => isAll f
  end.

Definition VarSet := forall s, SV.set (variable s).

Definition vsIn {s} (v: variable s) (F: VarSet) := SV.set_In v (F s).

Definition vsSubset e1 e2 := forall s, SV.subset (T:=variable s) (e1 s) (e2 s).

Lemma vsSubset_refl : forall e, vsSubset e e.
Proof.
  repeat intro; auto.
Qed.

Lemma vsSubset_trans : forall {e1 e2 e3}, vsSubset e1 e2 -> vsSubset e2 e3 -> vsSubset e1 e3.
Proof.
  repeat intro; auto.
  apply H0.
  apply H.
  auto.
Qed.

Definition vsAdd {s} (v: variable s) (e: VarSet): VarSet :=
  fun s' =>
    match eq_dec s s' with
      left h => match h in _=s' return SV.set (variable s') with 
                  eq_refl => SV.add v (e s)
                end
    | right _ => e s'
    end.

Lemma vsAdd_l: forall {s} (v: variable s) (e: VarSet),
  SV.set_In v (vsAdd v e s).
Proof.
  unfold vsAdd; simpl; intros.
  destruct (eq_dec s s); try tauto.
  rewrite (proof_irrelevance _ e0 eq_refl).
  apply SV.InAdd_l.
Qed.

Lemma vsAdd_r: forall {s s'} (v: variable s) (e: VarSet) {w: variable s'},
  SV.set_In w (e s') -> SV.set_In w (vsAdd v e s').
Proof.
  intros.
  unfold vsAdd.
  destruct (eq_dec s s'); auto.
  subst s'.
  apply SV.InAdd_r; auto.
Qed.

Lemma vsAdd_elim: forall {s s'} (v: variable s) (e: VarSet) {w: variable s'},
  SV.set_In w (vsAdd v e s') -> isEq2 (U:=variable) s' w s v \/ SV.set_In w (e s').
Proof.
  intros.
  unfold vsAdd in H.
  unfold isEq2; simpl.
  destruct (eq_dec s s').
  subst s'.
  apply SV.InAdd in H; destruct H.
  subst v.
  left; auto.
  right; auto.
  right; auto.
Qed.

Lemma vsAdd_ne: forall {s s'} {v: variable s} {e: VarSet} {w: variable s'},
  SV.set_In w (vsAdd v e s') -> not (isEq2 (U:=variable) s' w s v) -> SV.set_In w (e s').
Proof.
  intros.
  apply vsAdd_elim in H.
  destruct H; tauto.
Qed.

Lemma vsAdd_ne2: forall {s s'} {v: variable s} {e: VarSet} {w: variable s'},
  SV.set_In w (vsAdd v e s') -> not (SV.set_In w (e s')) -> (isEq2 (U:=variable) s' w s v).
Proof.
  intros.
  apply vsAdd_elim in H.
  destruct H; tauto.
Qed.

Definition vsEmpty: VarSet := fun s => SV.empty _.

Definition vsSing {s} (v: variable s): VarSet :=
  fun s' =>
    match eq_dec s s' with
      left h => match h in _=s' return SV.set (variable s') with 
                  eq_refl => SV.sing _  v
                end
    | right _ => SV.empty _
    end.

Definition vsUnion (e1 e2: VarSet): VarSet :=
  fun s => SV.union (e1 s) (e2 s).

Lemma vsUnion_l: forall {s v} {e1 e2: VarSet},
  SV.set_In v (e1 s) -> SV.set_In v (vsUnion e1 e2 s).
Proof.
  intros.
  apply SV.InUnion_l; auto.
Qed.

Lemma vsUnion_r: forall {s v} {e1 e2: VarSet},
  SV.set_In v (e2 s) -> SV.set_In v (vsUnion e1 e2 s).
Proof.
  intros.
  apply SV.InUnion_r; auto.
Qed.

Lemma vsUnion_elim: forall {s v} {e1 e2: VarSet},
  SV.set_In v (vsUnion e1 e2 s) -> SV.set_In v (e1 s) \/ SV.set_In v (e2 s).
Proof.
  intros.
  apply SV.InUnion in H.
  destruct H; tauto.
Qed.

Definition vsInter (e1 e2: VarSet): VarSet :=
  fun s => SV.inter (e1 s) (e2 s).

Lemma vsInter_intro: forall {s v} {e1 e2: VarSet},
  SV.set_In v (e1 s) -> SV.set_In v (e2 s) -> SV.set_In v (vsInter e1 e2 s).
Proof.
  intros.
  apply SV.InInter; auto.
Qed.

Lemma vsInter_elim: forall {s v} {e1 e2: VarSet},
  SV.set_In v (vsInter e1 e2 s) -> SV.set_In v (e1 s) /\ SV.set_In v (e2 s).
Proof.
  intros; split.
  apply SV.InInter_l in H; auto.
  apply SV.InInter_r in H; auto.
Qed.

Definition vsGUnion `{K: Finite} (ek: K->VarSet): VarSet :=
  fun s => SV.GUnion (T1:=K) (T2:=variable s) fin_set fin_set (fun k _ => ek k s).

Lemma vsGUnion_intro `{K:Finite} {ek: K->VarSet}:
  forall s k, SV.subset (ek k s) (vsGUnion ek s).
Proof.
  repeat intro.
  unfold vsGUnion.
  apply SV.InCUnion_intro with (u:=k); simpl; auto.
  apply fin_all.
  apply fin_all.
Qed.

Lemma vsGUnion_elim `{K:Finite} {ek: K->VarSet} s (v: variable s):
  vsIn v (vsGUnion ek) -> exists k, vsIn v (ek k).
Proof.
  repeat intro.
  unfold vsGUnion in H.
  apply SV.InCUnion_elim in H; simpl; auto.
  destruct H as [k [h1 [h2 h3]]].
  exists k.
  apply h3.
  apply h2.
Qed.

Lemma vsSubsetUnion_elim_l: forall e1 e2 e,
  vsSubset (vsUnion e1 e2) e -> vsSubset e1 e.
Proof.
  repeat intro.
  apply (H s v); clear H; intros.
  apply vsUnion_l; auto.
Qed.

Lemma vsSubsetUnion_elim_r: forall e1 e2 e,
  vsSubset (vsUnion e1 e2) e -> vsSubset e2 e.
Proof.
  repeat intro.
  apply (H s v); clear H; intros.
  apply vsUnion_r; auto.
Qed.

Lemma vsSubsetGUnion_elim `{K:Finite} {ek: K->VarSet} e:
  vsSubset (vsGUnion ek) e -> forall k, vsSubset (ek k) e.
Proof.
  repeat intro.
  unfold vsGUnion.
  apply (H s v); clear H.
  apply SV.InCUnion_intro with (u:=k); simpl; auto.
  apply fin_all.
  apply fin_all.
Qed.

Definition vsRemove {s} (v: variable s) (e: VarSet): VarSet :=
  fun s' => match eq_dec s s' with
    left h =>
      match h in _=s' return SV.set (variable s') with
        eq_refl => SV.remove v (e s)
      end
  | right _ => e s'
  end.

Lemma vsInRemove_intro: forall s (v: variable s) (e: VarSet) s' (w: variable s'),
  vsIn w e -> not (isEq2 (U:=variable) s v s' w) -> vsIn w (vsRemove v e).
Proof.
  intros.
  unfold vsRemove, vsIn; simpl.
  destruct (eq_dec s s'); auto.
  subst s'.
  apply SV.InRemove.
  intro.
  subst w.
  apply H0; reflexivity.
  apply H.
Qed.

Lemma vsInRemove_elim: forall s (v: variable s) (e: VarSet) s' (w: variable s'),
  vsIn w (vsRemove v e) -> vsIn w e /\ not (isEq2 (U:=variable) s v s' w).
Proof.
  intros.
  unfold vsRemove, vsIn in H.
  destruct (eq_dec s s'); auto.
  subst s'.
  split.
  apply SV.InRemove_r in H; apply H.
  apply SV.InRemove_l in H.
  simpl; intro.
  apply H; clear H.
  apply inj_pair2_eq_dec in H0; try apply eq_dec.
  symmetry; apply H0.

  split.
  apply H.
  intro; apply n; clear n.
  injection H0; intro; auto.  
Qed.

Definition vsFinite (vs: VarSet): Finite :=
  PairFin Sort (fun s => asFinite (vs s)).

Definition tm_vars {s'} (tm: term s'): VarSet :=
  match tm with
    Var _ v => vsSing v
  | Cst _ s => vsEmpty
  end.

Definition lt_vars lt: VarSet :=
  match lt with
    PApp n p args => vsGUnion (fun i => tm_vars (args i))
  end.

Definition at_vars a : VarSet :=
  match a with
  | Literal a | NLiteral a => lt_vars a
  | Eq _ t1 t2 | NEq _ t1 t2 => vsUnion (tm_vars t1) (tm_vars t2)
  end.

Fixpoint fm_vars f : VarSet :=
  match f with
  | FTrue | FFalse => vsEmpty
  | Atom a => at_vars a
  | And f1 f2 | Or f1 f2 => vsUnion (fm_vars f1) (fm_vars f2)
  | Ex s v f | All s v f => fm_vars f
  | F f | G f => fm_vars f
  end.

Definition removeVars `{K: Finite} {sk: K->Sort} (vk: forall k, variable (sk k)) (e:VarSet): VarSet :=
  fun s => SV.Filter (fun (x:variable s) => NotDec (ExDecidable (ex_dec (fun k => isEq2 (U:=variable) s x (sk k) (vk k))))) (e s).

Definition vsVars `{K: Finite} {sk: K->Sort} (vk: forall k, variable (sk k)) : VarSet :=
  vsGUnion (fun k => vsSing (vk k)).

Lemma vsSing_intro: forall s v, SV.set_In v (vsSing v s).
Proof.
  intros.
  unfold vsSing.
  destruct (eq_dec s s); try tauto.
  rewrite (proof_irrelevance _ e eq_refl).
  left; auto.
Qed.

Lemma vsSing_elim: forall s (v: variable s) s' (w: variable s'), 
  SV.set_In v (vsSing w s) -> isEq2 (U:=variable) s v s' w.
Proof.
  intros.
  unfold vsSing in H.
  unfold isEq2; simpl.
  destruct (eq_dec s' s); try tauto; subst.
  destruct H; try tauto; subst; auto.
Qed.

Lemma vsSubsetSing: forall {s} {v: variable s} e, vsSubset (vsSing v) e -> SV.set_In v (e s).
Proof.
  intros.
  apply SV.subset_sing; repeat intro.
  generalize (H s v0); intro.
  apply H1.
  destruct H0.
  subst v0.
  apply vsSing_intro.
  destruct H0.
Qed.

Lemma vsVars_intro: forall `{K: Finite} {sk: K->Sort} (vk: forall k, variable (sk k)),
  forall k, SV.set_In (vk k) (vsVars vk (sk k)).
Proof.
  intros.
  apply SV.InCUnion_intro with (u:=k); auto.
  apply fin_all; simpl; intros; auto.
  apply fin_all.
  intro.
  apply vsSing_intro.
Qed.

Lemma vsVars_elim: forall `{K: Finite} {sk: K->Sort} (vk: forall k, variable (sk k)),
  forall s (v: variable s), SV.set_In v (vsVars vk s) -> exists k, isEq2 (U:=variable) (sk k) (vk k) s v.
Proof.
  intros.
  unfold vsVars in H.
  apply SV.InCUnion_elim in H.
  destruct H as [u [h1 [h2 h3]]].
  exists u; unfold isEq2; simpl.
  apply h3 in h2; clear h3.
  apply vsSing_elim in h2.
  symmetry; apply h2.
Qed.

Definition at_free a: VarSet :=
  match a with
  | Literal lt | NLiteral lt => lt_vars lt
  | Eq _ t1 t2 | NEq _ t1 t2 => vsUnion (tm_vars t1) (tm_vars t2)
  end.

Fixpoint free f: VarSet :=
  match f with
  | FTrue | FFalse => vsEmpty
  | Atom a => at_vars a
  | And f1 f2 | Or f1 f2 => vsUnion (free f1) (free f2)
  | Ex s v f | All s v f => vsRemove v (free f)
  | F f | G f => free f
  end.

  Lemma tm_sem_eq: forall (D: Dom mySig) (Itp: Interp D) s (tm: term s) (e1 e2: Env D),
      (forall s (v: variable s), SV.set_In v (tm_vars tm s) -> e1 s v = e2 s v) ->
        tm_sem (Itp:=Itp) e1 tm = tm_sem (Itp:=Itp) e2 tm.
  Proof.
    intros.
    destruct tm; simpl in *.
    apply H; clear H; auto.
    apply vsSing_intro.
    reflexivity.
  Qed.

  Lemma lt_free_X: forall l, lt_vars (ltX l) = lt_vars l.
  Proof.
    intro.
    destruct l; simpl in *; auto.
  Qed.
  
  Lemma at_free_X: forall a, at_vars (atX a) = at_vars a.
  Proof.
    intro.
    destruct a; simpl; intros; auto.
    apply lt_free_X.
    apply lt_free_X.
  Qed.
  
  Lemma free_X: forall f, free (X f) = free f.
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
  
  Lemma free_Ex: forall s (v: variable s) f, (free (Ex s v f)) = (vsRemove v (free f)).
  Proof.
    intros; reflexivity.
  Qed.
  
  Lemma free_And: forall f1 f2, free (And f1 f2) = (vsUnion (free f1) (free f2)).
  Proof.
    intros.
    reflexivity.
  Qed.

  Lemma free_Or: forall f1 f2,  free (Or f1 f2) = (vsUnion (free f1) (free f2)).
  Proof.
    intros; reflexivity.
  Qed.

  Lemma free_IAnd_sub: forall `(K: Finite) fk, vsSubset (free (IAnd K fk)) (vsGUnion (fun k => free (fk k))).
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
  
  Lemma free_IAnd_sup: forall `(K: Finite) fk, vsSubset (vsGUnion (fun k => free (fk k))) (free (IAnd K fk)).
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

  Lemma free_IOr_sub: forall `(K: Finite) fk, vsSubset (free (IOr K fk)) (vsGUnion (fun k => free (fk k))).
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
  
  Lemma free_IOr_sup: forall `(K: Finite) fk, vsSubset (vsGUnion (fun k => free (fk k))) (free (IOr K fk)).
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
  
  Ltac psemTac :=
    match goal with
      H:psem _ _ ?sa |- psem _ _ ?sa' => assert (sa' = sa) as ae;
          try (rewrite ae; assumption); (apply functional_extensionality_dep; intros)
    end.

  Lemma lt_sem_imp: forall (D: Dom mySig) (Itp: Interp D) (l: literal) t (e1 e2: Env D),
      (forall s (v: variable s), SV.set_In v (lt_vars l s) -> e1 s v = e2 s v) ->
        lt_sem (Itp:=Itp) e1 l t -> lt_sem (Itp:=Itp) e2 l t.
  Proof.
    intros.
    destruct l; simpl in *.
    psemTac.
    apply tm_sem_eq; intros.
    symmetry; apply H; clear H; intros; auto.
    apply (vsGUnion_intro s x); auto.
  Qed.

  Lemma lt_sem_equiv: forall (D: Dom mySig) (Itp: Interp D) (l: literal ) t (e1 e2: Env D),
      (forall s (v: variable s), SV.set_In v (lt_vars l s) -> e1 s v = e2 s v) ->
        lt_sem (Itp:=Itp) e1 l t <-> lt_sem (Itp:=Itp) e2 l t.
  Proof.
    intros; split.
    apply lt_sem_imp; auto.
    apply lt_sem_imp; intros.
    symmetry; apply H; auto. 
  Qed.
  
  Lemma at_sem_equiv: forall (D: Dom mySig) (Itp: Interp D) (a: atom ) t (e1 e2: Env  D),
      (forall s (v: variable s), SV.set_In v (at_free a s) -> e1 s v = e2 s v) ->
        at_sem (Itp:=Itp) e1 a t <-> at_sem (Itp:=Itp) e2 a t.
  Proof.
    intros.
    destruct a; simpl in *.
    apply lt_sem_equiv; auto.
    
    apply not_iff_compat.
    apply lt_sem_equiv; auto.

    rewrite tm_sem_eq with (e1:=e2) (e2:=e1); intros; auto.
    rewrite tm_sem_eq with (e1:=e2) (e2:=e1); intros; auto.
    reflexivity.
    symmetry; apply H; clear H.
    apply vsUnion_r; auto.
    symmetry; apply H; clear H.
    apply vsUnion_l; auto.
    
    apply not_iff_compat.
    rewrite tm_sem_eq with (e1:=e2) (e2:=e1); intros; auto.
    rewrite tm_sem_eq with (e1:=e2) (e2:=e1); intros; auto.
    reflexivity.
    symmetry; apply H; clear H.
    apply vsUnion_r; auto.
    symmetry; apply H; clear H.
    apply vsUnion_l; auto.
  Qed.

  Lemma fm_sem_equiv: forall (D: Dom mySig) (Itp: Interp D) (f: formula) t (e1 e2: Env D),
      (forall s (v: variable s), SV.set_In v (free f s) -> e1 s v = e2 s v) ->
        fm_sem (Itp:=Itp) e1 f t <-> fm_sem (Itp:=Itp) e2 f t.
  Proof.
    induction f; intros; auto.
  - reflexivity.
  - reflexivity.
  - apply at_sem_equiv; auto.
  - simpl.
    rewrite (IHf1 t e1 e2), (IHf2 t e1 e2); auto.
    reflexivity.
    intros; apply H; auto.
    apply vsUnion_r; apply H0.
    intros; apply H; auto.
    apply vsUnion_l; apply H0.
  - simpl.
    rewrite (IHf1 t e1 e2), (IHf2 t e1 e2); auto.
    reflexivity.
    intros; apply H; auto.
    apply vsUnion_r; apply H0.
    intros; apply H; auto.
    apply vsUnion_l; apply H0.
  - simpl.
    assert (forall d, fm_sem (add e d e1) f t <-> fm_sem (add e d e2) f t).
    intro.
    apply IHf; clear IHf; intros.
    unfold add.
    destruct (eq_dec s s0); auto.
    subst s0.
    destruct (eq_dec e v); auto.
    apply H; clear H; intros; auto.
    simpl.
    apply vsInRemove_intro; simpl; auto.
    intro; apply n; clear n.
    apply inj_pair2_eq_dec in H; try apply eq_dec; now auto.
    apply H; clear H; intros; auto.
    simpl.
    apply vsInRemove_intro; simpl; auto.
    intro; apply n; clear n.
    injection H; clear H; intros; now auto.

    setoid_rewrite H0; reflexivity.
  - simpl.
    assert (forall d, fm_sem (add e d e1) f t <-> fm_sem (add e d e2) f t).
    intro.
    apply IHf; clear IHf; intros.
    unfold add.
    destruct (eq_dec s s0); auto.
    subst s0.
    destruct (eq_dec e v); auto.
    apply H; clear H; intros; auto.
    simpl.
    apply vsInRemove_intro; simpl; auto.
    intro; apply n; clear n.
    apply inj_pair2_eq_dec in H; try apply eq_dec; now auto.
    apply H; clear H; intros; auto.
    simpl.
    apply vsInRemove_intro; simpl; auto.
    intro; apply n; clear n.
    injection H; clear H; intros; now auto.

    setoid_rewrite H0; reflexivity.
  - simpl.
    assert (forall t', (t'>=t /\ fm_sem e1 f t') <-> (t'>=t /\ fm_sem e2 f t')).
    intro.    
    setoid_rewrite (IHf t' e1 e2); auto.
    reflexivity.
    setoid_rewrite H0; reflexivity.
  - simpl.
    assert (forall t', (t'>=t -> fm_sem e1 f t') <-> (t'>=t -> fm_sem e2 f t')).
    intro.    
    setoid_rewrite (IHf t' e1 e2); auto.
    reflexivity.
    setoid_rewrite H0; reflexivity.
  Qed.

(*
env |- ex x1,..,xn. f <-> ex di. add xn dn ... (add x1 d1 env) |- f 
*)

(*
Definition addl {K:Finite} {D: Dom mySig} (sk: K-> Sort) (vk: forall k, variable (sk k)) (dk: forall k, ssem (sk k)) (env: Env D): Env D :=
  List.fold_left (fun e (k:K) => add (vk k) (dk k) e) fin_set env.
*)

Definition addl {D: Dom mySig} `(K: Finite) 
  (sk: K->Sort) (vk: forall k:K, variable (sk k)) (dk: forall k:K, ssem (sk k)) (env: Env D): Env D :=
  fun (s: Sort) (v: variable s) =>
    match last_dec (fun k => isEq2 (U:=variable) (sk k) (vk k) s v) with
      inleft (exist _ k h) =>
        match h in _=sv return ssem (projT1 sv) with
          eq_refl => dk k
        end
    | inright h => env s v
    end.

Definition addr {D: Dom mySig} `(K: Finite) 
  (sk: K->Sort) (vk: forall k:K, variable (sk k)) (dk: forall k:K, ssem (sk k)) (env: Env D): Env D :=
  fun (s: Sort) (v: variable s) =>
    match first_dec (fun k => isEq2 (U:=variable) (sk k) (vk k) s v) with
      inleft (exist _ k h) =>
        match h in _=sv return ssem (projT1 sv) with
          eq_refl => dk k
        end
    | inright h => env s v
    end.

Lemma fold_in: forall `{K:Finite} {D: Dom mySig} {sk: K-> Sort} (vk: forall k, variable (sk k)) (dk: forall k, ssem (sk k)) (env: Env D) l s (w: variable s) d,
  (exists k, List.In k l /\ isEq2 (U:=variable) _ w _ (vk k)) -> forall s' v,
    List.fold_left (fun (e : Env D) (k0 : K) => add (vk k0) (dk k0) e) l
      (add w d env) s' v =
    List.fold_left (fun (e : Env D) (k0 : K) => add (vk k0) (dk k0) e) l
      env s' v.
Proof.
  intros.
  revert env; induction l; simpl; intros; auto.
  destruct H as [k [H _]]; destruct H.
  
  destruct (@dc_dec (isEq2 (U:=variable) s w (sk a) (vk a))).
  simpl in d0; injection d0; clear d0; intros; subst s.
  apply inj_pair2_eq_dec in H0; try apply eq_dec; subst w.
  rewrite add_add_eq; now auto.
  
  assert (exists k : K, List.In k l /\ isEq2 (U:=variable) s w (sk k) (vk k)).
  destruct H as [k [h1 h2]].
  exists k; split; auto.
  destruct h1; try tauto.
  subst k; tauto.
  rewrite add_add_ne_swp; auto.
  simpl in *; intro; apply n; clear n.
  injection H1; clear H1; intros; subst s; auto.
Qed.

Lemma fold_add_ex: forall `{K:Finite} {D: Dom mySig} {sk: K-> Sort} (vk: forall k, variable (sk k)) (dk: forall k, ssem (sk k)) (env: Env D) l s (w: variable s),
  (exists k, SV.set_In k l /\ isEq2 (U:=variable) _ (vk k) _ w) -> forall d1 d2 s' v,
  List.fold_left (fun (e : Env D) (k0 : K) => add (vk k0) (dk k0) e) l
    (add w d1 env) s' v =
  List.fold_left (fun (e : Env D) (k0 : K) => add (vk k0) (dk k0) e) l
    (add w d2 env) s' v.
Proof.
  intros.
  revert env d1 d2; induction l; simpl; intros; auto.
  destruct H as [k [h1 h2]]; destruct h1.
  
  destruct H as [k [h1 h2]].
  destruct h1.
  subst k.
  change  (
    List.fold_left (fun (e : Env D) (k0 : K) => add (vk k0) (dk k0) e) (a::l)
      (add w d1 env) s' v =
    List.fold_left (fun (e : Env D) (k0 : K) => add (vk k0) (dk k0) e) (a::l)
      (add w d2 env) s' v).
  
  rewrite fold_in.
  rewrite fold_in; auto.
  
  exists a; split; simpl; now auto.
  exists a; split; simpl; now auto.

  destruct (@dc_dec (isEq2 (U:=variable) _ w _ (vk a))).
  injection d; intros; subst s.
  apply inj_pair2_eq_dec in d; try apply eq_dec; subst w.
  do 2 rewrite add_add_eq; now auto.  

  rewrite add_add_ne_swp with (v2:=w); auto.
  rewrite add_add_ne_swp with (v2:=w); auto.
  apply IHl.
  exists k; split; now auto.
  simpl in *; intro; apply n; clear n.
  injection H0; clear H0; intros; subst s; auto.
  simpl in *; intro; apply n; clear n.
  injection H0; clear H0; intros; subst s; auto.
Qed.

Lemma fold_add_nex: forall `(K: EqDec) {D: Dom mySig} {sk: K-> Sort} (vk: forall k, variable (sk k)) (dk dk': forall k, ssem (sk k)) (env: Env D) l s (w: variable s) (a:K),
  (forall k, List.In k l -> ~ (isEq2 (U:=variable) (sk k) (vk k) (sk a) (vk a))) ->
  (forall k, a <> k -> dk' k = dk k) ->
  List.fold_left (fun e k => add (vk k) (dk' k) e) l env s w =
  List.fold_left (fun e k => add (vk k) (dk k) e) l env s w.
Proof.
  intros.
  revert env; induction l; simpl; intros; auto.
  
  rewrite (H0 a0).
  apply IHl; clear IHl; intros; auto.
  apply H.
  right; now auto.
  intro; subst a0.
  apply (H a); simpl; auto.
Qed.

Lemma IEx_sem: forall D (Itp: Interp D) env `(K: Finite) sk vk f t,
    fm_sem env (IEx K sk vk f) t
  <-> exists (dk: forall k, ssem (sk k)), fm_sem (addl K sk vk dk env) f t.
Proof.
  intros.
  unfold addl, IEx.
  unfold last_dec.
  revert env; induction fin_set; simpl; intros.
  
  split; intro.
  
  exists (fun k => neDom (sk k)); now auto.
  destruct H as [dk H].
  apply H.
  
  split; intro.
  destruct H as [d H].
  (***)
  
  apply IHs in H; clear IHs.
  destruct H as [dk H].
  
  destruct (SV.set_In_dec a s).
  exists dk.
  revert H; apply fm_sem_equiv; intros; clear H.
  destruct (SV.last_dec (fun k : K => isEq2 (sk k) (vk k) s0 v) s); auto.
  destruct s1 as [k [h1 h2]]; simpl; reflexivity.
  destruct ( dec.isEq2_obligation_1 _ Sort _ (fun x : Sort => variable x)
        (sk a) (vk a) s0 v); auto.
  unfold and_ind.
  injection e; intros; subst s0.
  apply inj_pair2_eq_dec in H; try apply eq_dec; subst v.
  exfalso; apply (n a i eq_refl).
  rewrite add_ne2; now auto.
    
  set (dk' := fun k => 
    match eq_dec a k return ssem (sk k) 
    with left e =>
      match e in _=k return ssem (sk k) with
        eq_refl => d
      end
      | _ => dk k
      end).
  exists dk'.
  
  revert H; apply fm_sem_equiv; intros; clear H.
  destruct (SV.last_dec (fun k : K => isEq2 (sk k) (vk k) s0 v) s); auto.
  destruct s1 as [k [h1 h2]]; simpl.
  
  injection h2; intros; subst s0.
  apply inj_pair2_eq_dec in H; try apply eq_dec; subst v.
  rewrite (proof_irrelevance _ _ eq_refl).
  unfold dk'.
  destruct (eq_dec a k); auto.
  subst k; tauto.
  
  destruct (dec.isEq2_obligation_1 _ Sort _ (fun x : Sort => variable x) 
        (sk a) (vk a) s0 v); auto.
  injection e; intros; subst s0.
  destruct (eq_dec (sk a) (sk a)); try tauto.
  unfold and_ind.
  apply inj_pair2_eq_dec in H; try apply eq_dec; subst v.
  rewrite (proof_irrelevance _ e eq_refl).
  rewrite add_eq.
  unfold dk'.
  destruct (eq_dec a a); try tauto.
  rewrite (proof_irrelevance _ e1 eq_refl); now auto.
  rewrite add_ne2; now auto.
  
  destruct H as [dk H].
  exists (dk a).
  apply IHs; clear IHs.
  exists dk.
  unfold and_ind in *.
  revert H; apply fm_sem_equiv; intros; auto.
  destruct (SV.last_dec (fun k : K => isEq2 (sk k) (vk k) s0 v) s); auto.
  destruct s1 as [k [h1 h2]]; simpl in *.
  reflexivity.
  destruct (dec.isEq2_obligation_1 _ Sort _ (fun x : Sort => variable x) 
        (sk a) (vk a) s0 v); auto.
  injection e; intros; subst s0.
  apply inj_pair2_eq_dec in H0; try apply eq_dec; subst v.
  rewrite add_eq.
  rewrite (proof_irrelevance _ _ eq_refl); now auto.  
  rewrite add_ne2; auto.
Qed.

Lemma IAll_sem: forall D (Itp: Interp D) env `(K: Finite) sk vk f t,
  fm_sem env (IAll K sk vk f) t <-> forall (dk: forall k, ssem (sk k)), fm_sem (addl K sk vk dk env) f t.
Proof.
  intros.
  assert (not (fm_sem env (IAll K sk vk f) t) <->
           (exists dk : forall k : K, ssem (sk k), not (fm_sem (addl K sk vk dk env) f t))).
  rewrite <-Not_sem.
  setoid_rewrite <-Not_sem.
  rewrite Not_IAll.
  rewrite IEx_sem; now auto.
  assert (not (fm_sem env (IAll K sk vk f) t) <->
           not (forall dk : forall k : K, ssem (sk k), (fm_sem (addl K sk vk dk env) f t))).
  rewrite H; clear H.
  split; intro.
  intro.
  destruct H as [dk H]; apply H; apply H0; now auto.
  apply not_all_ex_not in H; apply H.
  clear H.
  split; intros; try tauto.
  apply proj2 in H0.
  apply NNPP; intro; revert H; apply H0; clear H0; intro.
  apply (H1 (H dk)).
Qed.

End FO.

