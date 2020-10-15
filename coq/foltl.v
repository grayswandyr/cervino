
Require Import Eqdep_dec.
Require Import Coq.Logic.FunctionalExtensionality.
Import EqNotations.
Require Import Coq.Logic.JMeq.
Require Import ProofIrrelevance.
Require Import Classical.
Require Import Fin.

Require Import dec.
Require Import finite.
Require Import set.

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


Class Sig {Ts: Type} {Tv: Ts->Type} {Tc: Ts->Type} {Tp} := {
  Sort: @SortT Ts;
  variable: forall (s:Sort), @VariableT (Tv s);
  constant: forall (s:Sort), @ConstantT (Tc s);
  predicate: @PredicateT Tp;
  pr_arity: predicate -> nat;
  pr_args: forall p, Fin.t (pr_arity p) -> Sort;
}.

Class Dom {Ts Tv Tc Tp} (Sg: @Sig Ts Tv Tc Tp) := {
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
  Context {Ts: Type} {Tv: Ts->Type} {Tc: Ts->Type} {Tp: Type}.
  Variable mySig: @Sig Ts Tv Tc Tp.
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

Definition tm_sem {D: Dom mySig} {Itp: Interp D} {s} (env: Env D) (tm: term s): ssem s :=
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
  destruct (all_dec (F:=uptoFinite (pr_arity p)) (fun i => isEq (T:=tmDec (pr_args p i)) (t i) (t0 i))).
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

Definition lt_sem {D: Dom mySig} {Itp: Interp D} (env: Env D) (lt: literal) (t:nat): Prop :=
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

Definition tm_subst {s s'} (x : variable s) (tm: term s) (t: term s'): term s' :=
  match t with
    Var _ y => 
      match eq_dec s' s return term s' with
        left e =>
          match e in _ = s return variable s -> term s -> term s' with
            eq_refl => fun x tm => if eq_dec x y then tm else Var _ y
          end x tm
      | right _ => t
      end
  | Cst _ c => Cst _ c
  end.

Definition lt_subst {s} (v : variable s) (tm: term s) (l: literal) :=
  match l with
    PApp x r args => PApp x r (fun i => tm_subst v tm (args i))
  end.

Definition at_subst {s} (x : variable s) (tm: term s) (a: atom) :=
  match a with
    Literal l => Literal (lt_subst x tm l)
  | NLiteral l => NLiteral (lt_subst x tm l)
  | Eq s' t1 t2 => Eq s' (tm_subst x tm t1) (tm_subst x tm t2)
  | NEq s' t1 t2  => NEq s' (tm_subst x tm t1) (tm_subst x tm t2)
  end.

Definition esubst {s} (x : variable s) (tm: term s) (P: formula) :=
  Ex s x (And (Atom (Eq s (Var s x) tm)) P).

Definition asubst {s} (x : variable s) (tm: term s) (P: formula) :=
  All s x (Imp (Atom (Eq s (Var s x) tm)) P).

Fixpoint subst {s} (x: variable s) (tm: term s) (f: formula) :=
  match f with
  | FTrue => FTrue
  | FFalse => FFalse
  | Atom a => Atom (at_subst x tm a)
  | And f1 f2 => And (subst x tm f1) (subst x tm f2)
  | Or f1 f2 => Or (subst x tm f1) (subst x tm f2)
  | Ex s' w f' => esubst x tm f
  | All s' w f' => asubst x tm f
  | F f => F (subst x tm f)
  | G f => G (subst x tm f)
  end.

Notation "'[' x ':=' y ']'" := (subst x y).  

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

Lemma isProp_dec f : {isProp f}+{not (isProp f)}.
Proof.
  induction f; simpl; intros; try (left; now auto); try (right; tauto).
  destruct IHf1; [idtac | right; tauto].
  destruct IHf2; [left | right]; tauto.

  destruct IHf1; [idtac | right; tauto].
  destruct IHf2; [left | right]; tauto.
Defined.

Lemma isAll_dec f : {isAll f}+{not (isAll f)}.
Proof.
  induction f; simpl; intros; try (left; now auto); try (right; tauto); auto.
  destruct (isProp_dec f1); [idtac | right; tauto].
  destruct (isProp_dec f2); [left | right]; tauto.

  destruct (isProp_dec f1); [idtac | right; tauto].
  destruct (isProp_dec f2); [left | right]; tauto.
Defined.

Lemma isExAll_dec f : {isExAll f}+{not (isExAll f)}.
Proof.
  induction f; simpl; intros; try (left; now auto); try (right; tauto); auto.
  destruct (isProp_dec f1); [idtac | right; tauto].
  destruct (isProp_dec f2); [left | right]; tauto.

  destruct (isProp_dec f1); [idtac | right; tauto].
  destruct (isProp_dec f2); [left | right]; tauto.

  apply (isAll_dec f).  
Defined.

End FO.

