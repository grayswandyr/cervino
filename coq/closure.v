
Require Import Eqdep_dec.
Require Import Fin.

Require Import foltl.
Require Import dec.
Require Import finite.
Require Import set.
Require Import varset.
Require Import vars.
Require Import fosem.

Section Closure.
  Context {Ts: Type} {Tv: Ts->Type} {Tc: Ts->Type} {Tp: Type}.
  Variable Sg: @Sig Ts Tv Tc Tp.
  Variable D: Dom Sg.
  Variable s: Sort.
  Variable itp: Interp D.
  Variable BinItp: ssem s -> ssem s -> Prop.

  Inductive Closure: ssem s -> ssem s -> Prop :=
    Cl0: forall d1 d2, d1=d2 -> Closure d1 d2
  | ClS: forall d1 d2 d3, Closure d1 d2 -> BinItp d2 d3 -> Closure d1 d3.

  Inductive AuxVars := X1 | X2 | Z1 | Z2.
  Program Definition AuxVarsDec: @EqDec AuxVars := {| eq_dec := _ |}.
  Next Obligation.
    repeat intro.
    decide equality.
  Qed.
  Definition AuxVarsSet: SV.set AuxVarsDec := (cons X1 (cons X2 (cons Z1 (cons Z2 nil)))).
  Program Definition AuxVarsFin: Finite := {| fin_set := AuxVarsSet |}.
  Next Obligation.
    destruct x; tauto.
  Qed.
    
  Inductive BinPreds := Succ | Succ'.
  Program Definition BinPredsDec: @EqDec BinPreds := {| eq_dec := _ |}.
  Next Obligation.
    repeat intro.
    decide equality.
  Qed.
  Definition BinPredsSet: SV.set BinPredsDec := (cons Succ (cons Succ' nil)).
  Program Definition BinPredsFin: Finite := {| fin_set := BinPredsSet |}.
  Next Obligation.
    destruct x; tauto.
  Qed.
  
  Definition epredicate := (SumDec BinPredsDec predicate).

  Definition epr_arity (p': epredicate) := match p' with inl p => 2 | inr p => pr_arity p end.
  Definition epr_args p': Fin.t (epr_arity p') -> _ :=
    match p' return Fin.t (epr_arity p') -> _ with 
      inl p => fun i => s
    | inr p => fun i => pr_args p i 
    end.
  
  Definition srcSg : Sig := {|
    Sort := Sort (Sig:=Sg);
    constant := constant;
    variable := variable;
    predicate := epredicate;
    pr_arity := epr_arity;
    pr_args := epr_args;
  |}.

  Definition dstVarT s' (e: {s'=s}+{s'<>s}): Type := if e then AuxVars + (variable s') else variable s'.

  Definition dstSg : Sig := {|
    Sort := Sort (Sig:=Sg);
    variable := fun s' => if eq_dec s' s as e return @VariableT (dstVarT s' e) then (SumFin AuxVarsFin (variable s')) else variable s';
    constant := constant;
    predicate := epredicate;
    pr_arity := epr_arity;
    pr_args := epr_args;
  |}.
  
  Program Definition srcD: Dom srcSg := {| ssem := ssem (Dom:=D); neDom := neDom (Dom:=D) |}.

  Program Definition dstD: Dom dstSg := {| ssem := ssem (Dom:=D); neDom := neDom (Dom:=D) |}.
  
  Program Definition srcItp : Interp srcD := {|
    csem s c := csem (Interp:=itp) c;
    psem p t := match (p: predicate (Sig:=srcSg)) as p0 return 
      (forall i : Fin.t (epr_arity p0), ssem (epr_args p0 i)) -> Prop with 
      inl np =>
        match np return (Fin.t 2 -> ssem s) -> _ with 
          Succ => fun a => BinItp (a F1) (a (FS F1))
        | Succ' => fun a => Closure (a F1) (a (FS F1))
        end
    | inr p => psem p t
    end
  |}.

  Program Definition dstItp : Interp dstD := {|
    csem s c := csem (Interp:=itp) c;
    psem p t := match (p: predicate (Sig:=dstSg)) as p0 return 
      (forall i : Fin.t (epr_arity p0), ssem (epr_args p0 i)) -> Prop with 
      inl np =>
        match np return (Fin.t 2 -> ssem s) -> _ with 
          Succ => fun a => BinItp (a F1) (a (FS F1))
        | Succ' => fun a => Closure (a F1) (a (FS F1))
        end
    | inr p => psem p t
    end
  |}.
  
  Definition at_Succ (x1 x2: term dstSg s): formula dstSg :=
    Atom dstSg (Literal dstSg
     (PApp dstSg 0 (inl Succ)
        (fun i : Fin.t 2 => match i with F1 => x1 | _ => x2 end))).

  Definition at_Succ' (x1 x2: term dstSg s): formula dstSg :=
    Atom dstSg (Literal dstSg
     (PApp dstSg 0 (inl Succ')
        (fun i : Fin.t 2 => match i with F1 => x1 | _ => x2 end))).

  Definition var (v: AuxVars): variable (Sig:=dstSg) s.
  Proof.
    simpl.
    destruct (eq_dec s s).
    apply (inl v).
    destruct (n eq_refl).
  Defined.
  
  Lemma var_inj: forall v1 v2, var v1 = var v2 -> v1 = v2.
  Proof.
    unfold var; intros.
    simpl in *.
    destruct (eq_dec s s).
    injection H; intros; auto.
    exfalso; clear H; tauto.
  Qed.
  
  Definition unary (P: formula dstSg) (x: variable (Sig:=dstSg) s) :=
    vsIn dstSg x (free dstSg P) /\ 
    vsSubset dstSg (free dstSg P) (vsSing dstSg x).
    
  Definition subst (x y: variable (Sig:=dstSg) s) (P: formula dstSg) :=
    Ex dstSg s x (And dstSg (Atom dstSg (Eq dstSg s (Var dstSg s y) (Var dstSg s x))) P).

  Notation "'[' x ':=' y ']'" := (subst x y).
  
  Lemma subst_sem:
    forall (f: formula dstSg) (itp: Interp dstD) (env1 env2: Env dstSg dstD) t (x y: variable (Sig:=dstSg) s), 
    unary f x -> env1 s x = env2 s y -> x <> y ->
      fm_sem dstSg (Itp:=itp) env1 f t <-> fm_sem dstSg (Itp:=itp) env2 ([x:=y] f) t.
  Proof.
    intros.
    unfold subst.
    rewrite Ex_sem.
    setoid_rewrite And_sem.
    simpl.
    setoid_rewrite add_eq.
    split; intros.
    exists (env2 s y); split; auto.
    rewrite add_upd; auto.
    rewrite <-H0.
    revert H2; apply fm_sem_equiv; intros.
    apply H in H2.
    apply (vsSing_elim dstSg) in H2.
    injection H2; intros; subst s0.
    apply inj_pair2_eq_dec in H3; try apply eq_dec.
    subst v.
    rewrite add_eq; reflexivity.
    
    destruct H2 as [d [h1 h2]].
    revert h2; apply fm_sem_equiv; intros.
    apply H in H2.
    apply (vsSing_elim dstSg) in H2.
    injection H2; intros; subst s0.
    apply inj_pair2_eq_dec in H3; try apply eq_dec.
    subst v.
    rewrite add_eq.
    rewrite add_ne in h1; auto.
    subst d; auto.
  Qed.
  
  Definition Propagates (P: formula dstSg) (fp: unary P (var X1)) :=
   All dstSg _ (var X1) (All dstSg _ (var X2) (G dstSg
    (Imp dstSg (And dstSg P (at_Succ (Var dstSg s (var X1)) (Var dstSg s (var X2))))
          (F dstSg ([var X1 := var X2] P ))))).

  Definition AbsClosure (P: formula dstSg) (fp: unary P (var X1)) :=
    All dstSg _ (var Z1) (Imp dstSg  (And dstSg ([var X1 := var Z1] P ) (Propagates P fp))
                       (All dstSg _ (var Z2) (Imp dstSg (at_Succ' (Var dstSg s (var Z1)) (Var dstSg s (var Z2))) (F dstSg ([var X1 := var Z2] P ))))).

  Theorem AbsClosureOK: forall (P: formula dstSg) (fp: unary P (var X1)),
    forall (v: variable (Sig:=dstSg) s), 
      forall (env: Env dstSg dstD) t, fm_sem (Itp:=dstItp) dstSg env (AbsClosure P fp) t.
  Proof.
    intros.
    unfold AbsClosure.
    apply All_sem; intro.
    apply Imp_sem; intro.
    apply And_sem in H; destruct H.
    apply All_sem; intro.
    apply Imp_sem; intro.
    simpl in H1.
    assert ((add dstSg (var Z2) d0 (add dstSg (var Z1) d env) s
          (var Z1)) = d).
      rewrite add_ne.
      apply add_eq.
      intro.
      apply var_inj in H2; discriminate.
    assert ((add dstSg (var Z2) d0 (add dstSg (var Z1) d env) s
          (var Z2)) = d0).
      apply add_eq.
    rewrite H2,H3 in H1; clear H2 H3.
    
    induction H1.
    subst d2.
    exists t; split; auto.
    clear H0.
    simpl in d1.
    rewrite <-subst_sem with (env1:=add dstSg (var X1) (d1: ssem (Dom:=dstD) s) env) in H; auto.
    rewrite <-subst_sem with (env1:=add dstSg (var X1) (d1: ssem (Dom:=dstD) s) env); auto.
    do 2 rewrite add_eq; now auto.
    intro.
    apply var_inj in H0; discriminate.
    do 2 rewrite add_eq; now auto.
    intro.
    apply var_inj in H0; discriminate.
        
    generalize (IHClosure H H0); clear IHClosure H; intro H.
    destruct H as [t' [h1 h2]].
    unfold Propagates in H0.
    rewrite All_sem in H0; specialize H0 with d2.
    rewrite All_sem in H0; specialize H0 with d3.
    rewrite G_sem in H0.
    generalize (H0 t' h1); clear H0; intro H0.
    rewrite Imp_sem in H0.
    match goal with H0: ?p -> _ |- _ => assert p as h; [clear H0 | apply H0 in h; clear H0] end.
    apply And_sem; split.
    rewrite <-subst_sem with (env1:=add dstSg (var X1) (d2: ssem (Dom:=dstD) s) env) in h2; auto.
    revert h2; apply fm_sem_equiv; intros; auto.
    apply fp in H; apply (vsSing_elim dstSg) in H.
    injection H; intros; subst s0.
    apply inj_pair2_eq_dec in H0; try apply eq_dec; subst v0.
    repeat rewrite add_eq.
    rewrite add_ne; try (intro diff; apply var_inj in diff; discriminate).
    rewrite add_eq; now auto.
    repeat rewrite add_eq; now auto.
    intro diff; apply var_inj in diff; discriminate.

    simpl.
    rewrite add_eq.
    rewrite add_ne; try (intro diff; apply var_inj in diff; discriminate).
    rewrite add_eq.
    apply H2.

    rewrite F_sem in h; destruct h as [t'' [h h']].
    exists t''; split.
    apply Arith.Le.le_trans with t'; now auto.
    rewrite <-subst_sem with (env1:=add dstSg (var X1) (d3: ssem (Dom:=dstD) s) env) in h'; auto.
    rewrite <-subst_sem with (env1:=add dstSg (var X1) (d3: ssem (Dom:=dstD) s) env); auto.
    repeat rewrite add_eq; auto.
    intro diff; apply var_inj in diff; discriminate.
    repeat rewrite add_eq; auto.
    intro diff; apply var_inj in diff; discriminate.
  Qed.
End Closure.

  
