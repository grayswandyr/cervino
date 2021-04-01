Require Import Arith.
Require Import Eqdep_dec.
Require Import Fin.
Import EqNotations.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.

Require Import foltl.
Require Import dec.
Require Import finite.
Require Import set.
Require Import varset.
Require Import vars.
Require Import fosem.

Ltac psemTac :=
    match goal with
      H:psem _ _ ?sa |- psem _ _ ?sa' => assert (sa' = sa) as ae;
          try (rewrite ae; assumption); (apply functional_extensionality_dep; intros)
    end.
    

Inductive Closure {T} (R: T -> T -> Prop): T -> T -> Prop :=
  Cl0: forall d1 d2, d1=d2 -> Closure R d1 d2
| ClS: forall d1 d2 d3, Closure R d1 d2 -> R d2 d3 -> Closure R d1 d3.

Section Closure.
  Context {Ts: Type} {Tv: Ts->Type} {Tc: Ts->Type} {Tp: Type}.
  Variable srcSg: @Sig Ts Tv Tc Tp.
  Variable D: Dom srcSg.
  Variable s: Sort.
  Variable srcItp: Interp D.
  Variable Succ: predicate.
  Variable Succ': predicate.
  Variable SuccAr: pr_arity Succ = 2.
  Variable SuccAr': pr_arity Succ' = 2.
  Variable SuccArgs: forall i, pr_args Succ i = s.
  Variable SuccArgs': forall i, pr_args Succ' i = s.
  (*Variable Succ_stb: forall t1 t2 a, psem Succ t1 a <-> psem Succ t2 a. *)
  
  Definition SuccSem t (x y: ssem s) :=
    psem Succ t (fun i => match i with F1 => rew [ssem] (eq_sym (SuccArgs i)) in x | _ => rew [ssem] (eq_sym (SuccArgs i)) in y end).

  Definition SuccSem' t (x y: ssem s) :=
    psem Succ' t (fun i => match i with F1 => rew [ssem] (eq_sym (SuccArgs' i)) in x | _ => rew [ssem] (eq_sym (SuccArgs' i)) in y end).
  
  Definition ClosureSem := forall t x y, SuccSem' t x y <-> Closure (SuccSem t) x y.
  
  Variable SuccSem_cls': ClosureSem.
  
  Inductive AuxVars := X1 | X2 | Z1 | Z2.
  Program Definition AuxVarsDec: @EqDec AuxVars := {| eq_dec := _ |}.
  Next Obligation.
    repeat intro.
    decide equality.
  Defined.
  Definition AuxVarsSet: SV.set AuxVarsDec := (cons X1 (cons X2 (cons Z1 (cons Z2 nil)))).
  Program Definition AuxVarsFin: Finite := {| fin_set := AuxVarsSet |}.
  Next Obligation.
    destruct x; tauto.
  Qed.
  
  Definition dstVarT s' (e: {s'=s}+{s'<>s}): Type := if e then AuxVars + (variable s') else variable s'.

  Definition dstSg : Sig := {|
    Sort := Sort (Sig:=srcSg);
    variable := fun s' => if eq_dec s' s as e return @VariableT (dstVarT s' e) then (SumFin AuxVarsFin (variable s')) else variable s';
    constant := constant;
    predicate := predicate;
    pr_arity := pr_arity;
    pr_args := pr_args;
  |}.
  
  Program Definition dstD: Dom dstSg := {| ssem := ssem (Dom:=D); neDom := neDom (Dom:=D) |}.
  
  Program Definition dstItp : Interp dstD := {| csem s c := csem (Interp:=srcItp) c; psem := psem (Interp:=srcItp) |}.

  Definition tfrVar {s'} (v: variable (Sig:=srcSg) s') : variable (Sig:=dstSg) s'.
  Proof.
    unfold variable; simpl.
    destruct (eq_dec s' s); simpl.
    exact (inr v).
    exact v.
  Defined.
  
  Lemma tfrVar_inj: forall {s1 s2} (v1: variable (Sig:=srcSg) s1) (v2: variable (Sig:=srcSg) s2),
    @isEq2 _ Sort _ (variable (Sig:=dstSg)) s1 (tfrVar v1) s2 (tfrVar v2) -> @isEq2 _ Sort _ (variable (Sig:=srcSg)) s1 v1 s2 v2.
  Proof.
    intros.
    injection H; clear H; intros; subst; auto.
    apply inj_pair2_eq_dec in H; try apply eq_dec.
    unfold tfrVar in H.
    destruct (eq_dec s2 s); subst; auto.
    injection H; intros; subst; auto.
    constructor.
    constructor.
  Qed.
  
  Definition tfrTerm {s} (tm: term srcSg s): term dstSg s :=
  match tm return term dstSg s with
    Cst _ _ c => Cst dstSg _ c
  | Var _ _ v => Var dstSg _ (tfrVar v)
  end.
  
  Definition tfrLiteral (l: literal srcSg): literal dstSg :=
  match l with
    PApp _ x r args => PApp dstSg x r (fun i => tfrTerm (args i))
  end.
  
  Definition tfrAtom (a: atom srcSg): atom dstSg :=
  match a with
    Literal _ l => Literal dstSg (tfrLiteral l)
  | NLiteral _ l => NLiteral dstSg (tfrLiteral l)
  | Eq _ s t1 t2 => Eq dstSg s (tfrTerm t1) (tfrTerm t2)
  | NEq _ s t1 t2 => NEq dstSg s (tfrTerm t1) (tfrTerm t2)
  end.
  
  Fixpoint tfrFormula (f: formula srcSg): formula dstSg :=
  match f with
  | FTrue _ => FTrue dstSg
  | FFalse _ => FFalse dstSg
  | Atom _ a => Atom dstSg (tfrAtom a)
  | And _ f1 f2 => And dstSg (tfrFormula f1) (tfrFormula f2)
  | Or _ f1 f2 => Or dstSg (tfrFormula f1) (tfrFormula f2)
  | Ex _ s v f => Ex dstSg s (tfrVar v) (tfrFormula f)
  | All _ s v f => All dstSg s (tfrVar v) (tfrFormula f)
  | F _ f => F dstSg (tfrFormula f)
  | G _ f => G dstSg (tfrFormula f)
  end.

  Definition tfrEnv (env: Env srcSg D) : Env dstSg dstD.
  Proof.
    intro s'.
    unfold variable; simpl.
    unfold dstVarT in *; simpl.
    destruct (@eq_dec Ts (@Sort Ts Tv Tc Tp srcSg) s' s); intro v.
    destruct v.
    exact (neDom _).
    exact (env _ e0).
    exact (env _ v).
  Defined.

  Lemma tfr_env_sem: forall env s' v, env s' v = tfrEnv env s' (tfrVar v).
  Proof.
    unfold tfrEnv, tfrVar; simpl; intros.
    destruct (eq_dec s' s); auto.
  Qed.

  Lemma tfr_addEnv: forall env s' (v: variable (Sig:=srcSg) s') d,
    add dstSg (tfrVar v) d (tfrEnv env) = tfrEnv (add srcSg v d env).
  Proof.
    intros.
    apply functional_extensionality_dep; intro s''.
    apply functional_extensionality; intro w.
    destruct (eq_dec s'' s').
    subst.
    destruct (eq_dec (tfrVar v) w); auto.
    subst w.
    rewrite <-tfr_env_sem.
    do 2 rewrite add_eq; now auto.
    rewrite add_ne.
    revert w n; unfold tfrEnv, tfrVar, add; simpl.
    destruct (eq_dec s' s); simpl; intros; auto.
    subst s'.
    destruct w; simpl; auto.
    destruct (eq_dec s s); try tauto.
    rewrite (proof_irrelevance _ e0 eq_refl).
    destruct (eq_dec v e); auto.
    subst v; tauto.
    destruct (eq_dec s' s'); try tauto.
    rewrite (proof_irrelevance _ e eq_refl).
    destruct (eq_dec v w); auto; tauto.
    apply n.
    
    rewrite add_ne2.
    revert w n; unfold tfrEnv, tfrVar, dstVarT, add; simpl.
    destruct (@eq_dec Ts (@Sort Ts Tv Tc Tp srcSg) s'' s); simpl; intros; auto.
    destruct w; simpl; auto.
    subst s''.
    destruct (eq_dec s' s); try (subst s'; tauto); auto.
    destruct (eq_dec s' s''); try (subst s''; tauto); auto.
    intro; apply n.
    injection H; intros; auto.
  Qed.

  Lemma tfr_tm_sem: forall env s' (tm: term srcSg s'), tm_sem srcSg (Itp:=srcItp) env tm = tm_sem dstSg (Itp:=dstItp) (tfrEnv env) (tfrTerm tm).
  Proof.
    intros.
    destruct tm; simpl; auto.
    apply tfr_env_sem.
  Qed.
  
  Lemma tfr_lt_sem: forall env l t, lt_sem srcSg (Itp:=srcItp) env l t <-> lt_sem dstSg (Itp:=dstItp) (tfrEnv env) (tfrLiteral l) t.
  Proof.
    intros.
    destruct l; simpl.
    split; intro; psemTac.
    symmetry; apply tfr_tm_sem.
    apply tfr_tm_sem.
  Qed.
  
  Lemma tfr_at_sem: forall env a t, at_sem srcSg (Itp:=srcItp) env a t <-> at_sem dstSg (Itp:=dstItp) (tfrEnv env) (tfrAtom a) t.
  Proof.
    intros.
    destruct a; simpl.
    apply tfr_lt_sem.
    apply not_iff_compat; apply tfr_lt_sem.
    do 2 rewrite tfr_tm_sem; reflexivity.
    apply not_iff_compat; do 2 rewrite tfr_tm_sem; reflexivity.
  Qed.
    
  Lemma tfr_sem: forall env f t, fm_sem srcSg (Itp:=srcItp) env f t <-> fm_sem dstSg (Itp:=dstItp) (tfrEnv env) (tfrFormula f) t.
  Proof.
    intros.
    revert env t; induction f; intros; simpl; try tauto.
    apply tfr_at_sem.
    rewrite IHf1; rewrite IHf2; reflexivity.
    rewrite IHf1; rewrite IHf2; reflexivity.
    setoid_rewrite tfr_addEnv; setoid_rewrite IHf; reflexivity.
    setoid_rewrite tfr_addEnv; setoid_rewrite IHf; reflexivity.
    setoid_rewrite IHf; reflexivity.
    setoid_rewrite IHf; reflexivity.
  Qed.
  
  Definition at_Succ (x1 x2: term dstSg s): formula dstSg :=
    Atom dstSg (Literal dstSg
     (PApp dstSg 0 Succ
        (fun i => rew eq_sym (SuccArgs i) in match rew SuccAr in i with F1 => x1 | _ => x2 end))).

  Definition at_Succ' (x1 x2: term dstSg s): formula dstSg :=
    Atom dstSg (Literal dstSg
     (PApp dstSg 0 Succ'
        (fun i => rew eq_sym (SuccArgs' i) in match rew SuccAr' in i with F1 => x1 | _ => x2 end))).

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
  
  Lemma tfrVar_var_diff: forall {s1} (v1: variable (Sig:=srcSg) s1) v2,
    not (@isEq2 _ Sort _ (variable (Sig:=dstSg)) s1 (tfrVar v1) _ (var v2)).
  Proof.
    intros; intro.
    inversion H; subst.
    apply inj_pair2_eq_dec in H2; try apply eq_dec.
    unfold tfrVar,var in H2.
    destruct (eq_dec s s); try tauto.
    discriminate.
    auto.
  Qed.
  
  Definition unary `{Sg: Sig} {s} (P: formula Sg) (x: variable (Sig:=Sg) s) :=
    vsIn Sg x (free Sg P) /\ 
    vsSubset Sg (free Sg P) (vsSing Sg x).
  
  Lemma unary_dec: forall `{Sg: Sig} {s} (P: formula Sg) (x: variable (Sig:=Sg) s), {unary P x} + {not (unary P x)}.
  Proof.
    intros.
    apply (AndDec {| dc_dec := vsIn_dec Sg x (free Sg P) |}
                     {| dc_dec := vsSubset_dec Sg (free Sg P) (vsSing Sg x) |}).
  Defined.

  Lemma tfr_tm_vars: forall s s' (w: variable s) (tm: term srcSg s'), 
    vsIn srcSg w (tm_vars srcSg tm) <->
    vsIn dstSg (tfrVar w) (tm_vars dstSg (tfrTerm tm)).
  Proof.
    intros.
    destruct tm; simpl; split; intro.
    apply vsSing_elim in H.
    injection H; clear H; intros; subst.
    apply inj_pair2_eq_dec in H; try apply eq_dec; subst w.
    apply vsSing_intro.

    apply vsSing_elim in H.
    injection H; clear H; intros; subst.
    apply inj_pair2_eq_dec in H; try apply eq_dec.
    unfold tfrVar in H.
    destruct (eq_dec s' s).
    injection H; clear H; intros; subst w.
    apply vsSing_intro.
    subst w.
    apply vsSing_intro.

    destruct H.
    destruct H.
  Qed.

  Lemma tfr_lt_vars: forall s (w: variable s) l, 
    vsIn srcSg w (lt_vars srcSg l) <->
    vsIn dstSg (tfrVar w) (lt_vars dstSg (tfrLiteral l)).
  Proof.
    intros.
    destruct l; simpl.
    split; intro.
    apply vsGUnion_elim in H.
    destruct H as [k H].
    apply vsGUnion_intro with k.
    apply tfr_tm_vars in H.
    apply H.
    
    apply vsGUnion_elim in H.
    destruct H as [k H].
    apply vsGUnion_intro with k.
    apply tfr_tm_vars in H.
    apply H.
  Qed.
  
  Lemma tfr_at_vars: forall s (w: variable s) a, 
    vsIn srcSg w (at_vars srcSg a) <->
    vsIn dstSg (tfrVar w) (at_vars dstSg (tfrAtom a)).
  Proof.
    intros.
    destruct a; simpl.
    apply tfr_lt_vars.
    apply tfr_lt_vars.
    split; intro.

    apply vsUnion_elim in H.
    destruct H; [apply vsUnion_l | apply vsUnion_r].
    revert H; apply tfr_tm_vars.
    revert H; apply tfr_tm_vars.

    apply vsUnion_elim in H.
    destruct H; [apply vsUnion_l | apply vsUnion_r].
    revert H; apply tfr_tm_vars.
    revert H; apply tfr_tm_vars.

    split; intro.
    apply vsUnion_elim in H.
    destruct H; [apply vsUnion_l | apply vsUnion_r].
    revert H; apply tfr_tm_vars.
    revert H; apply tfr_tm_vars.

    apply vsUnion_elim in H.
    destruct H; [apply vsUnion_l | apply vsUnion_r].
    revert H; apply tfr_tm_vars.
    revert H; apply tfr_tm_vars.    
  Qed.
  
  Lemma tfr_free: forall (P: formula srcSg) s' (w: variable s'),
    vsIn srcSg w (free srcSg P) <-> vsIn dstSg (tfrVar w) (free dstSg (tfrFormula P)).
  Proof.
    clear D srcItp SuccSem_cls'.
    induction P; simpl; intros; auto.
    - split; intro H; destruct H.
    - split; intro H; destruct H.
    - apply tfr_at_vars.
    - split; intro; apply vsUnion_elim in H.
      destruct H; [apply vsUnion_l; apply IHP1 | apply vsUnion_r; apply IHP2]; apply H.
      destruct H; [apply vsUnion_l; apply IHP1 | apply vsUnion_r; apply IHP2]; apply H.
    - split; intro; apply vsUnion_elim in H.
      destruct H; [apply vsUnion_l; apply IHP1 | apply vsUnion_r; apply IHP2]; apply H.
      destruct H; [apply vsUnion_l; apply IHP1 | apply vsUnion_r; apply IHP2]; apply H.
    - split; intro.
      apply vsInRemove_elim in H; destruct H.
      apply IHP in H.
      apply vsInRemove_intro; auto.
      intro; apply H0; clear H0.
      apply tfrVar_inj in H1; now auto.
      
      apply vsInRemove_elim in H; destruct H.
      apply IHP in H.
      apply vsInRemove_intro; auto.
      intro; apply H0; clear H0.
      inversion H1; clear H1; intros; subst.
      apply inj_pair2_eq_dec in H3; try apply eq_dec; subst; constructor.
    - split; intro.
      apply vsInRemove_elim in H; destruct H.
      apply IHP in H.
      apply vsInRemove_intro; auto.
      intro; apply H0; clear H0.
      apply tfrVar_inj in H1; now auto.
      
      apply vsInRemove_elim in H; destruct H.
      apply IHP in H.
      apply vsInRemove_intro; auto.
      intro; apply H0; clear H0.
      inversion H1; clear H1; intros; subst.
      apply inj_pair2_eq_dec in H3; try apply eq_dec; subst; constructor.
  Qed.

  Lemma tfr_aux_tm: forall x s (tm: term srcSg s),
    not (vsIn dstSg (var x) (tm_vars dstSg (tfrTerm tm))).
  Proof.
    intros; intro.
    destruct tm; simpl in *.
    apply vsSing_elim in H.
    simpl in H; symmetry in H.
    apply tfrVar_var_diff in H; now auto.
    inversion H.
  Qed.

  Lemma tfr_aux_lt: forall x l,
    not (vsIn dstSg (var x) (lt_vars dstSg (tfrLiteral l))).
  Proof.
    intros.
    destruct l; simpl; intro.
    apply vsGUnion_elim in H.
    destruct H as [k H].
    apply tfr_aux_tm in H; now auto.
  Qed.

  Lemma tfr_aux_at: forall x a,
    not (vsIn dstSg (var x) (at_vars dstSg (tfrAtom a))).
  Proof.
    intros; intro.
    destruct a; simpl in H.
    apply tfr_aux_lt in H; now auto.
    apply tfr_aux_lt in H; now auto.
    apply vsUnion_elim in H.
    destruct H; apply tfr_aux_tm in H; now auto.
    apply vsUnion_elim in H.
    destruct H; apply tfr_aux_tm in H; now auto.    
  Qed.

  Lemma tfr_aux: forall (P: formula srcSg) x,
    not (vsIn dstSg (var x) (free dstSg (tfrFormula P))).
  Proof.
    clear D srcItp SuccSem_cls'.
    induction P; simpl; intros; intro; auto.
    - apply tfr_aux_at in H; now auto.
    - apply vsUnion_elim in H.
      destruct H; [apply IHP1 in H | apply IHP2 in H]; now auto.
    - apply vsUnion_elim in H.
      destruct H; [apply IHP1 in H | apply IHP2 in H]; now auto.
    - apply vsInRemove_elim in H; destruct H.
      apply IHP in H; now auto.
    - apply vsInRemove_elim in H; destruct H.
      apply IHP in H; now auto.
    - apply IHP in H; now auto.
    - apply IHP in H; now auto.
  Qed.
  
  Lemma unary_tfr: forall (P: formula srcSg) (v: variable s), unary P v -> unary (tfrFormula P) (tfrVar v).
  Proof.
    intros.
    destruct H.
    split; intros.
    rewrite <-tfr_free; auto.
    
    intros s' w h.
    apply (vsSing_intro_eq dstSg).
    rewrite tfr_free in H.
    generalize (vsSubsetSing_r srcSg (free srcSg P) H0 ); clear H0; intro.
    setoid_rewrite tfr_free in H0.
    assert (vsIn dstSg w (free dstSg (tfrFormula P))) by (apply h); clear h.
    generalize (tfr_aux P).
    revert H H1 H0; generalize (free dstSg (tfrFormula P)) as F; intros.
    revert H H1 H0 H2; generalize (@vsIn _ _ _ _ dstSg).
    intros.
    set (P0F s v := P0 s v F).
    assert (forall s v, P0F s v = P0 s v F) by (intros; reflexivity).
    rewrite <-H3 in *.
    setoid_rewrite <-H3 in H0.
    setoid_rewrite <-H3 in H2.
    clear H3; clearbody P0F; clear P0 F.
    generalize (H0 s); intro.
    generalize (H0 s'); intro.
    clear H0.
    destruct (eq_dec s' s).
    subst s'.
    clear H4.
    revert H H1 H2 H3; generalize (P0F s) as PFs; clear P0F; intros.
    assert (forall w : variable s, PFs (tfrVar w) -> w = v).
      intros.
      apply H3 in H0.
      apply inj_pair2_eq_dec in H0; try apply eq_dec; now auto.
    clear H3.
    assert (w = tfrVar v).
    revert v w PFs H H1 H2 H0.
    unfold tfrVar, variable, dstSg, dstVarT, var; simpl.
    destruct (eq_dec s s); simpl; intros.
    destruct w; auto.
    apply H2 in H1; tauto.
    
    apply H0 in H1; subst e0; tauto.
    apply H0 in H1; now auto.
    subst w; reflexivity.
    
    exfalso.
    assert (forall w, P0F s' (tfrVar w) -> False).
      intros.
      apply H4 in H0.
      injection H0; intros; tauto.
    clear H4.
    assert (forall w : variable s, P0F s (tfrVar w) -> w = v).
      intros.
      apply H3 in H4.
      apply inj_pair2_eq_dec in H4; try apply eq_dec; auto.
    clear H3.
    revert w H H1 H2 H0 H4.
    generalize (P0F s) as PF; generalize (P0F s') as PF'; clear P0F.
    unfold tfrVar, variable, dstSg, dstVarT, var; simpl.
    
    destruct (@eq_dec Ts (@Sort Ts Tv Tc Tp srcSg) s' s); try tauto.
    clear n0.
    destruct (@eq_dec Ts (@Sort Ts Tv Tc Tp srcSg) s s); auto; try tauto; intros.
    apply H0 in H1; tauto.
  Qed.
  
  Definition vsubst (x y: variable (Sig:=dstSg) s) (P: formula dstSg) :=
    subst dstSg x (Var dstSg s y) P.

  Notation "'[' x ':=' y ']'" := (vsubst x y).
  
  Lemma vsubst_sem:
    forall (f: formula dstSg) (itp: Interp dstD) (env1 env2: Env dstSg dstD) t (x y: variable (Sig:=dstSg) s), 
    unary f x -> env1 s x = env2 s y -> x <> y ->
      fm_sem dstSg (Itp:=itp) env1 f t <-> fm_sem dstSg (Itp:=itp) env2 ([x:=y] f) t.
  Proof.
    intros.
    apply subst_sem; intros; auto.
    unfold unary in H.
    apply (proj2 H) in H2.
    exfalso; apply H3; clear H3.
    symmetry.
    apply vsSing_elim; auto.
    simpl; intro.
    apply vsSing_elim in H2.
    injection H2; intros; subst.
    apply inj_pair2_eq_dec in H3; try apply eq_dec.
    tauto.
  Qed.
  
  Definition Propagates (P: formula dstSg) v (fp: unary P v) :=
   All dstSg _ v (All dstSg _ (var X2) 
                      (Imp dstSg (at_Succ (Var dstSg s v) (Var dstSg s (var X2)))
                           (G dstSg (Imp dstSg P (F dstSg ([v := var X2] P )))))).
  (****** A REVOIR ****)
  
  Definition AbsClosure (P: formula dstSg) v (fp: unary P v) :=
    All dstSg _ (var Z1) (Imp dstSg  (And dstSg ([v := var Z1] P ) (Propagates P v fp))
                       (All dstSg _ (var Z2) (Imp dstSg (at_Succ' (Var dstSg s (var Z1)) (Var dstSg s (var Z2))) (F dstSg ([v := var Z2] P ))))).

  Lemma SuccSem_equ: forall env t t1 t2, fm_sem (Itp:=dstItp) dstSg env (at_Succ t1 t2) t <-> SuccSem t (tm_sem (Itp:=dstItp) dstSg env t1) (tm_sem (Itp:=dstItp) dstSg env t2).
   Proof.
    intros.
    unfold SuccSem; simpl.
    clear SuccSem_cls' SuccArgs' SuccAr'.
    generalize (psem Succ t) as ps.
    revert SuccArgs; generalize (pr_args Succ) as pa.
    rewrite SuccAr; clear SuccAr; intros.
    assert (pa = fun i => s).
      apply functional_extensionality; apply SuccArgs.
    subst pa; simpl.
    assert (SuccArgs = fun i => eq_refl).
      apply functional_extensionality; intro.
      apply proof_irrelevance.
    subst SuccArgs; simpl.
    match goal with |- ps ?f1 <-> ps ?f2 => assert (f1 = f2) end.
    apply functional_extensionality; intro i.
    destruct i; simpl; auto.
    rewrite H; tauto.
   Qed.

   Lemma SuccSem_equ': forall env t t1 t2, fm_sem (Itp:=dstItp) dstSg env (at_Succ' t1 t2) t <-> SuccSem' t (tm_sem (Itp:=dstItp) dstSg env t1) (tm_sem (Itp:=dstItp) dstSg env t2).
   Proof.
    intros.
    unfold SuccSem'; simpl.
    clear SuccSem_cls' SuccArgs SuccAr Succ.
    generalize (psem Succ' t) as ps.
    revert SuccArgs'; generalize (pr_args Succ') as pa.
    rewrite SuccAr'; clear SuccAr'; intros.
    assert (pa = fun i => s).
      apply functional_extensionality; apply SuccArgs'.
    subst pa; simpl.
    assert (SuccArgs' = fun i => eq_refl).
      apply functional_extensionality; intro.
      apply proof_irrelevance.
    subst SuccArgs'; simpl.
    match goal with |- ps ?f1 <-> ps ?f2 => assert (f1 = f2) end.
    apply functional_extensionality; intro i.
    destruct i; simpl; auto.
    rewrite H; tauto.
   Qed.

  Theorem AbsClosureOK: forall (P: formula dstSg) v (fp: unary P (tfrVar v)),
      forall (env: Env dstSg dstD) t, fm_sem (Itp:=dstItp) dstSg env (AbsClosure P (tfrVar v) fp) t.
  Proof.
    intros.
    unfold AbsClosure.
    apply All_sem; intro.
    apply Imp_sem; intro.
    apply And_sem in H; destruct H.
    apply All_sem; intro.
    apply Imp_sem; intro.
    assert ((add dstSg (var Z2) d0 (add dstSg (var Z1) d env) s
          (var Z1)) = d).
      rewrite add_ne.
      apply add_eq.
      intro.
      apply var_inj in H2; discriminate.
    assert ((add dstSg (var Z2) d0 (add dstSg (var Z1) d env) s
          (var Z2)) = d0).
      apply add_eq.
    apply SuccSem_equ' in H1.
    simpl in H1.
    rewrite H2,H3 in H1; clear H2 H3.
    
    apply SuccSem_cls' in H1.
    induction H1.
    subst d2.
    exists t; split; auto.
    clear H0.
    simpl in d1.
    rewrite <-vsubst_sem with (env1:=add dstSg (tfrVar v) (d1: ssem (Dom:=dstD) s) env) in H; auto.
    rewrite <-vsubst_sem with (env1:=add dstSg (tfrVar v) (d1: ssem (Dom:=dstD) s) env); auto.
    do 2 rewrite add_eq; now auto.
    intro.
    unfold tfrVar, var in H0; simpl in H0.
    destruct (eq_dec s s); auto; try tauto; discriminate.
    do 2 rewrite add_eq; now auto.
    intro.
    unfold tfrVar, var in H0; simpl in H0.
    destruct (eq_dec s s); auto; try tauto; discriminate.
        
    generalize (IHClosure H H0); clear IHClosure H; intro H.
    destruct H as [t' [h1 h2]].
    unfold Propagates in H0.
    rewrite All_sem in H0; specialize H0 with d2.
    rewrite All_sem in H0; specialize H0 with d3.
    rewrite Imp_sem in H0.
    rewrite <-vsubst_sem with (env1:=add dstSg (tfrVar v) (d2: ssem (Dom:=dstD) s) env) in h2; auto.
    match goal with H0: ?p -> _ |- _ => assert p as h; [clear H0 | apply H0 in h; clear H0] end.
    apply SuccSem_equ; simpl.
    rewrite add_eq.
    rewrite add_ne.
    rewrite add_eq; now auto.

    unfold tfrVar, var; simpl.
    destruct (eq_dec s s); try discriminate; now auto.
    
    rewrite G_sem in h.
    generalize (h t' h1); clear h; intro H0.
    rewrite Imp_sem in H0.
    match goal with H0: ?p -> _ |- _ => assert p as h; [clear H0 | apply H0 in h; clear H0] end.
    revert h2; apply fm_sem_equiv; intros; auto.
    apply fp in H; apply (vsSing_elim dstSg) in H.
    injection H; intros; subst s0.
    apply inj_pair2_eq_dec in H0; try apply eq_dec; subst v0.
    clear H.
    repeat rewrite add_eq.
    rewrite add_ne.
    rewrite add_eq; now auto.
    unfold tfrVar, var; simpl.
    destruct (eq_dec s s); try discriminate; now auto.

    rewrite F_sem in h.
    destruct h as [t'' [h3 h]].
    rewrite F_sem.
    exists t''; split.
    apply le_trans with t'; now auto.
    
    rewrite <-vsubst_sem with (env1:=add dstSg (tfrVar v) (d3: ssem (Dom:=dstD) s) env) in h; auto.
    rewrite <-vsubst_sem with (env1:=add dstSg (tfrVar v) (d3: ssem (Dom:=dstD) s) env); auto.
    repeat rewrite add_eq; now auto.
    unfold tfrVar, var; simpl; destruct (eq_dec s s); try discriminate; now auto.
    repeat rewrite add_eq; now auto.
    unfold tfrVar, var; simpl; destruct (eq_dec s s); try discriminate; now auto.
    repeat rewrite add_eq; now auto.
    unfold tfrVar, var; simpl; destruct (eq_dec s s); try discriminate; now auto.
  Qed.
End Closure.

Record ClosureSpec `(srcSg : Sig) (s: Sort) (Succ Succ' : predicate) (P: formula srcSg) (v: variable s):= {
  cs_ar: pr_arity Succ = 2;
  cs_ar': pr_arity Succ' = 2;
  cs_prf: forall i : Fin.t (pr_arity Succ), pr_args Succ i = s;
  cs_prf': forall i : Fin.t (pr_arity Succ'), pr_args Succ' i = s;
  cs_one: unary P v;
}.
Arguments cs_ar [_ _ _ _ _ _ _ _ _ _] _.
Arguments cs_ar' [_ _ _ _ _ _ _ _ _ _] _.
Arguments cs_prf [_ _ _ _ _ _ _ _ _ _] _.
Arguments cs_prf' [_ _ _ _ _ _ _ _ _ _] _.
Arguments cs_one [_ _ _ _ _ _ _ _ _ _] _.

Lemma ClosureSpec_dec: forall `{srcSg : Sig} {s: Sort} (Succ Succ' : predicate) (P: formula srcSg) (v: variable s),
  {ClosureSpec srcSg s Succ Succ' P v} + { not (ClosureSpec srcSg s Succ Succ' P v)}.
Proof.
  intros.
  destruct (Peano_dec.eq_nat_dec (pr_arity Succ) 2); [idtac | right; intro cs; destruct cs; tauto].
  destruct (Peano_dec.eq_nat_dec (pr_arity Succ') 2); [idtac | right; intro cs; destruct cs; tauto].
  destruct (all_dec (fun i => isEq (pr_args Succ i) s)); [idtac | destruct s0 as [i h]; simpl in h; right; intro cs; destruct cs; auto].
  destruct (all_dec (fun i => isEq (pr_args Succ' i) s)); [idtac | destruct s0 as [i h]; simpl in h; right; intro cs; destruct cs; auto].
  destruct (unary_dec P v).
  left; split; simpl in *; intros; auto.
  right; intro cs; destruct cs; auto.
Defined.

Definition cs_sem `{srcSg: Sig} {s} {Succ Succ'} {P} {v} (cs: ClosureSpec srcSg s Succ Succ' P v) {D: Dom srcSg} (itp: Interp D) : Prop :=
  ClosureSem srcSg D s itp Succ Succ' (cs_prf cs) (cs_prf' cs).

Definition absClosure`{srcSg: Sig} {s} {Succ Succ'} {P} {v} (cs: ClosureSpec srcSg s Succ Succ' P v) :=
  AbsClosure srcSg s Succ Succ' (cs_ar cs) (cs_ar' cs) (cs_prf cs) (cs_prf' cs) (tfrFormula srcSg s P) (tfrVar srcSg s v) (unary_tfr srcSg _  _ _ (cs_one cs)).

Lemma elim_cs: forall `(srcSg: Sig) s Succ Succ' P v (cs: ClosureSpec srcSg s Succ Succ' P v) (f: formula srcSg) {D: Dom srcSg} (itp: Interp D) env t,
  (cs_sem cs itp /\ fm_sem srcSg (Itp:=itp) env f t) -> 
    fm_sem (dstSg srcSg s) (Itp:=dstItp srcSg D s itp) (tfrEnv srcSg D s env) (And _ (absClosure cs) (tfrFormula srcSg s f)) t.
Proof.
  intros.
  destruct H.
  apply And_sem; split.
  apply AbsClosureOK; intros; auto.
  apply tfr_sem; auto.
Qed.
