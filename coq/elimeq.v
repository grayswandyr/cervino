Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.

Require Import Arith.
Require Import Eqdep_dec.
Require Import Fin.
Import EqNotations.

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
    
Section ElimEq.
  Context {Ts: Type} {Tv: Ts->Type} {Tc: Ts->Type} {Tp: Type}.
  Variable srcSg: @Sig Ts Tv Tc Tp.
  Variable D: Dom srcSg.
  Variable srcItp : Interp D.

  Definition dst_arity (p: SumFin predicate Sort) := 
    match p with inl p => pr_arity p | inr _ => 2 end.
  
  Definition dst_args (p: SumFin predicate Sort) :=
    match p return Fin.t (dst_arity p) -> Sort with inl p => pr_args p | inr s => fun _ => s end.

  Inductive NewVarsType (s: Sort): Type :=
    NV1
  | NV2
  | NV3
  | NVx (p: predicate) (i: Fin.t (pr_arity p))
  | NVy (p: predicate) (i: Fin.t (pr_arity p)).
  
  Program Definition NewVarsDec s : EqDec (T:= NewVarsType s).
  Proof.
    repeat (split || intro).
    destruct x; destruct y; try (left; now auto); try (right; discriminate).
    destruct (eq_dec p p0).
    subst p0.
    destruct (eq_dec i i0).
    subst i0.
    left; reflexivity.
    
    right; intro.
    injection H; clear H; intros; subst.
    apply inj_pair2_eq_dec in H; try apply eq_dec; tauto.
    
    right; intro.
    injection H; clear H; intros; subst.
    apply inj_pair2_eq_dec in H; try apply eq_dec; tauto.
    
    destruct (eq_dec p p0).
    subst p0.
    destruct (eq_dec i i0).
    subst i0.
    left; reflexivity.
    
    right; intro.
    injection H; clear H; intros; subst.
    apply inj_pair2_eq_dec in H; try apply eq_dec; tauto.
    
    right; intro.
    injection H; clear H; intros; subst.
    apply inj_pair2_eq_dec in H; try apply eq_dec; tauto.
  Qed.
  
  Definition NewVarsSet (s:Sort): SV.set (NewVarsDec s) :=
   SV.add (NV1 s)
    (SV.add (NV2 s)
      (SV.add (NV3 s)
        (SV.union
           (SV.CUnion (fun _ : predicate => TrueDec) fin_set
              (fun p _ =>
               SV.CUnion (fun _ => TrueDec)
                 fin_set
                 (fun i _ => SV.sing (NewVarsDec s) (NVx s p i))))
           (SV.CUnion (fun _ => TrueDec) fin_set
              (fun p _ =>
               SV.CUnion (fun _ => TrueDec)
                 fin_set
                 (fun i _ => SV.sing (NewVarsDec s) (NVy s p i))))))).
  
  Program Definition NewVarsFin s : Finite (T:= NewVarsType s) := {|
    fin_dec := NewVarsDec s;
    fin_set := NewVarsSet s;
  |}.
  Next Obligation.
    destruct x.
    apply SV.InAdd_l.
    apply SV.InAdd_r; apply SV.InAdd_l.
    apply SV.InAdd_r; apply SV.InAdd_r; apply SV.InAdd_l.
    apply SV.InAdd_r; apply SV.InAdd_r; apply SV.InAdd_r.
    apply SV.InUnion_l.
    apply SV.InCUnion_intro with (u:=p).
    apply fin_all.
    constructor.
    intros _.
    apply SV.InCUnion_intro with (u:=i).
    apply fin_all.
    constructor.
    intros _.
    now apply SV.InSing.

    apply SV.InAdd_r; apply SV.InAdd_r; apply SV.InAdd_r.
    apply SV.InUnion_r.
    apply SV.InCUnion_intro with (u:=p).
    apply fin_all.
    constructor.
    intros _.
    apply SV.InCUnion_intro with (u:=i).
    apply fin_all.
    constructor.
    intros _.
    now apply SV.InSing.
  Qed.
  
  Definition dstSg : Sig := {|
    Sort := Sort (Sig:=srcSg);
    variable s := SumFin (variable s) (NewVarsFin s);
    constant := constant;
    predicate := SumFin predicate (Sort (Sig:=srcSg));
    pr_arity := dst_arity;
    pr_args := dst_args
  |}.
  
  Program Definition dstD: Dom dstSg := {| ssem := ssem (Dom:=D); neDom := neDom (Dom:=D) |}.
  
  Definition dst_psem (p: SumFin predicate Sort) t :
     (forall i : Fin.t (dst_arity p), ssem (dst_args p i)) -> Prop :=
  match p with
    inl p => psem (Interp:=srcItp) p t
  | inr s => fun args => args F1 = args (FS F1)
  end.
  
  Program Definition dstItp : Interp dstD := {| 
    csem s c := csem (Interp:=srcItp) c; 
    psem := dst_psem
  |}.
  
  Definition tfrTerm {s} (tm: term srcSg s): term dstSg s :=
  match tm return term dstSg s with
    Cst _ _ c => Cst dstSg _ c
  | Var _ _ v => Var dstSg _ (inl v)
  end.
  
  Definition tfrLiteral (l: literal srcSg): literal dstSg :=
  match l with
    PApp _ x r args => PApp dstSg x (inl r) (fun i => tfrTerm (args i))
  end.
  
  Definition mkEq s (t1 t2: term dstSg s): literal dstSg :=
    PApp dstSg 0 (inr s) (fun i => match i with F1 => t1 | _ => t2 end).
  
  Definition tfrAtom (a: atom srcSg): atom dstSg :=
  match a with
    Literal _ l => Literal dstSg (tfrLiteral l)
  | NLiteral _ l => NLiteral dstSg (tfrLiteral l)
  | Eq _ s t1 t2 => Literal dstSg (mkEq s (tfrTerm t1) (tfrTerm t2))
  | NEq _ s t1 t2 => NLiteral dstSg (mkEq s (tfrTerm t1) (tfrTerm t2))
  end.
  
  Fixpoint tfrFormula (f: formula srcSg): formula dstSg :=
  match f with
  | FTrue _ => FTrue dstSg
  | FFalse _ => FFalse dstSg
  | Atom _ a => Atom dstSg (tfrAtom a)
  | And _ f1 f2 => And dstSg (tfrFormula f1) (tfrFormula f2)
  | Or _ f1 f2 => Or dstSg (tfrFormula f1) (tfrFormula f2)
  | Ex _ s v f => Ex dstSg s (inl v) (tfrFormula f)
  | All _ s v f => All dstSg s (inl v) (tfrFormula f)
  | F _ f => F dstSg (tfrFormula f)
  | G _ f => G dstSg (tfrFormula f)
  end.

  Definition tfrEnv (env: Env srcSg D) : Env dstSg dstD :=
    fun s v => match v with 
      inl w => env s w
     | _ => neDom _
     end.

  Lemma tfr_tm_sem: forall env s' (tm: term srcSg s'), tm_sem srcSg (Itp:=srcItp) env tm = tm_sem dstSg (Itp:=dstItp) (tfrEnv env) (tfrTerm tm).
  Proof.
    intros.
    destruct tm; simpl; auto.
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
  
  Program Definition tfr_dom (D: Dom srcSg): Dom dstSg := {|
    ssem s := ssem (Dom:=D) s;
    neDom s := neDom (Dom:=D) s;
  |}.

  Lemma tfrEnv_add: forall env s (v: variable s) (d: ssem (Sg:=srcSg) s),
    tfrEnv (add srcSg v d env) = add dstSg (inl v) (d: ssem (Dom:=tfr_dom D) s) (tfrEnv env).
  Proof.
    intros.
    apply functional_extensionality_dep; intro s'.
    apply functional_extensionality; intro v'.
    destruct v'.
    unfold tfrEnv, add; simpl.
    destruct (eq_dec s s'); simpl.
    subst s'.
    destruct (eq_dec v e).
    subst e.
    reflexivity.
    reflexivity.
    reflexivity.
    
    unfold tfrEnv, add; simpl.
    destruct (eq_dec s s'); simpl.
    subst s'.
    reflexivity.
    reflexivity.
  Qed.
  
  Lemma tfr_sem: forall env f t, fm_sem srcSg (Itp:=srcItp) env f t <-> fm_sem dstSg (Itp:=dstItp) (tfrEnv env) (tfrFormula f) t.
  Proof.
    intros.
    revert env t; induction f; intros; simpl; try tauto.
    apply tfr_at_sem.
    rewrite IHf1; rewrite IHf2; reflexivity.
    rewrite IHf1; rewrite IHf2; reflexivity.
    setoid_rewrite IHf; setoid_rewrite tfrEnv_add; reflexivity.
    setoid_rewrite IHf; setoid_rewrite tfrEnv_add; reflexivity.
    setoid_rewrite IHf; reflexivity.
    setoid_rewrite IHf; reflexivity.
  Qed.
  
  Definition veq {s: Sort} (v1 v2: NewVarsType s) :=
    Atom dstSg (Literal dstSg (mkEq s (Var dstSg s (inr v1)) (Var dstSg s (inr v2)))).
  
  (* !v1, equiv_s v1 v1 *)
  Definition mk_refl (s: Sort) := All dstSg s (inr (NV1 s)) (All dstSg s (inr (NV2 s)) (veq (NV1 s) (NV1 s))).

  (* !x y, equiv_s x y -> equiv_s y x *)
  Definition mk_sym (s: Sort) := 
    All dstSg s (inr (NV1 s)) (All dstSg s (inr (NV2 s)) 
      (Imp dstSg (veq (NV1 s) (NV2 s)) (veq (NV2 s) (NV1 s)))).

  (* !v1 v2 v3, equiv_s v1 v2 -> equiv_s v2 v3 -> equiv_s v1 v3 *)
  Definition mk_trans s := 
    All dstSg s (inr (NV1 s)) (All dstSg s (inr (NV2 s)) (All dstSg s (inr (NV3 s))
      (Imp dstSg (veq (NV1 s) (NV2 s)) (Imp dstSg (veq (NV2 s) (NV3 s)) (veq (NV1 s) (NV3 s)))))).

  (* /\_p !x1...xn y1...yn, equiv_s xi yi -> ... -> p(x1,...,xn) <-> p(y1,...,yn) *)
  Definition mk_pcongr (p: predicate (Sig:=srcSg)) :=
    IAll dstSg (uptoFinite (pr_arity p)) (pr_args p) (fun i => inr (NVx (pr_args p i) p i))
      (IAll dstSg (uptoFinite (pr_arity p)) (pr_args p) (fun i => inr (NVy (pr_args p i) p i))
        (Imp dstSg
          (IAnd dstSg (uptoFinite (pr_arity p)) (fun i => veq (NVx (pr_args p i) p i) (NVy (pr_args p i) p i)))
          (Equiv dstSg 
            (Atom _ (Literal _ (PApp dstSg 0 (inl p) (fun i => Var dstSg _ (inr (NVx (pr_args p i) p i))))))
            (Atom _ (Literal _ (PApp dstSg 0 (inl p) (fun i => Var dstSg _ (inr (NVy (pr_args p i) p i))))))
            ))).

  Definition mk_congr: formula dstSg := IAnd dstSg (predicate (Sig:=srcSg)) mk_pcongr.

  Lemma refl_sem: forall s env t, fm_sem (Itp:=dstItp) dstSg env (mk_refl s) t.
  Proof.
    intros.
    unfold mk_refl.
    apply All_sem; intro.
    apply All_sem; intro.
    reflexivity.
  Qed.

  Lemma sym_sem: forall s env t, fm_sem (Itp:=dstItp) dstSg env (mk_sym s) t.
  Proof.
    intros.
    unfold mk_sym.
    apply All_sem; intro.
    apply All_sem; intro.
    apply Imp_sem; intro.
    symmetry.
    apply H.
  Qed.

  Lemma trans_sem: forall s env t, fm_sem (Itp:=dstItp) dstSg env (mk_trans s) t.
  Proof.
    intros.
    unfold mk_trans.
    apply All_sem; intro.
    apply All_sem; intro.
    apply All_sem; intro.
    apply Imp_sem; intro.
    apply Imp_sem; intro.
    simpl in *.
    rewrite H.
    apply H0.
  Qed.

  Lemma congr_sem: forall env t, fm_sem (Itp:=dstItp) dstSg (tfrEnv env) mk_congr t.
  Proof.
    intros.
    unfold mk_congr.
    apply IAnd_sem; intro.
    apply IAll_sem; intro.
    apply IAll_sem; intro.
    apply Imp_sem; intro.
    apply Equiv_sem; split; intro.
    generalize (fun env h => proj1 (IAnd_sem dstSg (dstD) dstItp env _ (fun i  =>
          veq (NVx (pr_args k i) k i) (NVy (pr_args k i) k i)) t) h); intro.
    simpl.
    simpl in H1.
    generalize (H1 _ H); clear H1 H; intro.
    simpl in H0.
    psemTac; clear H0.
    rewrite H; clear H.
    reflexivity.
    
    generalize (fun env h => proj1 (IAnd_sem dstSg (dstD) dstItp env _ (fun i  =>
          veq (NVx (pr_args k i) k i) (NVy (pr_args k i) k i)) t) h); intro.
    simpl.
    simpl in H1.
    generalize (H1 _ H); clear H1 H; intro.
    simpl in H0.
    psemTac; clear H0.
    rewrite H; clear H.
    reflexivity.
  Qed.

  Definition equiv_spec :=
    G dstSg (And dstSg (IAnd dstSg Sort mk_refl)
                (And _ (IAnd dstSg Sort mk_sym)
                         (And _ 
                            (IAnd dstSg Sort mk_trans)
                            mk_congr))).

  Lemma equiv_spec_sem:
    forall env t,  fm_sem (Itp:=dstItp) dstSg (tfrEnv env) equiv_spec t.
  Proof.
    intros.
    apply G_sem; intros.
    apply And_sem; split.
    apply IAnd_sem; intros.
    apply refl_sem.
    apply And_sem; split.
    apply IAnd_sem; intros.
    apply sym_sem.
    apply And_sem; split.
    apply IAnd_sem; intros.
    apply trans_sem.
    apply congr_sem.
  Qed.
  
  Definition elim_eq f := And dstSg equiv_spec (tfrFormula f).
  
  Lemma elim_eq_sem: forall f env t, fm_sem srcSg (Itp:=srcItp) env f t <->
    fm_sem dstSg (Itp:=dstItp) (tfrEnv env) (elim_eq f) t.
  Proof.
    intros.
    unfold elim_eq.
    rewrite And_sem.
    rewrite tfr_sem.
    intuition.
    apply equiv_spec_sem.
  Qed.
  
End ElimEq.

(** PaperLemma 1 **)
Lemma elim_eq_sat: forall `(srcSg: Sig) (f: formula srcSg),
  isSat srcSg f -> isSat (dstSg srcSg) (elim_eq srcSg f).
Proof.
  intros.
  destruct H as [D [srcItp [env [t H]]]].
  apply elim_eq_sem in H.
  exists (tfr_dom srcSg D).
  exists (dstItp srcSg D srcItp).
  exists (tfrEnv srcSg D env).
  exists t.
  apply H.
Qed.

