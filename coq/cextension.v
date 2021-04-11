Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.

Require Import dec.
Require Import finite.
Require Import foltl.


Ltac psemTac :=
    match goal with
      H:psem _ _ ?sa |- psem _ _ ?sa' => assert (sa' = sa) as ae;
          try (rewrite ae; assumption); (apply functional_extensionality_dep; intros)
    end.

Section  Copy.
  Context {Ts: Type} {Tv: Ts->Type} {Tc1 Tc2: Ts->Type} {Tp: Type}.
  Variable Sg1: @Sig Ts Tv Tc1 Tp.
  Variable D1: Dom Sg1.
  Variable itp1 : Interp D1.
  Variable Fc2 : forall (s: Ts), @Finite (Tc2 s). 
  Variable m: forall s, Tc1 s -> Tc2 s.

  Definition Sg2 : @Sig Ts Tv Tc2 Tp := {|
    Sort := Sort (Sig:=Sg1);
    constant s := Fc2 s;
    variable := variable (Sig:=Sg1);
    predicate := predicate (Sig:=Sg1);
    pr_arity := pr_arity (Sig:=Sg1);
    pr_args := pr_args (Sig:=Sg1);
  |}.
  Definition D2: Dom Sg2 := {|
    ssemT (s: Sort (Sig:=Sg2)) := ssemT (Dom:=D1) s;
    ssem := ssem (Dom:=D1);
    neDom := neDom (Dom:=D1)
  |}.
  
  Program Definition itp2 (vc: forall (s: Sort (Sig:=Sg2)), Tc2 s -> ssem s) : Interp D2 := {|
    csem := (vc: forall (s: Sort (Sig:=Sg2)), constant (Sig:=Sg2) s -> ssem s);
    psem (p: predicate (Sig:=Sg2)) t (a: forall (i:Fin.t (pr_arity (Sig:=Sg2) p)), ssem (pr_args (Sig:=Sg2) p i)) := 
      psem (Interp:=itp1) p t (fun (i: Fin.t (pr_arity (Sig:=Sg1) p)) => ((a i): ssem (pr_args (Sig:=Sg1) p i)))
  |}.

  Definition copy_tm {s} (tm: term Sg1 s): term Sg2 s :=
    match tm with
      Var _ _ v => Var Sg2 _ v
    | Cst _ _ c => Cst Sg2 _ (m s c)
    end.

  Definition copy_lt (l: literal Sg1): literal Sg2 :=
    match l with
      PApp _ n p a => PApp Sg2 n p (fun i => copy_tm (a i))
    end.

  Definition copy_at (a: atom Sg1): atom Sg2 :=
    match a with
     Literal _ l => Literal Sg2 (copy_lt l)
    | NLiteral _ l => NLiteral Sg2 (copy_lt l)
    | Eq _ s t1 t2 => Eq Sg2 s (copy_tm t1) (copy_tm t2)
    | NEq _ s t1 t2 => NEq Sg2 s (copy_tm t1) (copy_tm t2)
    end.

  Fixpoint copy_fm (f: formula Sg1): formula Sg2 :=
  match f with
    FTrue _ => FTrue _
  | FFalse _ => FFalse _
  | Atom _ a => Atom _ (copy_at a)
  | And _ f1 f2 => And _ (copy_fm f1) (copy_fm f2)
  | Or _ f1 f2 => Or _ (copy_fm f1) (copy_fm f2)
  | Ex _ s v f' => Ex Sg2 s v (copy_fm f')
  | All _ s v f' => All Sg2 s v (copy_fm f')
  | F _ f' => F _ (copy_fm f')
  | G _ f' => G _ (copy_fm f')
  end.

  Definition copy_env (env: Env Sg1 D1): Env Sg2 D2 := env.

  Lemma copy_sem_tm : 
    forall s (tm: term Sg1 s) env vc (h: forall s e, csem e = vc s (m s e)), tm_sem (Itp:=itp1) Sg1 env tm =
      tm_sem (Itp:=itp2 vc) Sg2 env (copy_tm tm).
  Proof.
    intros.
    destruct tm; simpl; intros; auto.
  Qed.

  Lemma copy_sem_lt : 
    forall l env vc (h: forall s e, csem e = vc s (m s e)) t, 
      lt_sem (Itp:=itp1) Sg1 env l t <->
      lt_sem (Itp:=itp2 vc) Sg2 env (copy_lt l) t.
  Proof.
    intros; destruct l; simpl in *.
    split; intro H; psemTac; clear H.
    symmetry; apply copy_sem_tm; now auto.
    apply copy_sem_tm; now auto.
  Qed.
  
  Lemma copy_sem_at : 
    forall a env vc (h: forall s e, csem e = vc s (m s e)) t, 
      at_sem (Itp:=itp1) Sg1 env a t <->
      at_sem (Itp:=itp2 vc) Sg2 env (copy_at a) t.
  Proof.
    intros; destruct a; simpl in *.
    rewrite copy_sem_lt; auto; tauto.
    rewrite copy_sem_lt; auto; tauto.
    rewrite copy_sem_tm with (vc:=vc); auto.
    rewrite copy_sem_tm with (vc:=vc); auto.
    reflexivity.
    rewrite copy_sem_tm with (vc:=vc); auto.
    rewrite copy_sem_tm with (vc:=vc); auto.
    reflexivity.
  Qed.
  
  Lemma copy_sem : 
    forall f env vc (h: forall s e, csem e = vc s (m s e)) t, 
      fm_sem (Itp:=itp1) Sg1 env f t <->
      fm_sem (Itp:=itp2 vc) Sg2 env (copy_fm f) t.
  Proof.
    induction f; simpl; intros; auto; try tauto.
    - apply copy_sem_at; tauto.
    - rewrite <-IHf1, <-IHf2; auto; tauto.
    - rewrite <-IHf1, <-IHf2; auto; tauto.
    - split; intro H; destruct H as [d H]; exists d; revert H; apply IHf; auto.
    - split; intros H d; specialize (H d); revert H; apply IHf; auto.
    - split; intro H; destruct H as [t' [ht H]]; exists t'; split; auto; revert H; apply IHf; auto.
    - split; intros H t' th; specialize (H t' th); revert H; apply IHf; auto.
  Qed.
End Copy.

Definition cextSig `(Sg: Sig) {xT : Sort (Sig:=Sg) -> Type} (xF : forall s, @Finite (xT s)): Sig :=
  Sg2 Sg (fun s => SumFin (constant s) (xF s)).

Definition cext_dom `(Sg: Sig) {xT : Sort (Sig:=Sg) -> Type} (xF : forall s, @Finite (xT s)) (D: Dom Sg): Dom (cextSig Sg xF) :=
  D2 Sg D (fun s => SumFin (constant s) (xF s)).

Definition cext_itp `(Sg: Sig) {D: Dom Sg} (itp: Interp (Sg:=Sg) D) {xT : Sort (Sig:=Sg) -> Type} (xF : forall s, @Finite (xT s)) (xD: forall s, xT s -> ssem s): Interp (Sg:=cextSig Sg xF) (cext_dom Sg xF D) := 
  itp2 Sg D itp (fun s => SumFin (constant s) (xF s)) (fun s c => match c with inr c1 => xD s c1 | inl c2 => csem (Interp:=itp) c2 end).

Definition cext_env `(Sg: Sig) {D: Dom Sg} {xT : Sort (Sig:=Sg) -> Type} (xF : forall s, @Finite (xT s)) (env: Env Sg D) : Env (cextSig Sg xF) (cext_dom Sg xF D) := env.

Definition cext_fm `{Sg: Sig} {xT : Sort (Sig:=Sg) -> Type} (xF : forall s, @Finite (xT s)) (f: formula Sg) : formula (cextSig Sg xF) :=
  copy_fm Sg (fun s => SumFin (constant s) (xF s)) (fun s c => inl c) f.
  
Lemma cext_sem `(Sg:Sig) (D: Dom Sg) (itp: Interp (Sg:=Sg) D) {xT : Sort (Sig:=Sg) -> Type} (xF : forall s, @Finite (xT s)) (f: formula Sg): 
    forall xD (env: Env Sg D) t, fm_sem Sg (Itp:=itp) env f t <-> fm_sem (cextSig Sg xF) (Itp:=cext_itp Sg itp xF xD) (cext_env Sg xF env) (cext_fm xF f) t.
Proof.
  intros.
  apply copy_sem; auto.
Qed.

Definition cext2Sig `(Sg: Sig) 
    {xT1: Sort -> Type} (xF1: forall s, @Finite (xT1 s)) 
    {xT2: Sort -> Type} (xF2: forall s, @Finite (xT2 s)) :=
  cextSig Sg (fun s => SumFin (xF1 s) (xF2 s)).

Definition cext2_dom `(Sg: Sig) 
  {xT1 : Sort (Sig:=Sg) -> Type} (xF1 : forall s, @Finite (xT1 s))
  {xT2 : Sort (Sig:=Sg) -> Type} (xF2 : forall s, @Finite (xT2 s)) (D: Dom Sg): Dom (cext2Sig Sg xF1 xF2) :=
  D2 Sg D (fun s => SumFin (constant s) (SumFin (xF1 s) (xF2 s))).

Definition cext2_env `(Sg: Sig) 
  {xT1 : Sort (Sig:=Sg) -> Type} (xF1 : forall s, @Finite (xT1 s))
  {xT2 : Sort (Sig:=Sg) -> Type} (xF2 : forall s, @Finite (xT2 s)) {D: Dom Sg}(env: Env Sg D): Env (cext2Sig Sg xF1 xF2) (cext2_dom Sg xF1 xF2 D) :=
  env.

Definition cext2_itp `{Sg:Sig} {D: Dom Sg} (itp: Interp (Sg:=Sg) D) 
    {xT1: Sort -> Type} (xF1: forall s, @Finite (xT1 s)) 
    {xT2: Sort -> Type} (xF2: forall s, @Finite (xT2 s))
    xD1 xD2 : Interp (cext2_dom Sg xF1 xF2 D)
  := cext_itp Sg itp (fun s => SumFin (xF1 s) (xF2 s)) 
    (fun s c => match c  with inl c1 => xD1 s c1 | inr c2 => xD2 s c2 end).

Definition cinj1_fm `(Sg: Sig) 
    {xT1: Sort -> Type} (xF1: forall s, @Finite (xT1 s)) 
    {xT2: Sort -> Type} (xF2: forall s, @Finite (xT2 s))
    (f: formula (cextSig Sg xF1)): formula (cext2Sig Sg xF1 xF2) :=
  copy_fm (cextSig Sg xF1) (fun s => SumFin (constant s) (SumFin (xF1 s) (xF2 s)))
    (fun s c => match c with inl c1 => inl c1 | inr c2 => inr (inl c2) end) f.

Definition cinj2_fm `(Sg: Sig) 
    {xT1: Sort -> Type} (xF1: forall s, @Finite (xT1 s)) 
    {xT2: Sort -> Type} (xF2: forall s, @Finite (xT2 s))
    (f: formula (cextSig Sg xF2)): formula (cext2Sig Sg xF1 xF2) :=
  copy_fm (cextSig Sg xF2) (fun s => SumFin (constant s) (SumFin (xF1 s) (xF2 s)))
    (fun s c => match c with inl c1 => inl c1 | inr c2 => inr (inr c2) end) f.

Lemma cinj1_sem `(Sg: Sig)
  {xT1: Sort -> Type} (xF1: forall s, @Finite (xT1 s)) 
  {xT2: Sort -> Type} (xF2: forall s, @Finite (xT2 s))
  (f: formula (cextSig Sg xF1)) (D: Dom Sg) env t (itp: Interp D) xD1 xD2:
    fm_sem (Itp:=cext_itp Sg itp xF1 xD1) (cextSig Sg xF1) env f t -> 
      fm_sem (Itp:=cext2_itp itp xF1 xF2 xD1 xD2) (cext2Sig Sg xF1 xF2) env (cinj1_fm Sg xF1 xF2 f) t.
Proof.
  intro.
  apply (copy_sem (cextSig Sg xF1) _ (cext_itp Sg itp xF1 xD1) 
    (fun s => SumFin (constant s) (SumFin (xF1 s) (xF2 s)))); intros; auto.
  destruct e; auto.
Qed.

Lemma cinj2_sem `(Sg: Sig)
  {xT1: Sort -> Type} (xF1: forall s, @Finite (xT1 s)) 
  {xT2: Sort -> Type} (xF2: forall s, @Finite (xT2 s))
  (f: formula (cextSig Sg xF2)) (D: Dom Sg) env t (itp: Interp D) xD1 xD2:
    fm_sem (Itp:=cext_itp Sg itp xF2 xD2) (cextSig Sg xF2) env f t -> 
      fm_sem (Itp:=cext2_itp itp xF1 xF2 xD1 xD2) (cext2Sig Sg xF1 xF2) env (cinj2_fm Sg xF1 xF2 f) t.
Proof.
  intro.
  apply (copy_sem (cextSig Sg xF2) _ (cext_itp Sg itp xF2 xD2) 
    (fun s => SumFin (constant s) (SumFin (xF1 s) (xF2 s)))); intros; auto.
  destruct e; auto.
Qed.

Definition cinj1_env `(Sg: Sig) 
  {xT1 : Sort (Sig:=Sg) -> Type} (xF1 : forall s, @Finite (xT1 s))
  {xT2 : Sort (Sig:=Sg) -> Type} (xF2 : forall s, @Finite (xT2 s)) {D: Dom Sg} (env: Env (cextSig Sg xF1) (cext_dom Sg xF1 D)): Env (cext2Sig Sg xF1 xF2) (cext2_dom Sg xF1 xF2 D) :=
  env.

Definition cinj2_env `(Sg: Sig) 
  {xT1 : Sort (Sig:=Sg) -> Type} (xF1 : forall s, @Finite (xT1 s))
  {xT2 : Sort (Sig:=Sg) -> Type} (xF2 : forall s, @Finite (xT2 s)) {D: Dom Sg} (env: Env (cextSig Sg xF2) (cext_dom Sg xF2 D)): Env (cext2Sig Sg xF1 xF2) (cext2_dom Sg xF1 xF2 D) :=
  env.

