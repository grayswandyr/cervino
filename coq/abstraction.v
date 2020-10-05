
Require Import ProofIrrelevance.
Require Import Eqdep_dec.
Require Import Classical.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.IndefiniteDescription.
Require Import Fin.

Require Import foltl.
Require Import dec.
Require Import finite.
Require Import set.
Require Import subItp.
Require Import quantifiers.
Require Import env.
Require Import varset.
Require Import vars.

Section Abstraction.
  Context {Ts: Type} {Tv: Ts->Type} {Tc: Ts->Type} {Tp: Type}.
  Variable srcSig: @Sig Ts Tv Tc Tp.
  Existing Instance srcSig.

  Section ExAll.

  Variable exv: VarSet srcSig.
  Variable allv: VarSet srcSig.
  Variable ex_all_exc: forall s, SV.disjoint (exv s) (allv s).

  Inductive newPred :=
    OldPred (p: predicate)
  | NewPred (s: Sort) (v: variable s) (h: SV.set_In v (exv s)).

  Program Definition newPredDec: @EqDec newPred := {| eq_dec:= _ |}.
  Next Obligation.
    repeat intro.
    destruct x; destruct y.
    destruct (eq_dec p p0).
    subst.
    left; reflexivity.
    right; intro.
    injection H; clear H; intro; tauto.
    right; intro; discriminate.
    right; intro; discriminate.
    destruct (eq_dec s s0).
    subst s0.
    destruct (eq_dec v v0).
    subst v0.
    left.
    rewrite (proof_irrelevance _ h h0).
    reflexivity.
    right; intro.
    injection H; clear H; intros.
    apply inj_pair2_eq_dec in H; try apply eq_dec; tauto.
    right; intro.
    injection H; clear H; intros; tauto.
  Qed.

  Definition dstTa (p:newPred): Type := 
    match p with OldPred op => Fin.t (pr_arity op) | NewPred _ _ _ => One end.

  Definition dstSig: Sig := {|
    Sort := Sort (Sig:=srcSig);
    variable := variable (Sig:=srcSig);
    constant := constant (Sig:=srcSig);
    predicate := newPredDec;
    pr_arity p := match p with OldPred op => pr_arity op | NewPred _ _ _ => 1 end;
    pr_args p := match p with OldPred op => pr_args op | NewPred s _ _ => fun i => s end
  |}.

  Definition tm_dstSig {s} (tm: term srcSig s): term dstSig s :=
    match tm with
      Var _ _ v => Var dstSig s v
    | Cst _ _ c => Cst dstSig s c
    end.
  
  Definition lt_dstSig (a: literal srcSig): literal dstSig :=
    match a with
      PApp _ n p args => PApp dstSig n (OldPred p) (fun i => tm_dstSig (args i))
    end.

  Definition at_dstSig (a: atom srcSig): atom dstSig :=
    match a with
    | Literal _ l => Literal dstSig (lt_dstSig l)
    | NLiteral _ l => NLiteral dstSig (lt_dstSig l)
    | Eq _ s t1 t2 => Eq dstSig s (tm_dstSig t1) (tm_dstSig t2)
    | NEq _ s t1 t2 => NEq dstSig s (tm_dstSig t1) (tm_dstSig t2)
    end.

  Fixpoint fm_dstSig (f: formula srcSig): formula dstSig :=
    match f with
      FTrue _ => FTrue dstSig
    | FFalse _ => FFalse dstSig
    | Atom _ a => Atom dstSig (at_dstSig a)
    | And _ f1 f2 => And dstSig (fm_dstSig f1) (fm_dstSig f2)
    | Or _ f1 f2 => Or dstSig (fm_dstSig f1) (fm_dstSig f2)
    | All _ s v f => All dstSig s v (fm_dstSig f)
    | Ex _ s v f => Ex dstSig s v (fm_dstSig f)
    | F _ f => F dstSig (fm_dstSig f)
    | G _ f => G dstSig (fm_dstSig f)
    end.

  Definition tm_abstract {s} (tm: term srcSig s): term dstSig s :=
  match tm with
    Var _ _ v => Var dstSig s v
  | Cst _ _ c => Cst dstSig s c
  end.

  Definition Ed {s} (v: variable s) (h: SV.set_In v (exv s)) (d: term dstSig s) :=
    PApp dstSig 0 (NewPred s v h) (fun i => d).
  
  Definition Ey {s} (v: variable s) (h: SV.set_In v (exv s)) (w: variable s) :=
    Ed v h (Var dstSig s w).
  
  Definition mk_disj `{K: Finite} {sk: K-> Sort} (tk: forall k, term srcSig (sk k)) :=
    IOr dstSig K (fun k =>
      match tk k with
        Cst _ _ _ => FFalse dstSig
      | Var _ _ v => 
        match SV.In_dec v (exv (sk k)) with
          left h => Atom _ (NLiteral dstSig (Ey v h v))
        | right _ => FFalse dstSig
        end
      end).
  
  (*
    X^n p(.. yi ..)_{i in I}
    /\_{i in I} E^n_i(yi) -> X^n p(.. yi ..)
    RQ: pas de X sur E
  *)
  
  Definition lt_abstract (a: literal srcSig) :=
    match a with
      PApp _ n p args => 
        Or dstSig
          (mk_disj args)
          (Atom _ (Literal _ (PApp dstSig n (OldPred p) (fun i => tm_abstract (args i)))))
    end.

  (*
    X^n -p(.. yi ..)_{i in I}
    /\_{i in I} E^n_i(yi) -> X^n -p(.. yi ..)
    RQ: pas de X sur E
  *)

  Definition nlt_abstract (a: literal srcSig) :=
    match a with
      PApp _ n p args => 
        Or dstSig
          (mk_disj args)
          (Atom _ (NLiteral _ (PApp dstSig n (OldPred p) (fun i => tm_abstract (args i)))))
    end.
  
  Definition eq_yy {s} (v: variable s) (hv: SV.set_In v (exv s)) (w: variable s) (hw: SV.set_In w (exv s)) :=
    And _ (Or _ (Atom _ (NLiteral _ (Ey v hv v))) (Atom _ (Literal _ (Ey w hw v))))
           (Or _ (Atom _ (NLiteral _ (Ey w hw w))) (Atom _ (Literal _ (Ey v hv w)))).

  Definition neq_yy {s} (v: variable s) (hv: SV.set_In v (exv s)) (w: variable s) (hw: SV.set_In w (exv s)) :=
    And _ (Or _ (Atom _ (NLiteral _ (Ey v hv v))) (Atom _ (NLiteral _ (Ey w hw v))))
           (Or _ (Atom _ (NLiteral _ (Ey w hw w))) (Atom _ (NLiteral _ (Ey v hv w)))).

  Definition eq_yd {s} (v: variable s) (hv: SV.set_In v (exv s)) (tm: term dstSig s) :=
    Atom _ (Literal _ (Ed v hv tm)).

  Definition neq_yd {s} (v: variable s) (hv: SV.set_In v (exv s)) (tm: term dstSig s) :=
    Atom _ (NLiteral _ (Ed v hv tm)).
  
  (*
    X^n (yi = yj)
    (E^n_i yi -> E^n_j yi) && (E^n_j yj -> E^n_i yj)

    X^n (yi = v)
    (E^n_i yi -> E^n_i v)
    
    RQ: pas de X sur E
  *)
  Definition eq_abstract {s} (t1 t2: term srcSig s): formula dstSig :=
    match t1,t2 with
      Var _ _ v1, Var _ _ v2 =>
        match SV.In_dec v1 (exv s) with
          left h1 =>
            match SV.In_dec v2 (exv s) with
              left h2 => eq_yy v1 h1 v2 h2
            | right _ => eq_yd v1 h1 (Var dstSig _ v2)
            end
        | right _ =>
            match SV.In_dec v2 (exv s) with
              left h2 => eq_yd v2 h2 (Var dstSig _ v1)
            | right _ => Atom _ (Eq dstSig s (Var dstSig _ v1) (Var dstSig _ v2))
            end
        end
     | Cst _ _ c, Var _ _ v2 =>
        match SV.In_dec v2 (exv s) with
          left h2 => eq_yd v2 h2 (Cst dstSig _ c)
        | right _ => Atom _ (Eq dstSig s (Cst dstSig _ c) (Var dstSig _ v2))
        end
     | Var _ _ v1, Cst _ _ c =>
        match SV.In_dec v1 (exv s) with
          left h1 => eq_yd v1 h1 (Cst dstSig _ c)
        | right _ => Atom _ (Eq dstSig s (Var dstSig _ v1) (Cst dstSig _ c))
        end
     | Cst _ _ c1, Cst _ _ c2 => Atom _ (Eq dstSig s (Cst dstSig _ c1) (Cst dstSig _ c2))
     end.

  (*
    X^n (yi <> yj)
    (E^n_i yi -> not E^n_j yi) && (E^n_j yj -> not E^n_i yj)

    X^n (yi <> v)
    (E^n_i yi -> not E^n_i v)
    
    RQ: pas de X sur E
  *)
  
    Definition neq_abstract {s} (t1 t2: term srcSig s): formula dstSig :=
    match t1,t2 with
      Var _ _ v1, Var _ _ v2 =>
        match SV.In_dec v1 (exv s) with
          left h1 =>
            match SV.In_dec v2 (exv s) with
              left h2 => neq_yy v1 h1 v2 h2
            | right _ => neq_yd v1 h1 (Var dstSig _ v2)
            end
        | right _ =>
            match SV.In_dec v2 (exv s) with
              left h2 => neq_yd v2 h2 (Var dstSig _ v1)
            | right _ => Atom _ (NEq dstSig s (Var dstSig _ v1) (Var dstSig _ v2))
            end
        end
     | Cst _ _ c, Var _ _ v2 =>
        match SV.In_dec v2 (exv s) with
          left h2 => neq_yd v2 h2 (Cst dstSig _ c)
        | right _ => Atom _ (NEq dstSig s (Cst dstSig _ c) (Var dstSig _ v2))
        end
     | Var _ _ v1, Cst _ _ c =>
        match SV.In_dec v1 (exv s) with
          left h1 => neq_yd v1 h1 (Cst dstSig _ c)
        | right _ => Atom _ (NEq dstSig s (Var dstSig _ v1) (Cst dstSig _ c))
        end
     | Cst _ _ c1, Cst _ _ c2 => Atom _ (NEq dstSig s (Cst dstSig _ c1) (Cst dstSig _ c2))
     end.

  Definition at_abstract (a: atom srcSig): formula dstSig :=
    match a with
    | Literal _ a => lt_abstract a
    | NLiteral _ a => nlt_abstract a
    | Eq _ _ t1 t2 => eq_abstract t1 t2
    | NEq _ _ t1 t2 => neq_abstract t1 t2
    end.
  
  Fixpoint abstract (f: formula srcSig): isProp srcSig f -> vsSubset _ (free srcSig f) (vsUnion _ exv allv) -> formula dstSig :=
  match f return isProp srcSig f -> vsSubset _ (free srcSig f) (vsUnion _ exv allv) -> formula dstSig with
  | FTrue _ => fun hn fv => FTrue _
  | FFalse _ => fun hn fv => FFalse _
  | Atom _ a => fun hn fv => at_abstract a
  | And _ f1 f2 => fun hn fv => 
      And dstSig (abstract f1 (proj1 hn) (vsSubsetUnion_elim_l dstSig _ _ _ fv))
                   (abstract f2 (proj2 hn) (vsSubsetUnion_elim_r dstSig _ _ _ fv))
  | Or _ f1 f2 => fun hn fv => 
      Or dstSig (abstract f1 (proj1 hn) (vsSubsetUnion_elim_l dstSig _ _ _ fv))
                 (abstract f2 (proj2 hn) (vsSubsetUnion_elim_r dstSig _ _ _ fv))
  | Ex _ s v f | All _ s v f => fun hn fv => match hn with end
  | F _ f | G _ f => fun hn fv => match hn with end
  end.
    
  Program Definition tfr_dom (D: Dom srcSig): Dom dstSig := {|
    ssem s := ssem (Dom:=D) s;
    neDom s := neDom (Dom:=D) s;
  |}.
  
  Program Definition tfr_itp {D: Dom srcSig} (Itp: Interp D) (pe: nat -> pEnv D exv): Interp (tfr_dom D) := {|
    csem s c := csem (Interp:=Itp) c;
    psem p t := 
      match p with
        OldPred op => psem op t
      | NewPred s v h => fun args => args F1 = pe t s v h
      end
  |}.
  
  Definition get_pe {D: Dom srcSig} (env': Env dstSig (tfr_dom D)) : pEnv D allv :=
    fun s v h => env' s v.
  
  Lemma get_pe_pAdd: forall D (env: Env dstSig (tfr_dom D)) pe,
    get_pe (pAdd env pe) = pe.
  Proof.
    intros.
    apply functional_extensionality_dep; intro s.
    apply functional_extensionality_dep; intro v.
    apply functional_extensionality_dep; intro h.
    unfold get_pe,pAdd; simpl.
    destruct (SV.set_In_dec v (allv s)); auto.
    f_equal; apply proof_irrelevance.
    destruct (n h).
  Qed.
  
  Record isExtItp {D: Dom srcSig} (Itp: Interp D) (Itp': Interp (tfr_dom D)): Prop := {
    is_uniq: forall s v h (x y: ssem s) t, psem (Interp:=Itp') (NewPred s v h) t (fun _ => x) -> psem (Interp:=Itp') (NewPred s v h) t (fun _ => y) -> x = y;
    is_ne: forall s (v: variable s) h t, exists (d: ssem s), psem (Interp:=Itp') (NewPred s v h) t (fun _ => d);
    is_eqp: forall p a t, psem (Interp:=Itp) p a t <-> psem (Interp:=Itp') (OldPred p) a t;
    is_eqc: forall s (c: constant s), csem (Interp:=Itp) c = csem (Interp:=Itp') c
  }.
  
  Ltac psemTac :=
    match goal with
      H:psem _ _ ?sa |- psem _ _ ?sa' => assert (sa' = sa) as ae;
          try (rewrite ae; assumption); (apply functional_extensionality_dep; intros)
    end.

  Definition isExtEnv {D: Dom srcSig} (env: Env srcSig D) (env': Env dstSig (tfr_dom D)) :=
    forall s v, env s v = env' s v.

  Lemma isExtEnv_add: forall {D: Dom srcSig} s (v: variable s) d (env: Env srcSig D) (env': Env dstSig (tfr_dom D)), isExtEnv env env' ->
    isExtEnv (add srcSig v d env) (add (D:=tfr_dom D) dstSig v d env').
  Proof.
    repeat intro.
    unfold add; simpl.
    destruct (eq_dec s s0).
    subst s0.
    destruct (eq_dec v v0); auto.
    apply H.
  Qed.

  Lemma isExtEnv_iadd: forall {D: Dom srcSig} `(K: Finite) sk vk dk env env',
    isExtEnv env env' ->
      isExtEnv (iadd srcSig K sk vk dk env) (iadd (D:=tfr_dom D) dstSig K sk vk dk env').
  Proof.
    repeat intro.
    unfold iadd; simpl.
    match goal with |- match ?cnd with _=>_ end = match ?cnd' with _=>_ end => destruct cnd end.
    destruct s0; simpl in *; auto.
    apply H.
  Qed.
  
  Lemma tm_dst_sem: forall s (tm: term srcSig s) (D: Dom srcSig) (env: Env srcSig D) (env': Env dstSig (tfr_dom D)) (Itp: Interp D) (Itp': Interp (tfr_dom D)), 
    isExtItp Itp Itp' -> isExtEnv env env' ->
      (tm_sem srcSig (Itp:=Itp) env tm = tm_sem dstSig (Itp:=Itp') env' (tm_dstSig tm)).
  Proof.
    intros.
    destruct tm; simpl; intros; auto.
    apply (is_eqc _ _ H).
  Qed.
  
  Lemma lt_dst_sem: forall l t (D: Dom srcSig) (env: Env srcSig D) (env': Env dstSig (tfr_dom D)) (Itp: Interp D) (Itp': Interp (tfr_dom D)), 
    isExtItp Itp Itp' -> isExtEnv env env' ->
      (lt_sem srcSig (Itp:=Itp) env l t <-> lt_sem dstSig (Itp:=Itp') env' (lt_dstSig l) t).
  Proof.
    intros.
    destruct l; simpl; intros; auto.
    split; intro.
    rewrite (is_eqp _ _ H) in H1.
    psemTac.
    symmetry; apply (tm_dst_sem _ (t0 x) D); intros; auto.
    rewrite (is_eqp _ _ H).
    psemTac.
    apply (tm_dst_sem _ (t0 x) D env env'); intros; auto.
  Qed.

  Fixpoint noAllV `{Sg: Sig} (V: VarSet Sg) (f: formula Sg): Prop :=
    match f with
    | Ex _ s v f => noAllV V f
    | All _ s v f => not (vsIn Sg v V) /\ noAllV V f
    | And _ f1 f2 | Or _ f1 f2 => noAllV V f1 /\ noAllV V f2
    | _ => True
    end.

  Lemma at_dst_sem: forall a t (D: Dom srcSig) (env: Env srcSig D) (env': Env dstSig (tfr_dom D)) (Itp: Interp D) (Itp': Interp (tfr_dom D)), 
    isExtItp Itp Itp'  -> isExtEnv env env' ->
      (at_sem srcSig (Itp:=Itp) env a t <-> at_sem dstSig (Itp:=Itp') env' (at_dstSig a) t).
  Proof.
    intros; destruct a; simpl.
  - apply lt_dst_sem; auto.
  - apply not_iff_compat.
    apply lt_dst_sem; auto.
  - rewrite tm_dst_sem with (Itp':=Itp') (env':=env'); auto.
    rewrite tm_dst_sem with (Itp':=Itp') (env':=env'); auto.
    reflexivity.
  - rewrite tm_dst_sem with (Itp':=Itp') (env':=env'); auto.
    rewrite tm_dst_sem with (Itp':=Itp') (env':=env'); auto.
    apply not_iff_compat.
    reflexivity.
  Qed.
  
  Lemma fm_dst_sem: forall f (nfo: noFO srcSig f) t (D: Dom srcSig) (env: Env srcSig D) (env': Env dstSig (tfr_dom D)) (Itp: Interp D) (Itp': Interp (tfr_dom D)), 
    isExtItp Itp Itp'  -> isExtEnv env env' ->
      (fm_sem srcSig (Itp:=Itp) env f t <-> fm_sem dstSig (Itp:=Itp') env' (fm_dstSig f) t).
  Proof.
    intros.
    revert f nfo t env env' H H0.
    induction f; simpl; intros; auto; try tauto.
  - rewrite at_dst_sem with (env':=env'); auto.
    reflexivity.
    auto.
  - rewrite <-IHf1, <-IHf2; auto; try tauto; try reflexivity; auto.
  - rewrite <-IHf1, <-IHf2; auto; try tauto; try reflexivity; auto.
  - split; intros.
    destruct H1 as [t' [h1 h2]].
    exists t'; split; auto.
    revert h2; apply IHf; auto.
    destruct H1 as [t' [h1 h2]].
    exists t'; split; auto.
    revert h2; apply IHf; auto.
  - split; intros.
    generalize (H1 t' H2); apply IHf; auto.
    generalize (H1 t' H2); apply IHf; auto.
  Qed.

  Lemma not_not_iff: forall (P:Prop), not (not P) -> P.
  Proof.
    intro; tauto.
  Qed.

  Lemma pAdd_exv: forall (D: Dom srcSig) (env: Env srcSig D) env' s v, 
    SV.set_In v (exv s) -> pAdd env (get_pe env') s v = env s v.
  Proof.
    intros.
    unfold pAdd, get_pe.
    destruct (SV.set_In_dec v (allv s)); auto.
    destruct (ex_all_exc _ v (conj H i)).
  Qed.

  Lemma pAdd_nexv: forall (D: Dom srcSig) (env: Env srcSig D) env' s v
    (fv: SV.set_In v (vsUnion _ exv allv s)), 
    not (SV.set_In v (exv s)) -> pAdd env (get_pe env') s v = env' s v.
  Proof.
    intros.
    unfold pAdd, get_pe.
    destruct (SV.set_In_dec v (allv s)); auto.
    apply vsUnion_elim in fv; destruct fv; tauto.
  Qed.

  Definition ItpEnvSing {D: Dom srcSig} (env: nat -> Env srcSig D) (Itp': Interp (tfr_dom D)) t : Prop :=
    forall s v h (d: ssem (Sg:=dstSig) s), psem (Sg:=dstSig) (NewPred s v h) t (fun _ => d) -> env t s v = d.

  Lemma lt_abstract_sem: forall (D: Dom srcSig) (env: nat -> Env srcSig D) (Itp: Interp D) Itp' (hx: isExtItp Itp Itp') t (he: forall t, ItpEnvSing env Itp' t) l (fv: vsSubset _ (lt_vars _ l) (vsUnion _ exv allv)),
    forall env' : Env dstSig (tfr_dom D),
      lt_sem srcSig (pAdd (env t) (get_pe env')) l t ->
        fm_sem dstSig (Itp:=Itp') env' (lt_abstract l) t.
  Proof.
    intros.
    unfold lt_abstract.
    destruct l; auto.
    rewrite Or_sem.
    match goal with
      |- ?P \/ ?Q => destruct (classic P); [left;auto|right]
    end.
    unfold mk_disj in H0.
    setoid_rewrite IOr_sem in H0.
    generalize (not_ex_all_not _ _ H0); clear H0; intro.
    apply (is_eqp _ _ hx).
    fold (fm_sem dstSig (Itp:=Itp') ) in H0.
    simpl in H.
    psemTac.
    specialize H0 with x.
    simpl in fv.
    apply vsSubsetGUnion_elim with (k:=x) in fv.
    destruct (t0 x); simpl in *; auto.
    apply vsSubsetSing in fv.
    destruct (SV.In_dec e (exv (pr_args p x))); try tauto.
    simpl in H0.
    apply not_not_iff in H0.
    rewrite (pAdd_exv _ (env t) env' _ e s).
    apply he in H0.
    symmetry; apply H0.
    
    symmetry; apply (pAdd_nexv _ (env t) env' _ e fv n0).
    symmetry; apply (is_eqc Itp Itp' hx).
  Qed.

  Lemma nlt_abstract_sem: forall (D: Dom srcSig) (env: nat->Env srcSig D) (Itp: Interp D) Itp' (hx: isExtItp Itp Itp') t  (he: forall t, ItpEnvSing env Itp' t) l (fv: forall s, SV.subset (lt_vars _ l s) (vsUnion _ exv allv s)),
    forall env' : Env dstSig (tfr_dom D),
      not (lt_sem srcSig (pAdd (env t) (get_pe env')) l t) ->
        fm_sem dstSig (Itp:=Itp') env' (nlt_abstract l) t.
  Proof.
    intros.
    unfold nlt_abstract.
    destruct l.
    rewrite Or_sem; simpl in *.
    match goal with
      |- ?P \/ ?Q => destruct (classic P); [left;auto|right]
    end.
    unfold mk_disj in H0; setoid_rewrite IOr_sem in H0.
    generalize (not_ex_all_not _ _ H0); clear H0; intro.
    intro; apply H; clear H.
    apply (is_eqp _ _ hx) in H1.
    psemTac.
    specialize H0 with x.
    apply vsSubsetGUnion_elim with (k:=x) in fv.
    destruct (t0 x); simpl; auto.
    apply vsSubsetSing in fv.
    destruct (SV.In_dec e (exv (pr_args p x))); auto.
    simpl in H0.
    apply not_not_iff in H0.
    rewrite (pAdd_exv _ (env t) env' _ e s).
    apply he in H0.
    apply H0.
    apply (pAdd_nexv _ (env t) env' _ e fv n0).
    apply (is_eqc Itp Itp' hx).
  Qed.
  
  Lemma eq_abstract_sem:  forall (D: Dom srcSig) (env: nat->Env srcSig D) (Itp: Interp D) Itp' (hx: isExtItp Itp Itp') s (t1 t2: term srcSig s) t (he: forall t, ItpEnvSing env Itp' t) 
  (fv1: vsSubset _ (tm_vars _ t1) (vsUnion _ exv allv))
  (fv2: vsSubset _ (tm_vars _ t2) (vsUnion _ exv allv)),
    forall env' : Env dstSig (tfr_dom D),
      tm_sem srcSig (pAdd (env t) (get_pe env')) t1 = tm_sem srcSig (pAdd (env t) (get_pe env')) t2 ->
        fm_sem dstSig (Itp:=Itp') env' (eq_abstract t1 t2) t.
  Proof.
    intros.
    destruct t1; destruct t2; unfold eq_abstract; repeat (rewrite And_sem, Or_sem); auto.
    destruct (SV.In_dec e (exv s)).
    destruct (SV.In_dec e0 (exv s)).
    generalize (pAdd_exv D (env t) env' s e s0); intro.
    generalize (pAdd_exv D (env t) env' s e0 s1); intro.
    assert (env t s e = env t s e0).
    rewrite <-H0,<-H1.
    apply H.
    clear H H0 H1.
    unfold eq_yy.
    rewrite And_sem, Or_sem; rewrite Or_sem; simpl in *.
    split.
    match goal with |- not ?P \/ ?Q => elim (classic P); try tauto; right end.
    apply he in H.
    destruct (is_ne Itp Itp' hx _ e0 s1 t) as [d h].
    generalize h; intro h'.
    apply he in h'.
    rewrite <-H,H2,h'.
    apply h.

    match goal with |- not ?P \/ ?Q => elim (classic P); try tauto; right end.
    destruct (is_ne Itp Itp' hx _ e s0 t) as [d h].
    destruct (is_ne Itp Itp' hx _ e0 s1 t) as [d0 h0].
    generalize (is_uniq Itp Itp' hx _ e0 s1 _ _ t H h0); intro.
    apply he in h0.
    rewrite H0,<-h0; clear H0 h0 d0.
    generalize h; intro h'.
    apply he in h'.
    subst d.
    rewrite H2 in h; apply h.
    
    simpl in fv2; apply vsSubsetSing in fv2.
    assert (env t s e = env' s e0).
      rewrite <-pAdd_exv with (env:=env t) (env':=env') (v:=e); auto.
      rewrite <-pAdd_nexv with (env:=env t)(env':=env') (v:=e0); now auto.
    clear H.
    unfold eq_yd; simpl.
    rewrite <-H0.
    destruct (is_ne Itp Itp' hx _ e s0 t) as [d h].
    generalize h; intro h'.
    apply he in h'.
    subst d; apply h.
    
    simpl in fv1; apply vsSubsetSing in fv1.
    simpl in fv2; apply vsSubsetSing in fv2.
    destruct (SV.In_dec e0 (exv s)); auto.
    assert (env' s e = env t s e0).
      rewrite <-pAdd_nexv with (env:=env t) (env':=env') (v:=e); auto.
      rewrite <-pAdd_exv with (env:=env t) (env':=env') (v:=e0); now auto.
    unfold eq_yd; simpl.
    rewrite H0.
    destruct (is_ne Itp Itp' hx _ e0 s0 t) as [d h].
    generalize h; intro h'.
    apply he in h'.
    subst d; apply h.

    simpl.
    rewrite <-pAdd_nexv with (env:=env t) (env':=env') (v:=e); auto.
    rewrite <-pAdd_nexv with (env:=env t) (env':=env') (v:=e0); auto.
    
    destruct (SV.In_dec e (exv s)); auto.
    assert (env t s e = csem e0).
      rewrite <-pAdd_exv with (env:=env t) (env':=env') (v:=e); auto.
    unfold eq_yd; simpl.
    rewrite <-(is_eqc _ _ hx).
    rewrite <-H0.
    destruct (is_ne Itp Itp' hx _ e s0 t) as [d h].
    generalize h; intro h'.
    apply he in h'.
    subst d; apply h.
    
    simpl.
    simpl in fv1; apply vsSubsetSing in fv1.
    rewrite <-pAdd_nexv with (env:=env t) (env':=env') (v:=e); auto.
    rewrite <-(is_eqc _ _ hx).
    apply H.
    
    destruct (SV.In_dec e0 (exv s)).
    simpl.
    assert (csem e = env t s e0).
      rewrite <-pAdd_exv with (env:=env t) (env':=env') (v:=e0); auto.
    rewrite <-(is_eqc _ _ hx).
    rewrite H0.
    destruct (is_ne Itp Itp' hx _ e0 s0 t) as [d h].
    generalize h; intro h'.
    apply he in h'.
    subst d; apply h.

    simpl.
    simpl in fv2; apply vsSubsetSing in fv2.

    rewrite <-pAdd_nexv with (env:=env t) (env':=env') (v:=e0); auto.
    rewrite <-(is_eqc _ _ hx).
    apply H.

    simpl in *.
    rewrite <-(is_eqc _ _ hx).
    rewrite <-(is_eqc _ _ hx).
    apply H.
  Qed.
  
  Lemma neq_abstract_sem:  forall (D: Dom srcSig) (env: nat -> Env srcSig D) (Itp: Interp D) Itp' (hx: isExtItp Itp Itp') s (t1 t2: term srcSig s) t (he: forall t, ItpEnvSing env Itp' t)
  (fv1: forall s, SV.subset (tm_vars srcSig t1 s) (vsUnion _ exv allv s))
  (fv2: forall s, SV.subset (tm_vars srcSig t2 s) (vsUnion _ exv allv s)),
    forall env' : Env dstSig (tfr_dom D),
      tm_sem srcSig (pAdd (env t) (get_pe env')) t1 <> tm_sem srcSig (pAdd (env t) (get_pe env')) t2 ->
        fm_sem dstSig (Itp:=Itp') env' (neq_abstract t1 t2) t.
  Proof.
    intros.
    unfold neq_abstract.
    destruct t1; destruct t2; simpl in *.
    destruct (SV.In_dec e (exv s)).
    rewrite pAdd_exv with (v:=e) in H; auto.
    destruct (SV.In_dec e0 (exv s)).
    rewrite pAdd_exv with (v:=e0) in H; auto.
    unfold neq_yy.
    rewrite And_sem, Or_sem; rewrite Or_sem; simpl.
    split.
    match goal with |- not ?P \/ ?Q => destruct (classic P); try tauto end.
    right; intro; apply H; clear H.
    apply he in H1.
    apply he in H0.
    rewrite H1; apply H0.
    match goal with |- not ?P \/ ?Q => destruct (classic P); try tauto end.
    right; intro; apply H; clear H.
    apply he in H1; apply he in H0.
    rewrite H0; apply H1.
    
    simpl in fv2; apply vsSubsetSing in fv2.
    rewrite (pAdd_nexv D) with (v:=e0) in H; auto.
    unfold neq_yd; simpl; intro.
    apply he in H0.
    apply H; tauto.
    
    simpl in fv1; apply vsSubsetSing in fv1.
    rewrite (pAdd_nexv D) with (v:=e) in H; auto.
    destruct (SV.In_dec e0 (exv s)); simpl; auto.
    rewrite pAdd_exv with (v:=e0) in H; auto.
    intro.
    unfold neq_yd in H0; simpl in H0.
    apply he in H0.
    apply H; symmetry; apply H0.

    intro; apply H; clear H.
    simpl in fv2; apply vsSubsetSing in fv2.
    rewrite (pAdd_nexv D) with (v:=e0); now auto.

    destruct (SV.In_dec e (exv s)).
    rewrite pAdd_exv with (v:=e) in H; auto.
    unfold neq_yd; simpl; intro.
    apply he in H0.
    apply H; rewrite (is_eqc _ _ hx); apply H0.

    simpl in fv1; apply vsSubsetSing in fv1.
    rewrite (pAdd_nexv D) with (v:=e) in H; auto.
    simpl.
    rewrite <-(is_eqc _ _ hx); apply H.

    destruct (SV.In_dec e0 (exv s)).
    rewrite pAdd_exv with (v:=e0) in H; auto.
    unfold neq_yd; simpl; intro.
    apply he in H0.
    apply H; rewrite (is_eqc _ _ hx); symmetry; apply H0.

    simpl.
    simpl in fv2; apply vsSubsetSing in fv2.
    rewrite (pAdd_nexv D) with (v:=e0) in H; auto.
    rewrite <-(is_eqc _ _ hx); apply H.
    
    do 2 rewrite <-(is_eqc _ _ hx); apply H.
  Qed.

  Lemma at_abstract_sem: forall (D: Dom srcSig) Itp Itp' (hx: isExtItp Itp Itp') (env: nat->Env srcSig D) (he: forall t, ItpEnvSing env Itp' t) a (fv: vsSubset _ (at_free _ a) (vsUnion _ exv allv)),
    forall t env', 
      at_sem srcSig (Itp:=Itp) (pAdd (env t) (get_pe env')) a t ->
        fm_sem dstSig (Itp:=Itp') env' (at_abstract a) t.
  Proof.
    intros.
    destruct a; simpl.
    revert H; apply lt_abstract_sem; auto.
    revert H; apply nlt_abstract_sem; auto.
    revert H; apply eq_abstract_sem; auto.
      apply vsSubsetUnion_elim_l in fv; auto.
      apply vsSubsetUnion_elim_r in fv; auto.
    revert H; apply neq_abstract_sem; auto.
      apply vsSubsetUnion_elim_l in fv; auto.
      apply vsSubsetUnion_elim_r in fv; auto.
  Qed.

  (*
    |- (EX ALL phi) => ALL abs(phi)
  *)
  
  (*
    PB:
    G (EX ALL phi) : pour tout t, valuation des EX fixe dans le temps pour eval de phi
    G (ALL ALL abs(phi)) : abs(phi) evalue avec des predicats E variables dans le temps
    ==> nombre d'instants borne ==> F et G interdits
  *)
  Lemma abstract_sem: forall (D: Dom srcSig) Itp Itp' (hx: isExtItp Itp Itp') (env: nat->Env srcSig D) (he: forall t, ItpEnvSing env Itp' t) f (nfo: isProp srcSig f) (fv: vsSubset _ (free _ f) (vsUnion _ exv allv)),
    forall t env', 
      fm_sem srcSig (Itp:=Itp) (pAdd (env t) (get_pe env')) f t ->
        fm_sem dstSig (Itp:=Itp') env' (abstract f nfo fv) t.
  Proof.
    induction f; intros; try (simpl; tauto).
    - revert H; apply at_abstract_sem; eauto.
    - simpl in H.
      destruct H.
      split; [revert H; apply IHf1 | revert H0; apply IHf2]; intros; auto.
    - simpl in H.
      apply Or_sem.
      destruct H; [left; revert H; apply IHf1 | right; revert H; apply IHf2]; auto.
  Qed.
  
  End ExAll.
  
  Ltac psemTac :=
    match goal with
      H:psem _ _ ?sa |- psem _ _ ?sa' => assert (sa' = sa) as ae;
          try (rewrite ae; assumption); (apply functional_extensionality_dep; intros)
    end.
    
  Ltac fm_semTac :=
    match goal with
      H: fm_sem _ ?e1 ?f ?t |- fm_sem _ ?e2 ?f ?t => assert (e1 = e2) as eeq;
        try (rewrite eeq in H; assumption); 
        apply functional_extensionality_dep; intro; 
        apply functional_extensionality_dep; intro
    end.
    
  Lemma not_not: forall (P:Prop), ~ (~ P) <-> P.
  Proof.
    intros.
    tauto.
  Qed.
  
  Lemma fm_dst_EX: forall (f: formula srcSig) V,
    (fm_dstSig V (EX f)) = EX (fm_dstSig V f).
  Proof.
    induction f; simpl; intros; auto.
  Qed.

  Lemma fm_dst_ALL: forall (f: formula srcSig) V,
    (fm_dstSig V (ALL f)) = ALL (fm_dstSig V f).
  Proof.
    induction f; simpl; intros; auto.
  Qed.
  
  Lemma fm_dst_getALl: forall V (f: formula srcSig),
    getAll (fm_dstSig V f) = getAll f.
  Proof.
    induction f; simpl; intros; auto.
    rewrite IHf.
    reflexivity.
  Qed.
  
  Lemma pAdd_add: forall `(Sg: Sig) (D: Dom Sg) (env: Env Sg D) (V: VarSet Sg) s (d: ssem s) (v: variable s) (pe: pEnv D V) s' v',
  pAdd (add Sg v d env) pe s' v' =
  pAdd env
    (fun (s' : Sort) (v' : variable s')
         (h : SV.set_In v' (vsAdd Sg v V s')) =>
   match SV.In_dec v' (V s') with
   | left hi => pe s' v' hi
   | right hn =>
       match
         eq_sym (inj_pairT1 (vsAdd_ne2 Sg h hn)) in (_ = s'0)
         return (ssem s'0)
       with
       | eq_refl => d
       end
   end) s' v'.
  Proof.
    intros; unfold pAdd,add; simpl.
    destruct (SV.set_In_dec v' (vsAdd Sg v V s')).
    destruct (dec.isEq2_obligation_1 _ Sort _ (fun x : Sort => variable x) s' v' s
    v); auto.
    injection e; intros; subst s'.
    destruct (SV.set_In_dec v' (V s)).
    destruct (SV.In_dec v' (V s)); auto.
    f_equal; apply proof_irrelevance.
    destruct (n i0).
    destruct (eq_dec s s); try tauto.
    rewrite (proof_irrelevance _ _ eq_refl); auto.
    destruct (eq_dec v v'); auto.
    destruct (SV.In_dec v' (V s)); auto.
    destruct (n s0); auto.
    subst.
    rewrite (proof_irrelevance _ _ eq_refl); auto.

    exfalso; apply inj_pair2_eq_dec in e; try apply eq_dec; auto.
    unfold SV.In_dec; unfold SV.set_In_dec.
    destruct (List.in_dec eq_dec v' (V s')); auto.
    destruct (eq_dec s s').
    subst s'.
    destruct (eq_dec v v').
    subst v'.
    exfalso; apply n; auto.
    
    exfalso; apply vsAdd_elim in i.
    destruct i; try tauto.
    match goal with |- _=match ?cnd return _ with _=>_ end => destruct cnd end.
    tauto.
    
    destruct (SV.set_In_dec v' (V s')).
    exfalso; apply n.
    apply vsAdd_r; auto.
    destruct (eq_dec s s'); auto.
    subst s'.
    destruct (eq_dec v v'); auto.
    subst v'.
    exfalso; apply n.
    apply vsAdd_l.
  Qed.
  
  Lemma pAdd_split_eq: forall `(Sg: Sig) (D: Dom Sg) (env: Env Sg D) (V: VarSet Sg) s (v: variable s) (pe: pEnv D (vsAdd Sg v V)) s' v',
    pAdd env pe s' v' =
    pAdd (add Sg v (pe s v (vsAdd_l Sg v V)) env)
        (fun s w (h : SV.set_In w (V s)) => pe s w (vsAdd_r Sg v V h))
        s' v'.
  Proof.
    intros.
    unfold pAdd, add; simpl.
    destruct (SV.set_In_dec v' (V s')).
    destruct (SV.set_In_dec v' (vsAdd Sg v V s')).
    f_equal; apply proof_irrelevance.
    exfalso; apply n; clear n.
    apply vsAdd_r; auto.
    destruct (eq_dec s s'); try tauto.
    subst s'.
    destruct (eq_dec v v'); try tauto.
    subst v'.
    destruct (SV.set_In_dec v (vsAdd Sg v V s)).
    f_equal; apply proof_irrelevance.
    exfalso; apply n0; clear n0.
    apply vsAdd_l.
    
    destruct (SV.set_In_dec v' (vsAdd Sg v V s)); auto.
    exfalso; apply vsAdd_elim in i; destruct i; try tauto.
    simpl in H.
    apply inj_pair2_eq_dec in H; try apply eq_dec; subst v'; tauto.
    
    destruct (SV.set_In_dec v' (vsAdd Sg v V s')); auto.
    exfalso; apply vsAdd_elim in i; destruct i; try tauto.
    simpl in H.
    injection H; clear H; intros; subst; tauto.
  Qed.  

  Lemma vsVars_dst: forall `(K:Finite) V (sk:K->Sort (Sig:=srcSig)) (vk: forall k:K, variable (sk k)),
    forall s v, SV.set_In v (vsVars (dstSig V) vk s) <->
      SV.set_In v (vsVars srcSig vk s).
  Proof.
    intros; auto.
    unfold vsVars; split; intros.
    apply SV.InCUnion_elim in H.
    destruct H as [u [h1 [h2 h3]]].
    apply SV.InCUnion_intro with (u0:=u); auto.
    apply SV.InCUnion_elim in H.
    destruct H as [u [h1 [h2 h3]]].
    apply SV.InCUnion_intro with (u0:=u); auto.    
  Qed.

  Lemma tfr_itp_ext: forall (D: Dom srcSig) exs (Itp: Interp D) pe,
    isExtItp exs Itp (tfr_itp exs Itp pe).
  Proof.
    intros; split; simpl in *; intros; auto.
    subst y; tauto.
    exists (pe t s v h); reflexivity.
    reflexivity.
  Qed.

  Lemma imp_ex: forall {T} (t:T) (P: Prop)  (Q: T -> Prop), 
    (P -> exists x, Q x) <-> (exists x, P -> Q x).
  Proof.
    repeat intro; split; intros; auto.
    destruct (classic P).
    destruct (H H0).
    exists x; tauto.
    exists t; tauto.
    destruct H as [x h].
    exists x; tauto.
  Qed.

  Definition abstract_ExAll f (hf: isExAll _ f) (fv: forall s, SV.is_empty (free _ f s)) :=
    (mkAll (Sg:=dstSig (getExF f)) (getExF f) (mkAll (Sg:=dstSig (getExF f)) (getAll (EX f)) (abstract _ _ (EX_ALL f) (isExAll_Prop _ hf) (close_EXfALL fv) ))).
  
  Lemma abstract_EA_sem: forall (D: Dom srcSig) (f: formula srcSig) (hf: isExAll _ f) (fv: forall s, SV.is_empty (free _ f s)) (P: nat->Prop),
    forall env Itp,
    (forall t, P t -> fm_sem (Itp:=Itp) srcSig env f t) ->
      exists (Itp': Interp (tfr_dom (getExF f) D)),
        forall t, P t ->
        fm_sem (dstSig _) (Itp:=Itp') env (abstract_ExAll f hf fv) t.
  Proof.
    intros.
    setoid_rewrite mkEx_getExF in H; auto.
    generalize (fun t h => semEx_elim D env Itp (EX f) (getExF f) t (H t h));  clear H; intro.
    setoid_rewrite (imp_ex (fun s v h => env s v)) in H.
    
    apply functional_choice in H.
    destruct H as [pe H].
    setoid_rewrite <-ALL_sem in H; auto.

    set (Itp' := (tfr_itp (getExF f) Itp pe)).
    exists Itp'; intros t h.
    generalize (H t h); clear H; intro H.

    apply semAll_intro; intro; auto.
    apply semAll_intro; intro; auto.

    set (pe' := (pe1: pEnv D (getAll (EX f)))).
    apply semAll_elim with (pe2 := pe') in H.

    set (env' := (pAdd (pAdd env (pe t)) pe1)).
    assert (forall s : Sort, SV.disjoint (getExF f s) (getAll (EX f) s)) as disj.
      repeat intro.
      destruct H0.
      apply vsInter_elim in H0; destruct H0.
      apply (getAll_nfree _ _ _ (conj H1 H2)); tauto.
    apply (fun hx => abstract_sem (getExF f) (getAll (EX f)) disj D Itp Itp' hx (fun t => pAdd (pAdd env (pe t)) pe')); auto.
    
    apply tfr_itp_ext.

    repeat intro.
    simpl in H0; subst d.
    unfold pe'.
    unfold pAdd.
    destruct (SV.set_In_dec v (getAll (EX f) s)).
    destruct (disj s v (conj h0 i)).
    destruct (SV.set_In_dec v (getExF f s)); try tauto.
    f_equal; apply proof_irrelevance.
    
    rewrite (get_pe_pAdd _ _ D).
    unfold EX_ALL.
    fm_semTac.
    rewrite pAdd2.
    reflexivity.
  Qed.

  Lemma abstract_GEA_sem: forall (D: Dom srcSig) (f: formula srcSig) (hf: isExAll _ f) (fv: forall s, SV.is_empty (free _ f s)),
    forall Itp,
    forall env t, 
      fm_sem srcSig (Itp:=Itp) env (G _ f) t ->
        exists (Itp': Interp (tfr_dom (getExF f) D)),
        fm_sem (dstSig _) (Itp:=Itp') env
          (G _ (abstract_ExAll f hf fv)) t.
  Proof.
    intros.
    rewrite G_sem in H; intros.
    setoid_rewrite G_sem.
    generalize (abstract_EA_sem D f hf); intro.
    unfold getExAll in H0.
    apply (H0 fv (fun t' => t' >= t) env Itp); auto.
  Qed.

  Theorem abstraction_OK: forall (f: formula srcSig) (hf: isExAll _ f) (fv: forall s, SV.is_empty (free _ f s)),
    isSat srcSig (G _ f) -> 
      isSat (dstSig (getExF f)) (G _ (abstract_ExAll f hf fv)).
  Proof.
    intros.
    unfold getExAll; intros.
    destruct H as [D [Itp [env [t H]]]].
    exists (tfr_dom (getExF f) D).
    apply abstract_GEA_sem with (fv:=fv) (hf:=hf) in H.
    destruct H as [itp' H].
    exists itp'.
    exists env.
    exists t.
    apply H.
  Qed.

End Abstraction.
