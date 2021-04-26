
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
Require Import fosem.

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

  Definition newPredSet : SV.set newPredDec.
    apply SV.GUnion with (d:=@fin_set _ Sort).
    apply fin_set.
    intros s hs.
    apply SV.GUnion with (d:=@fin_set _ (variable s)).
    apply fin_set.
    intros v hv.
    destruct (SV.set_In_dec v (exv s)).
    exact (SV.sing newPredDec (NewPred s v i)).
    exact (SV.empty newPredDec).
  Defined.
    
  Program Definition newPredFin: @Finite newPred := {| 
    fin_dec := newPredDec;
    fin_set := SV.union (SV.image OldPred fin_set) newPredSet            
  |}.
  Next Obligation.
    destruct x.
    apply SV.InUnion_l.
    apply SV.InImage_intro with (w:=p); auto.
    apply fin_all.
    apply SV.InUnion_r.
    apply SV.InCUnion_intro with (u:=s); intros; try apply fin_all.
    apply SV.InCUnion_intro with (u:=v); intros; try apply fin_all.
    simpl.
    destruct (SV.set_In_dec v (exv s)).
    apply SV.InSing.
    rewrite (proof_irrelevance _ i h); now auto.
    destruct (n h).
  Qed.
  
  Definition dstTa (p:newPred): Type := 
    match p with OldPred op => Fin.t (pr_arity op) | NewPred _ _ _ => One end.

  Definition dstSig: Sig := {|
    Sort := Sort (Sig:=srcSig);
    variable s := SumFin (variable (Sig:=srcSig) s) TwoFin;
    constant := constant (Sig:=srcSig);
    predicate := newPredFin;
    pr_arity p := match p with OldPred op => pr_arity op | NewPred _ _ _ => 1 end;
    pr_args p := match p with OldPred op => pr_args op | NewPred s _ _ => fun i => s end
  |}.

  Definition tm_dstSig {s} (tm: term srcSig s): term dstSig s :=
    match tm with
      Var _ _ v => Var dstSig s (inl v)
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
    | All _ s v f => All dstSig s (inl v) (fm_dstSig f)
    | Ex _ s v f => Ex dstSig s (inl v) (fm_dstSig f)
    | F _ f => F dstSig (fm_dstSig f)
    | G _ f => G dstSig (fm_dstSig f)
    end.

  Definition tm_abstract_U {s} (tm: term srcSig s): term dstSig s :=
  match tm with
    Var _ _ v => Var dstSig s (inl v)
  | Cst _ _ c => Cst dstSig s c
  end.

  Definition Ed {s} (v: variable s) (h: SV.set_In v (exv s)) (d: term dstSig s) :=
    PApp dstSig 0 (NewPred s v h) (fun i => d).
  
  Definition Ey {s} (v: variable s) (h: SV.set_In v (exv s)) (w: variable s) :=
    Ed v h (Var dstSig s (inl w)).
  
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


(* Definition 22 *)
  Definition AxE : formula dstSig :=
    G dstSig
      (IAnd dstSig Sort (fun s =>
        (IAnd dstSig (asFinite (exv s)) (fun v =>
          (All dstSig s (inr true) (All dstSig s (inr false) 
            (Imp dstSig
              (And dstSig
                (Atom _ (Literal _ (Ed (proj1_sig v) (InFin _ v) (Var dstSig s (inr true)))))
                (Atom _ (Literal _ (Ed (proj1_sig v) (InFin _ v) (Var dstSig s (inr false))))))
              (Atom _ (Eq dstSig s (Var dstSig s (inr true)) (Var dstSig s (inr false))))))))))).
  
  (*
    X^n p(.. yi ..)_{i in I}
    /\_{i in I} E^n_i(yi) -> X^n p(.. yi ..)
    RQ: pas de X sur E
  *)
  
  Definition lt_abstract_U (a: literal srcSig) :=
    match a with
      PApp _ n p args => 
        Or dstSig
          (mk_disj args)
          (Atom _ (Literal _ (PApp dstSig n (OldPred p) (fun i => tm_abstract_U (args i)))))
    end.

  (*
    X^n -p(.. yi ..)_{i in I}
    /\_{i in I} E^n_i(yi) -> X^n -p(.. yi ..)
    RQ: pas de X sur E
  *)

  Definition nlt_abstract_U (a: literal srcSig) :=
    match a with
      PApp _ n p args => 
        Or dstSig
          (mk_disj args)
          (Atom _ (NLiteral _ (PApp dstSig n (OldPred p) (fun i => tm_abstract_U (args i)))))
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
  Definition eq_abstract_U {s} (t1 t2: term srcSig s): formula dstSig :=
    match t1,t2 with
      Var _ _ v1, Var _ _ v2 =>
        match SV.In_dec v1 (exv s) with
          left h1 =>
            match SV.In_dec v2 (exv s) with
              left h2 => eq_yy v1 h1 v2 h2
            | right _ => eq_yd v1 h1 (Var dstSig _ (inl v2))
            end
        | right _ =>
            match SV.In_dec v2 (exv s) with
              left h2 => eq_yd v2 h2 (Var dstSig _ (inl v1))
            | right _ => Atom _ (Eq dstSig s (Var dstSig _ (inl v1)) (Var dstSig _ (inl v2)))
            end
        end
     | Cst _ _ c, Var _ _ v2 =>
        match SV.In_dec v2 (exv s) with
          left h2 => eq_yd v2 h2 (Cst dstSig _ c)
        | right _ => Atom _ (Eq dstSig s (Cst dstSig _ c) (Var dstSig _ (inl v2)))
        end
     | Var _ _ v1, Cst _ _ c =>
        match SV.In_dec v1 (exv s) with
          left h1 => eq_yd v1 h1 (Cst dstSig _ c)
        | right _ => Atom _ (Eq dstSig s (Var dstSig _ (inl v1)) (Cst dstSig _ c))
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
  
    Definition neq_abstract_U {s} (t1 t2: term srcSig s): formula dstSig :=
    match t1,t2 with
      Var _ _ v1, Var _ _ v2 =>
        match SV.In_dec v1 (exv s) with
          left h1 =>
            match SV.In_dec v2 (exv s) with
              left h2 => neq_yy v1 h1 v2 h2
            | right _ => neq_yd v1 h1 (Var dstSig _ (inl v2))
            end
        | right _ =>
            match SV.In_dec v2 (exv s) with
              left h2 => neq_yd v2 h2 (Var dstSig _ (inl v1))
            | right _ => Atom _ (NEq dstSig s (Var dstSig _ (inl v1)) (Var dstSig _ (inl v2)))
            end
        end
     | Cst _ _ c, Var _ _ v2 =>
        match SV.In_dec v2 (exv s) with
          left h2 => neq_yd v2 h2 (Cst dstSig _ c)
        | right _ => Atom _ (NEq dstSig s (Cst dstSig _ c) (Var dstSig _ (inl v2)))
        end
     | Var _ _ v1, Cst _ _ c =>
        match SV.In_dec v1 (exv s) with
          left h1 => neq_yd v1 h1 (Cst dstSig _ c)
        | right _ => Atom _ (NEq dstSig s (Var dstSig _ (inl v1)) (Cst dstSig _ c))
        end
     | Cst _ _ c1, Cst _ _ c2 => Atom _ (NEq dstSig s (Cst dstSig _ c1) (Cst dstSig _ c2))
     end.

  Definition at_abstract_U (a: atom srcSig): formula dstSig :=
    match a with
    | Literal _ a => lt_abstract_U a
    | NLiteral _ a => nlt_abstract_U a
    | Eq _ _ t1 t2 => eq_abstract_U t1 t2
    | NEq _ _ t1 t2 => neq_abstract_U t1 t2
    end.

  Definition vsMap (f : forall s, variable (Sig:=srcSig) s -> variable (Sig:=dstSig) s) e: VarSet dstSig := fun s => List.map (f s) (e s).
  
  Lemma vsSubset_map: forall {e1 e2}, vsSubset srcSig e1 e2 -> vsSubset dstSig (vsMap (fun s => inl) e1) (vsMap (fun s => inl) e2).
  Proof.
    unfold vsMap; repeat intro.
    apply List.in_map_iff in H0.
    destruct H0 as [x [h1 h2]]; subst v.
    apply List.in_map_iff.
    exists x; split; auto.
    apply H in h2; auto.
  Qed.

  Lemma vsMap_In_intro: forall  (f : forall s, variable (Sig:=srcSig) s -> variable (Sig:=dstSig) s) {s v e},
    vsIn srcSig v e -> vsIn dstSig (f s v) (vsMap f e).
  Proof.
    unfold vsIn, vsMap; intros.
    apply List.in_map_iff.
    exists v; split; auto.
  Qed.
  
  Lemma vsUnion_map_l: forall  (f : forall s, variable (Sig:=srcSig) s -> variable (Sig:=dstSig) s) {e e1 e2},
    vsSubset _ (vsUnion srcSig e1 e2) e -> vsSubset _ (vsUnion dstSig (vsMap f e1) (vsMap f e2)) (vsMap f e) .
  Proof.
    repeat intro.
    apply (vsUnion_elim dstSig) in H0.
    destruct H0; apply List.in_map_iff in H0; destruct H0 as [x [h1 h2]]; subst v;
      apply List.in_map_iff; exists x; split; auto; apply H.
    now apply vsUnion_l.
    now apply vsUnion_r.
  Qed.
  
  Lemma vsUnion_map_r: forall  (f : forall s, variable (Sig:=srcSig) s -> variable (Sig:=dstSig) s) {e e1 e2},
    vsSubset _ e (vsUnion srcSig e1 e2) -> vsSubset _ (vsMap f e) (vsUnion dstSig (vsMap f e1) (vsMap f e2)).
  Proof.
    repeat intro.
    apply List.in_map_iff in H0.
    destruct H0 as [x [h1 h2]]; subst v.
    apply H in h2.
    apply vsUnion_elim in h2.
    destruct h2; [apply SV.InUnion_l | apply SV.InUnion_r]; apply List.in_map_iff; exists x; auto.
  Qed.
  
  Definition isInj {T1 T2} (f: T1 -> T2) := forall x1 x2, f x1 = f x2 -> x1 = x2.
  
  Lemma vsMap_add: forall s (v: variable s) (f: forall s, variable (Sig:=srcSig) s -> variable (Sig:=dstSig) s) (hf: forall s, isInj (f s)) e, 
    vsAdd dstSig (f s v) (vsMap f e) = vsMap f (vsAdd srcSig v e).
  Proof.
    intros.
    apply functional_extensionality_dep; intros s'.
    unfold vsMap, vsAdd; simpl.
    destruct (eq_dec s s'); auto.
    subst s'.
    generalize (hf s); generalize (f s); intros g hg; clear hf f.
    generalize (e s); clear e; intro l.
    induction l; simpl; intros; auto.
    destruct (eq_dec v a).
    subst a.
    destruct (dec.SumDec_obligation_1 (Tv s) (variable s) bool TwoDec (g v) (g v)); tauto.
    simpl; rewrite <-IHl; clear IHl.
    destruct (dec.SumDec_obligation_1 (Tv s) (variable s) bool TwoDec (g v) (g a)); auto.
    apply hg in e; tauto.
  Qed.

  Lemma vsMap_In_elim: forall  (f : forall s, variable (Sig:=srcSig) s -> variable (Sig:=dstSig) s) {s v e},
    (forall s, isInj (f s)) -> vsIn dstSig (f s v) (vsMap f e) -> vsIn srcSig v e.
  Proof.
    unfold vsIn, vsMap; intros.
    apply List.in_map_iff in H0.
    destruct H0 as [x [h1 h2]].
    apply H in h1; subst x; auto.
  Qed.

  Lemma vsMap_In_ran: forall  (f : forall s, variable (Sig:=srcSig) s -> variable (Sig:=dstSig) s) {s v e},
    vsIn dstSig v (vsMap f e) -> exists v', v = f s v'.
  Proof.
    unfold vsIn, vsMap; intros.
    apply List.in_map_iff in H.
    destruct H as [x [h1 h2]].
    exists x; symmetry; auto.
  Qed.

  Lemma vsMap_Union: forall  (f : forall s, variable (Sig:=srcSig) s -> variable (Sig:=dstSig) s) {e1 e2}, (forall s, isInj (f s)) -> forall s' (v': variable (Sig:=dstSig) s'),
    vsIn _ v' (vsMap f (vsUnion srcSig e1 e2)) <-> vsIn _ v' (vsUnion dstSig (vsMap f e1) (vsMap f e2)).
  Proof.
    intros.
    split; intro.
    destruct (vsMap_In_ran f H0) as [v h]; subst v'.
    apply (vsMap_In_elim f) in H0; auto.
    apply vsUnion_elim in H0.
    destruct H0; [apply vsUnion_l | apply vsUnion_r]; apply vsMap_In_intro; auto.

    apply vsUnion_elim in H0; destruct H0.
    destruct (vsMap_In_ran f H0) as [v h]; subst v'.
    apply vsMap_In_elim in H0; auto.
    apply vsMap_In_intro; apply vsUnion_l; apply H0.

    destruct (vsMap_In_ran f H0) as [v h]; subst v'.
    apply vsMap_In_elim in H0; auto.
    apply vsMap_In_intro; apply vsUnion_r; apply H0.
  Qed.

  Lemma vsMap_Inter: forall  (f : forall s, variable (Sig:=srcSig) s -> variable (Sig:=dstSig) s) {e1 e2}, (forall s, isInj (f s)) -> forall s' (v': variable (Sig:=dstSig) s'),
    vsIn _ v' (vsMap f (vsInter srcSig e1 e2)) <-> vsIn _ v' (vsInter dstSig (vsMap f e1) (vsMap f e2)).
  Proof.
    intros.
    split; intro.
    destruct (vsMap_In_ran f H0) as [v h]; subst v'.
    apply (vsMap_In_elim f) in H0; auto.
    apply vsInter_elim in H0; destruct H0.
    apply vsInter_intro; apply vsMap_In_intro; auto.

    apply vsInter_elim in H0; destruct H0.
    destruct (vsMap_In_ran f H0) as [v h]; subst v'.
    apply vsMap_In_intro.
    apply (vsMap_In_elim f H) in H0.
    apply (vsMap_In_elim f H) in H1.
    apply vsInter_intro; auto.
  Qed.
  
  Lemma vsMap_Remove: forall  (f : forall s, variable (Sig:=srcSig) s -> variable (Sig:=dstSig) s) {s v} {e}, (forall s, isInj (f s)) -> forall s' (v': variable (Sig:=dstSig) s'),
    vsIn _ v' (vsMap f (vsRemove srcSig v e)) <-> vsIn _ v' (vsRemove dstSig (f s v) (vsMap f e)).
  Proof.
    intros; split; intro.
    destruct (vsMap_In_ran _ H0) as [w h]; subst v'.
    apply (vsMap_In_elim f) in H0; auto.
    apply vsInRemove_elim in H0.
    apply vsInRemove_intro; auto.
    apply vsMap_In_intro; tauto.
    intro; apply proj2 in H0; apply H0; clear H0.
    inversion H1; clear H1; intros; subst s'.
    apply inj_pair2_eq_dec in H3; try apply eq_dec.
    apply (H s) in H3; subst w; constructor.
    
    apply vsInRemove_elim in H0; destruct H0.
    destruct (vsMap_In_ran _ H0) as [w h]; subst v'.
    apply (vsMap_In_elim f) in H0; auto.
    apply vsMap_In_intro; auto.
    apply vsInRemove_intro; auto.
    intro; apply H1; clear H1.    
    inversion H2; clear H2; intros; subst s'; auto.
    constructor.
  Qed.
  
  Fixpoint abstract_U (f: formula srcSig): isProp srcSig f -> vsSubset _ (free srcSig f) (vsUnion _ exv allv) -> formula dstSig :=
  match f return isProp srcSig f -> vsSubset _ (free srcSig f) (vsUnion _ exv allv) -> formula dstSig with
  | FTrue _ => fun hn fv => FTrue _
  | FFalse _ => fun hn fv => FFalse _
  | Atom _ a => fun hn fv => at_abstract_U a
  | And _ f1 f2 => fun hn fv => 
      And dstSig (abstract_U f1 (proj1 hn) (vsSubsetUnion_elim_l _ _ _ _ fv))
                   (abstract_U f2 (proj2 hn) (vsSubsetUnion_elim_r _ _ _ _ fv))
  | Or _ f1 f2 => fun hn fv => 
      Or dstSig (abstract_U f1 (proj1 hn) (vsSubsetUnion_elim_l _ _ _ _ fv))
                 (abstract_U f2 (proj2 hn) (vsSubsetUnion_elim_r _ _ _ _ fv))
  | Ex _ s v f | All _ s v f => fun hn fv => match hn with end
  | F _ f | G _ f => fun hn fv => match hn with end
  end.

  Lemma free_tm_dstSig {s} (tm: term srcSig s) s' (v': variable (Sig:=dstSig) s'):
    vsIn _ v' (tm_vars _ (tm_dstSig tm)) <-> vsIn _ v' (vsMap (fun s v => inl v) (tm_vars _ tm)).
  Proof.
    destruct tm; simpl; auto; split; intro.
    apply vsSing_elim in H.
    inversion H; clear H; subst s'.
    apply inj_pair2_eq_dec in H2; try apply eq_dec; subst v'.
    apply (vsMap_In_intro (fun s v=>inl v)).
    apply vsSing_intro.
    destruct v'.
    apply (vsMap_In_elim (fun s v => inl v)) in H.
    apply vsSing_elim in H.
    injection H; clear H; intros; subst s'.
    apply inj_pair2_eq_dec in H; try apply eq_dec; subst e0.
    apply vsSing_intro.
    repeat intro; injection H0; tauto.
    apply vsMap_In_ran in H.
    destruct H as [v' H]; discriminate.
    destruct H.
    destruct H.
  Qed.
  
  Lemma free_lt_dstSig (l: literal srcSig) s' (v': variable (Sig:=dstSig) s'):
    vsIn _ v' (lt_vars _ (lt_dstSig l)) <-> vsIn _ v' (vsMap (fun s v => inl v) (lt_vars _ l)).
  Proof.
    intros; destruct l; simpl; auto.
    split; intros.
    apply vsGUnion_elim in H; destruct H as [i H].
    rewrite free_tm_dstSig in H.
    destruct (vsMap_In_ran (fun s v => inl v) H) as [v H1]; subst v'.
    apply (vsMap_In_intro (fun s v => inl v)).
    apply vsGUnion_intro with (k:=i); auto.
    apply (vsMap_In_elim (fun s v=>inl v)) in H; auto.
    repeat intro.
    injection H0; tauto.

    destruct (vsMap_In_ran (fun s v => inl v) H) as [v H1]; subst v'.
    apply (vsMap_In_elim (fun s v => inl v)) in H.
    apply vsGUnion_elim in H; destruct H as [i H].
    apply vsGUnion_intro with (k:=i); auto.
    apply free_tm_dstSig; auto.
    apply (vsMap_In_intro (fun s v => inl v)); auto.
    repeat intro.
    injection H0; tauto.
  Qed.
  
  Lemma free_at_dstSig (a: atom srcSig) s' (v': variable (Sig:=dstSig) s'):
    vsIn _ v' (at_vars _ (at_dstSig a)) <-> vsIn _ v' (vsMap (fun s v => inl v) (at_vars _ a)).
  Proof.
    destruct a; simpl; auto.
    apply free_lt_dstSig.
    apply free_lt_dstSig.
    rewrite vsMap_Union.
    split; intro.
    apply vsUnion_elim in H; destruct H; [apply vsUnion_l | apply vsUnion_r].
    apply free_tm_dstSig; apply H.
    apply free_tm_dstSig; apply H.

    apply vsUnion_elim in H; destruct H; [apply vsUnion_l | apply vsUnion_r].
    apply free_tm_dstSig; apply H.
    apply free_tm_dstSig; apply H.
    repeat intro; injection H; tauto.
    
    rewrite vsMap_Union.
    split; intro.
    apply vsUnion_elim in H; destruct H; [apply vsUnion_l | apply vsUnion_r].
    apply free_tm_dstSig; apply H.
    apply free_tm_dstSig; apply H.

    apply vsUnion_elim in H; destruct H; [apply vsUnion_l | apply vsUnion_r].
    apply free_tm_dstSig; apply H.
    apply free_tm_dstSig; apply H.
    repeat intro; injection H; tauto.
  Qed.

  Lemma free_dstSig (f: formula srcSig) s' (v': variable (Sig:=dstSig) s'):
    vsIn _ v' (free _ (fm_dstSig f)) <-> vsIn _ v' (vsMap (fun s v => inl v) (free _ f)).
  Proof.
    induction f; simpl; intros; auto.
    - split; intro; destruct H.
    - split; intro; destruct H.
    - apply free_at_dstSig.
    - rewrite vsMap_Union, vsUnion_equiv.
      rewrite IHf1, IHf2.
      rewrite vsUnion_equiv; tauto.
      repeat intro; injection H; tauto.
    - rewrite vsMap_Union, vsUnion_equiv.
      rewrite IHf1, IHf2.
      rewrite vsUnion_equiv; tauto.
      repeat intro; injection H; tauto.
    - rewrite vsMap_Remove.
      do 2 rewrite vsRemove_equiv.
      rewrite IHf.
      tauto.
      repeat intro; injection H; tauto.
    - rewrite vsMap_Remove.
      do 2 rewrite vsRemove_equiv.
      rewrite IHf.
      tauto.
      repeat intro; injection H; tauto.
  Qed.

  Lemma free_disj: forall p (a: forall i, term _ (pr_args p i)) s (v: variable s), vsIn _ v (free _ (mk_disj a)) -> exists v', v = inl v' /\ exists i, vsIn _ v' (tm_vars _ (a i)).
  Proof.
    unfold mk_disj; simpl; intros.
    apply free_IOr_sub in H.
    apply (vsGUnion_elim dstSig) in H; destruct H as [k H].
    destruct (a k) eqn:ak.
    destruct (SV.In_dec e (exv (pr_args p k))); try tauto.
    simpl in H.
    apply vsGUnion_elim in H; destruct H as [i H].
    apply vsSing_elim in H.
    inversion H; clear H; subst s; apply inj_pair2_eq_dec in H2; try apply eq_dec; subst v.
    exists e; split; auto.
    exists k.
    rewrite ak; simpl.
    apply vsSing_intro.
    destruct H.
  Qed.

  Lemma free_tm_abstract_U: forall s (tm: term _ s) s' (v: variable s'), vsIn _ v (tm_vars _ (tm_abstract_U tm)) -> exists v', v=inl v' /\ vsIn _ v' (tm_vars _ tm).
  Proof.
    intros; destruct tm; simpl in *.
    apply vsSing_elim in H.
    inversion H; clear H; subst s'; apply inj_pair2_eq_dec in H2; try apply eq_dec; subst v.
    exists e; split; auto; apply vsSing_intro.
    destruct H.
  Qed.

  Lemma free_lt_abstract_U: forall l s (v: variable s), vsIn _ v (free _ (lt_abstract_U l)) -> exists v', v=inl v' /\ vsIn _ v' (lt_vars _ l).
  Proof.
    intros; destruct l; simpl in *.
    apply vsUnion_elim in H; destruct H.
    apply free_disj in H.
    destruct H as [v' [h H]]; subst v.
    destruct H as [i H].
    exists v'; split; auto.
    apply vsGUnion_intro with (k:=i); apply H.
    
    apply (vsGUnion_elim dstSig) in H; destruct H as [k H].
    simpl in H.
    apply free_tm_abstract_U in H.
    destruct H as [v' [h H]]; subst v.
    exists v'; split; auto.
    apply vsGUnion_intro with (k0:=k); apply H.
  Qed.
  
  Lemma free_nlt_abstract_U: forall l s (v: variable s), vsIn _ v (free _ (nlt_abstract_U l)) -> exists v', v=inl v' /\ vsIn _ v' (lt_vars _ l).
  Proof.
    intros; destruct l; simpl in *.
    apply vsUnion_elim in H; destruct H.
    apply free_disj in H.
    destruct H as [v' [h H]]; subst v.
    destruct H as [i H].
    exists v'; split; auto.
    apply vsGUnion_intro with (k:=i); apply H.
    
    apply (vsGUnion_elim dstSig) in H; destruct H as [k H].
    simpl in H.
    apply free_tm_abstract_U in H.
    destruct H as [v' [h H]]; subst v.
    exists v'; split; auto.
    apply vsGUnion_intro with (k0:=k); apply H.
  Qed.

  Lemma free_eq_yd: forall s (v1: variable s) (h1:vsIn _ v1 exv) (tm: term dstSig s) s' (v: variable s'),
    vsIn _ v (free _ (eq_yd v1 h1 tm)) -> vsIn _ v (vsSing _ (inl v1)) \/ vsIn _ v (tm_vars _ tm).
  Proof.
    unfold eq_yd; simpl; intros.
    apply vsGUnion_elim in H; destruct H as [k H].
    right; auto.
  Qed.
  
  Lemma free_eq_yy: forall s (v1 v2: variable s) (h1:vsIn _ v1 exv) (h2: vsIn _ v2 exv) s' (v: variable s'),
    vsIn _ v (free _ (eq_yy v1 h1 v2 h2)) -> vsIn _ v (vsSing _ (inl v1)) \/ vsIn _ v (vsSing _ (inl v2)).
  Proof.
    unfold eq_yy; simpl; intros.
    apply vsUnion_elim in H; destruct H; [left|right].
    apply (vsUnion_elim dstSig) in H; destruct H; apply (vsGUnion_elim dstSig) in H; destruct H as [k H]; apply H.
    apply (vsUnion_elim dstSig) in H; destruct H; apply (vsGUnion_elim dstSig) in H; destruct H as [k H]; apply H.
  Qed.
  
  Lemma free_eq_abstract_U: forall s (t1 t2: term _ s) s' (v: variable s'), vsIn _ v (free _ (eq_abstract_U t1 t2)) -> exists v', v=inl v' /\ vsIn _ v' (vsUnion _ (tm_vars _ t1) (tm_vars _ t2)).
  Proof.
    intros.
    destruct t1; destruct t2; simpl in *.
    destruct (SV.In_dec e (exv s)).
    destruct (SV.In_dec e0 (exv s)).
    unfold eq_abstract_U in H.
    apply free_eq_yy in H; destruct H; apply vsSing_elim in H.
    inversion H; clear H; subst s'; apply inj_pair2_eq_dec in H2; try apply eq_dec; subst v.
    exists e; split; auto; apply vsUnion_l; apply vsSing_intro.
    inversion H; clear H; subst s'; apply inj_pair2_eq_dec in H2; try apply eq_dec; subst v.
    exists e0; split; auto; apply vsUnion_r; apply vsSing_intro.
    apply free_eq_yd in H; destruct H.
    apply vsSing_elim in H.
    inversion H; clear H; subst s'; apply inj_pair2_eq_dec in H2; try apply eq_dec; subst v.
    exists e; split; auto; apply vsUnion_l; apply vsSing_intro.
    simpl in H.
    apply vsSing_elim in H.
    inversion H; clear H; subst s'; apply inj_pair2_eq_dec in H2; try apply eq_dec; subst v.
    exists e0; split; auto; apply vsUnion_r; apply vsSing_intro.

    destruct (SV.In_dec e0 (exv s)).
    apply free_eq_yd in H; destruct H.
    apply vsSing_elim in H.
    inversion H; clear H; subst s'; apply inj_pair2_eq_dec in H2; try apply eq_dec; subst v.
    exists e0; split; auto; apply vsUnion_r; apply vsSing_intro.
    simpl in H.
    apply vsSing_elim in H.
    inversion H; clear H; subst s'; apply inj_pair2_eq_dec in H2; try apply eq_dec; subst v.
    exists e; split; auto; apply vsUnion_l; apply vsSing_intro.

    simpl in H.
    apply vsUnion_elim in H; destruct H; apply (vsSing_elim dstSig) in H.
    inversion H; clear H; subst s'; apply inj_pair2_eq_dec in H2; try apply eq_dec; subst v.
    exists e; split; auto; apply vsUnion_l; apply vsSing_intro.
    inversion H; clear H; subst s'; apply inj_pair2_eq_dec in H2; try apply eq_dec; subst v.
    exists e0; split; auto; apply vsUnion_r; apply vsSing_intro.
    
    destruct (SV.In_dec e (exv s)).
    apply free_eq_yd in H; destruct H.
    apply vsSing_elim in H.
    inversion H; clear H; subst s'; apply inj_pair2_eq_dec in H2; try apply eq_dec; subst v.
    exists e; split; auto; apply vsUnion_l; apply vsSing_intro.
    simpl in H.
    destruct H.
    simpl in H.
    apply vsUnion_elim in H; destruct H; try (now destruct H).
    apply (vsSing_elim dstSig) in H.
    inversion H; clear H; subst s'; apply inj_pair2_eq_dec in H2; try apply eq_dec; subst v.
    exists e; split; auto; apply vsUnion_l; apply vsSing_intro.
    
    destruct (SV.In_dec e0 (exv s)); simpl in H.
    apply vsGUnion_elim in H; destruct H as [k H]; destruct H.

    apply vsUnion_elim in H; destruct H; try (now destruct H).
    apply (vsSing_elim dstSig) in H.
    inversion H; clear H; subst s'; apply inj_pair2_eq_dec in H2; try apply eq_dec; subst v.
    exists e0; split; auto; apply vsUnion_r; apply vsSing_intro.
    
    apply vsUnion_elim in H; destruct H; destruct H.
  Qed.
  
  Lemma free_neq_abstract_U: forall s (t1 t2: term _ s) s' (v: variable s'), vsIn _ v (free _ (neq_abstract_U t1 t2)) -> exists v', v=inl v' /\ vsIn _ v' (vsUnion _ (tm_vars _ t1) (tm_vars _ t2)).
  Proof.
    intros.
    destruct t1; destruct t2; simpl in *.
    destruct (SV.In_dec e (exv s)).
    destruct (SV.In_dec e0 (exv s)).
    unfold eq_abstract_U in H.
    apply free_eq_yy in H; destruct H; apply vsSing_elim in H.
    inversion H; clear H; subst s'; apply inj_pair2_eq_dec in H2; try apply eq_dec; subst v.
    exists e; split; auto; apply vsUnion_l; apply vsSing_intro.
    inversion H; clear H; subst s'; apply inj_pair2_eq_dec in H2; try apply eq_dec; subst v.
    exists e0; split; auto; apply vsUnion_r; apply vsSing_intro.
    apply free_eq_yd in H; destruct H.
    apply vsSing_elim in H.
    inversion H; clear H; subst s'; apply inj_pair2_eq_dec in H2; try apply eq_dec; subst v.
    exists e; split; auto; apply vsUnion_l; apply vsSing_intro.
    simpl in H.
    apply vsSing_elim in H.
    inversion H; clear H; subst s'; apply inj_pair2_eq_dec in H2; try apply eq_dec; subst v.
    exists e0; split; auto; apply vsUnion_r; apply vsSing_intro.

    destruct (SV.In_dec e0 (exv s)).
    apply free_eq_yd in H; destruct H.
    apply vsSing_elim in H.
    inversion H; clear H; subst s'; apply inj_pair2_eq_dec in H2; try apply eq_dec; subst v.
    exists e0; split; auto; apply vsUnion_r; apply vsSing_intro.
    simpl in H.
    apply vsSing_elim in H.
    inversion H; clear H; subst s'; apply inj_pair2_eq_dec in H2; try apply eq_dec; subst v.
    exists e; split; auto; apply vsUnion_l; apply vsSing_intro.

    simpl in H.
    apply vsUnion_elim in H; destruct H; apply (vsSing_elim dstSig) in H.
    inversion H; clear H; subst s'; apply inj_pair2_eq_dec in H2; try apply eq_dec; subst v.
    exists e; split; auto; apply vsUnion_l; apply vsSing_intro.
    inversion H; clear H; subst s'; apply inj_pair2_eq_dec in H2; try apply eq_dec; subst v.
    exists e0; split; auto; apply vsUnion_r; apply vsSing_intro.
    
    destruct (SV.In_dec e (exv s)).
    apply free_eq_yd in H; destruct H.
    apply vsSing_elim in H.
    inversion H; clear H; subst s'; apply inj_pair2_eq_dec in H2; try apply eq_dec; subst v.
    exists e; split; auto; apply vsUnion_l; apply vsSing_intro.
    simpl in H.
    destruct H.
    simpl in H.
    apply vsUnion_elim in H; destruct H; try (now destruct H).
    apply (vsSing_elim dstSig) in H.
    inversion H; clear H; subst s'; apply inj_pair2_eq_dec in H2; try apply eq_dec; subst v.
    exists e; split; auto; apply vsUnion_l; apply vsSing_intro.
    
    destruct (SV.In_dec e0 (exv s)); simpl in H.
    apply vsGUnion_elim in H; destruct H as [k H]; destruct H.

    apply vsUnion_elim in H; destruct H; try (now destruct H).
    apply (vsSing_elim dstSig) in H.
    inversion H; clear H; subst s'; apply inj_pair2_eq_dec in H2; try apply eq_dec; subst v.
    exists e0; split; auto; apply vsUnion_r; apply vsSing_intro.
    
    apply vsUnion_elim in H; destruct H; destruct H.
  Qed.
  
  Lemma free_at_abstract_U: forall a s (v: variable s), vsIn _ v (free _ (at_abstract_U a)) -> exists v', v=inl v' /\ vsIn _ v' (at_free _ a).
  Proof.
    intros; destruct a; simpl in *.
    apply free_lt_abstract_U in H; auto.
    apply free_nlt_abstract_U in H; auto.
    apply free_eq_abstract_U in H; auto.
    apply free_neq_abstract_U in H; auto.
  Qed.
  
  Lemma free_abstract_U: forall f hn fv s (v: variable s), vsIn _ v (free _ (abstract_U f hn fv)) -> vsIn _ v (vsMap (fun s v => inl v) (vsUnion _ exv allv)).
  Proof.
    induction f; simpl; intros; auto; try (now inversion H); try tauto.
    - apply free_at_abstract_U in H.
      destruct H as [v' [h H]]; subst v.
      apply (vsMap_In_intro (fun s v => inl v)).
      apply fv in H; apply H.
    - apply vsUnion_elim in H; destruct H; [apply IHf1 in H|apply IHf2 in H]; apply H.
    - apply vsUnion_elim in H; destruct H; [apply IHf1 in H|apply IHf2 in H]; apply H.
  Qed.
  
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
    fun s v h => env' s (inl v).

  Definition rtfr_pe {D: Dom srcSig} (pe: pEnv (tfr_dom D) (vsMap (fun s v => inl v) allv)): pEnv D allv :=
    fun (s : Sort) (v : variable s) (h : vsIn _ v allv) =>
         pe s (inl v) (vsMap_In_intro (fun s v => inl v) h).
  
(*  
  Definition tfr_pe {D: Dom srcSig} (pe: pEnv D allv) : pEnv (tfr_dom D) (vsMap (fun s v => inl v) allv) :=
    fun s v h => match v with inl v1 => pe s v1 (vsMap_In _ h) | _ => neDom s end.
*)

  Lemma get_pe_pAdd: forall D (env: Env dstSig (tfr_dom D)) (pe: pEnv (tfr_dom D) (vsMap (fun s v => inl v) allv)),
    get_pe (pAdd env pe) = rtfr_pe pe.
  Proof.
    intros.
    apply functional_extensionality_dep; intro s.
    apply functional_extensionality_dep; intro v.
    apply functional_extensionality_dep; intro h.
    unfold get_pe,pAdd,rtfr_pe; simpl.
    match goal with |- match ?cnd with _=>_ end = _ => destruct cnd end.
    f_equal; apply proof_irrelevance.
    exfalso; apply n; clear n.
    apply (vsMap_In_intro (fun s v => inl v)); auto.
  Qed.
  
  Record isExtItp {D: Dom srcSig} (Itp: Interp D) (Itp': Interp (tfr_dom D)) t: Prop := {
    is_uniq: forall s v h (x y: ssem s), psem (Interp:=Itp') (NewPred s v h) t (fun _ => x) -> psem (Interp:=Itp') (NewPred s v h) t (fun _ => y) -> x = y;
    is_ne: forall s (v: variable s) h, exists (d: ssem s), psem (Interp:=Itp') (NewPred s v h) t (fun _ => d);
    is_eqp: forall p a t, psem (Interp:=Itp) p t a <-> psem (Interp:=Itp') (OldPred p) t a;
    is_eqc: forall s (c: constant s), csem (Interp:=Itp) c = csem (Interp:=Itp') c
  }.
  
  Ltac psemTac :=
    match goal with
      H:psem _ _ ?sa |- psem _ _ ?sa' => assert (sa' = sa) as ae;
          try (rewrite ae; assumption); (apply functional_extensionality_dep; intros)
    end.

  Definition isExtEnv {D: Dom srcSig} (env: Env srcSig D) (env': Env dstSig (tfr_dom D)) :=
    forall s v, env s v = env' s (inl v).

  Lemma isExtEnv_add: forall {D: Dom srcSig} s (v: variable s) d (env: Env srcSig D) (env': Env dstSig (tfr_dom D)), isExtEnv env env' ->
    isExtEnv (add srcSig v d env) (add (D:=tfr_dom D) dstSig (inl v) d env').
  Proof.
    repeat intro.
    unfold add; simpl.
    destruct (eq_dec s s0).
    subst s0.
    destruct (eq_dec v v0); auto.
    apply H.
    apply H.
  Qed.
(*
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
*)  
  Lemma tm_dst_sem: forall s (tm: term srcSig s) (D: Dom srcSig) (env: Env srcSig D) (env': Env dstSig (tfr_dom D)) (Itp: Interp D) (Itp': Interp (tfr_dom D)) t, 
    isExtItp Itp Itp' t -> isExtEnv env env' ->
      (tm_sem srcSig (Itp:=Itp) env tm = tm_sem dstSig (Itp:=Itp') env' (tm_dstSig tm)).
  Proof.
    intros.
    destruct tm; simpl; intros; auto.
    apply (is_eqc _ _ _ H).
  Qed.
  
  Lemma lt_dst_sem: forall l t (D: Dom srcSig) (env: Env srcSig D) (env': Env dstSig (tfr_dom D)) (Itp: Interp D) (Itp': Interp (tfr_dom D)), 
    isExtItp Itp Itp' t -> isExtEnv env env' ->
      (lt_sem srcSig (Itp:=Itp) env l t <-> lt_sem dstSig (Itp:=Itp') env' (lt_dstSig l) t).
  Proof.
    intros.
    destruct l; simpl; intros; auto.
    split; intro.
    rewrite (is_eqp _ _ _ H) in H1.
    psemTac.
    symmetry; apply (tm_dst_sem _ (t0 x) D) with (t:=t); intros; auto.
    rewrite (is_eqp _ _ _ H).
    psemTac.
    apply (tm_dst_sem _ (t0 x) D env env') with (t:=t); intros; auto.
  Qed.

  Fixpoint noAllV `{Sg: Sig} (V: VarSet Sg) (f: formula Sg): Prop :=
    match f with
    | Ex _ s v f => noAllV V f
    | All _ s v f => not (vsIn Sg v V) /\ noAllV V f
    | And _ f1 f2 | Or _ f1 f2 => noAllV V f1 /\ noAllV V f2
    | _ => True
    end.

  Lemma at_dst_sem: forall a t (D: Dom srcSig) (env: Env srcSig D) (env': Env dstSig (tfr_dom D)) (Itp: Interp D) (Itp': Interp (tfr_dom D)), 
    isExtItp Itp Itp' t -> isExtEnv env env' ->
      (at_sem srcSig (Itp:=Itp) env a t <-> at_sem dstSig (Itp:=Itp') env' (at_dstSig a) t).
  Proof.
    intros; destruct a; simpl.
  - apply lt_dst_sem; auto.
  - apply not_iff_compat.
    apply lt_dst_sem; auto.
  - rewrite tm_dst_sem with (Itp':=Itp') (env':=env') (t:=t); auto.
    rewrite tm_dst_sem with (Itp':=Itp') (env':=env') (t:=t); auto.
    reflexivity.
  - rewrite tm_dst_sem with (Itp':=Itp') (env':=env') (t:=t); auto.
    rewrite tm_dst_sem with (Itp':=Itp') (env':=env') (t:=t); auto.
    apply not_iff_compat.
    reflexivity.
  Qed.
  
  Lemma fm_dst_sem: forall f (hf: isProp _ f) t (D: Dom srcSig) (env: Env srcSig D) (env': Env dstSig (tfr_dom D)) (Itp: Interp D) (Itp': Interp (tfr_dom D)), 
    isExtItp Itp Itp' t -> isExtEnv env env' ->
      (fm_sem srcSig (Itp:=Itp) env f t <-> fm_sem dstSig (Itp:=Itp') env' (fm_dstSig f) t).
  Proof.
    intros.
    revert f hf t env env' H H0.
    induction f; simpl; intros; auto; try tauto.
  - rewrite at_dst_sem with (env':=env'); auto.
    reflexivity.
    auto.
  - rewrite <-IHf1, <-IHf2; auto; try tauto; try reflexivity; auto.
  - rewrite <-IHf1, <-IHf2; auto; try tauto; try reflexivity; auto.
Qed.

  Lemma fm_dst_sem_intro: forall f t (D: Dom srcSig) (env: Env srcSig D) (env': Env dstSig (tfr_dom D)) (Itp: Interp D) (Itp': Interp (tfr_dom D)), 
    (forall t, isExtItp Itp Itp' t) -> isExtEnv env env' ->
      fm_sem srcSig (Itp:=Itp) env f t -> fm_sem dstSig (Itp:=Itp') env' (fm_dstSig f) t.
  Proof.
    intros.
    revert f t env env' H H0 H1.
    induction f; simpl; intros; auto; try tauto.
  - revert H1; apply at_dst_sem; now auto.
  - destruct H1.
    apply IHf1 with (env':=env') in H1; auto.
    apply IHf2 with (env':=env') in H2; auto.
  - destruct H1.
    apply IHf1 with (env':=env') in H1; auto.
    apply IHf2 with (env':=env') in H1; auto.
  - destruct H1 as [d H1]; exists d.
    revert H1; apply IHf; auto.
    apply isExtEnv_add; auto.
  - specialize (H1 d).
    revert H1; apply IHf; auto.
    apply isExtEnv_add; auto.
  - destruct H1 as [t' [h1 h2]].
    exists t'; split; auto.
    revert h2; apply IHf; auto.
  - specialize (H1 t' H2).
    revert H1; apply IHf; auto.
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
    not (SV.set_In v (exv s)) -> pAdd env (get_pe env') s v = env' s (inl v).
  Proof.
    intros.
    unfold pAdd, get_pe.
    destruct (SV.set_In_dec v (allv s)); auto.
    apply vsUnion_elim in fv; destruct fv; tauto.
  Qed.

  Definition ItpEnvSing {D: Dom srcSig} (env: Env srcSig D) (Itp': Interp (tfr_dom D)) t : Prop :=
    forall s v h (d: ssem (Sg:=dstSig) s), psem (Sg:=dstSig) (NewPred s v h) t (fun _ => d) -> env s v = d.

  Lemma lt_abstract_U_sem: forall (D: Dom srcSig) (env: Env srcSig D) (Itp: Interp D) Itp' t (hx: isExtItp Itp Itp' t) (he: ItpEnvSing env Itp' t) l (fv: vsSubset _ (lt_vars _ l) (vsUnion _ exv allv)),
    forall env' : Env dstSig (tfr_dom D),
      lt_sem srcSig (pAdd env (get_pe env')) l t ->
        fm_sem dstSig (Itp:=Itp') env' (lt_abstract_U l) t.
  Proof.
    intros.
    unfold lt_abstract_U.
    destruct l; auto.
    rewrite Or_sem.
    match goal with
      |- ?P \/ ?Q => destruct (classic P); [left;auto|right]
    end.
    unfold mk_disj in H0.
    setoid_rewrite IOr_sem in H0.
    generalize (not_ex_all_not _ _ H0); clear H0; intro.
    apply (is_eqp _ _ _ hx).
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
    rewrite (pAdd_exv _ env env' _ e s).
    apply he in H0.
    symmetry; apply H0.
    
    symmetry; apply (pAdd_nexv _ env env' _ e fv n0).
    symmetry; apply (is_eqc Itp Itp' _ hx).
  Qed.

  Lemma nlt_abstract_U_sem: forall (D: Dom srcSig) (env: Env srcSig D) (Itp: Interp D) Itp' t (hx: isExtItp Itp Itp' t) (he: ItpEnvSing env Itp' t) l (fv: forall s, SV.subset (lt_vars _ l s) (vsUnion _ exv allv s)),
    forall env' : Env dstSig (tfr_dom D),
      not (lt_sem srcSig (pAdd env (get_pe env')) l t) ->
        fm_sem dstSig (Itp:=Itp') env' (nlt_abstract_U l) t.
  Proof.
    intros.
    unfold nlt_abstract_U.
    destruct l.
    rewrite Or_sem; simpl in *.
    match goal with
      |- ?P \/ ?Q => destruct (classic P); [left;auto|right]
    end.
    unfold mk_disj in H0; setoid_rewrite IOr_sem in H0.
    generalize (not_ex_all_not _ _ H0); clear H0; intro.
    intro; apply H; clear H.
    apply (is_eqp _ _ _ hx) in H1.
    psemTac.
    specialize H0 with x.
    apply vsSubsetGUnion_elim with (k:=x) in fv.
    destruct (t0 x); simpl; auto.
    apply vsSubsetSing in fv.
    destruct (SV.In_dec e (exv (pr_args p x))); auto.
    simpl in H0.
    apply not_not_iff in H0.
    rewrite (pAdd_exv _ env env' _ e s).
    apply he in H0.
    apply H0.
    apply (pAdd_nexv _ env env' _ e fv n0).
    apply (is_eqc Itp Itp' _ hx).
  Qed.
  
  Lemma eq_abstract_U_sem:  forall (D: Dom srcSig) (env: Env srcSig D) (Itp: Interp D) Itp' t (hx: isExtItp Itp Itp' t) s (t1 t2: term srcSig s) (he: ItpEnvSing env Itp' t) 
  (fv1: vsSubset _ (tm_vars _ t1) (vsUnion _ exv allv))
  (fv2: vsSubset _ (tm_vars _ t2) (vsUnion _ exv allv)),
    forall env' : Env dstSig (tfr_dom D),
      tm_sem srcSig (pAdd env (get_pe env')) t1 = tm_sem srcSig (pAdd env (get_pe env')) t2 ->
        fm_sem dstSig (Itp:=Itp') env' (eq_abstract_U t1 t2) t.
  Proof.
    intros.
    destruct t1; destruct t2; unfold eq_abstract_U; repeat (rewrite And_sem, Or_sem); auto.
    destruct (SV.In_dec e (exv s)).
    destruct (SV.In_dec e0 (exv s)).
    generalize (pAdd_exv D env env' s e s0); intro.
    generalize (pAdd_exv D env env' s e0 s1); intro.
    assert (env s e = env s e0).
    rewrite <-H0,<-H1.
    apply H.
    clear H H0 H1.
    unfold eq_yy.
    rewrite And_sem, Or_sem; rewrite Or_sem; simpl in *.
    split.
    match goal with |- not ?P \/ ?Q => elim (classic P); try tauto; right end.
    apply he in H.
    destruct (is_ne Itp Itp' _ hx _ e0 s1) as [d h].
    generalize h; intro h'.
    apply he in h'.
    rewrite <-H,H2,h'.
    apply h.

    match goal with |- not ?P \/ ?Q => elim (classic P); try tauto; right end.
    destruct (is_ne Itp Itp' _ hx _ e s0) as [d h].
    destruct (is_ne Itp Itp' _ hx _ e0 s1) as [d0 h0].
    generalize (is_uniq Itp Itp' _ hx _ e0 s1 _ _ H h0); intro.
    apply he in h0.
    rewrite H0,<-h0; clear H0 h0 d0.
    generalize h; intro h'.
    apply he in h'.
    subst d.
    rewrite H2 in h; apply h.
    
    simpl in fv2; apply vsSubsetSing in fv2.
    assert (env s e = env' s (inl e0)).
      rewrite <-pAdd_exv with (env:=env) (env':=env') (v:=e); auto.
      rewrite <-pAdd_nexv with (env:=env)(env':=env') (v:=e0); now auto.
    clear H.
    unfold eq_yd; simpl.
    destruct (is_ne Itp Itp' _ hx _ e s0) as [d h].
    generalize h; intro h'.
    apply he in h'.
    subst d.
    rewrite H0 in h.
    apply h.
    
    simpl in fv1; apply vsSubsetSing in fv1.
    simpl in fv2; apply vsSubsetSing in fv2.
    destruct (SV.In_dec e0 (exv s)); auto.
    assert (env' s (inl e) = env s e0).
      rewrite <-pAdd_nexv with (env:=env) (env':=env') (v:=e); auto.
      rewrite <-pAdd_exv with (env:=env) (env':=env') (v:=e0); now auto.
    unfold eq_yd; simpl.
    destruct (is_ne Itp Itp' _ hx _ e0 s0) as [d h].
    generalize h; intro h'.
    apply he in h'.
    subst d.
    rewrite <-H0 in h; apply h.

    simpl.
    generalize (pAdd_nexv D env env' s e fv1 n); simpl; intro.
    rewrite <-H0; clear H0.
    generalize (pAdd_nexv D env env' s e0 fv2 n0); simpl; intro.
    rewrite <-H0; clear H0.
    now auto.
    
    destruct (SV.In_dec e (exv s)); auto.
    assert (env s e = csem e0).
      rewrite <-pAdd_exv with (env:=env) (env':=env') (v:=e); auto.
    unfold eq_yd; simpl.
    rewrite <-(is_eqc _ _ _ hx).
    rewrite <-H0.
    destruct (is_ne Itp Itp' _ hx _ e s0) as [d h].
    generalize h; intro h'.
    apply he in h'.
    subst d; apply h.
    
    simpl.
    simpl in fv1; apply vsSubsetSing in fv1.
    generalize (pAdd_nexv _ env env' _ e); simpl; intro.
    rewrite <-H0; auto; clear H0.
    rewrite <-(is_eqc _ _ _ hx).
    apply H.
    
    destruct (SV.In_dec e0 (exv s)).
    simpl.
    assert (csem e = env s e0).
      rewrite <-pAdd_exv with (env:=env) (env':=env') (v:=e0); auto.
    rewrite <-(is_eqc _ _ _ hx).
    rewrite H0.
    destruct (is_ne Itp Itp' _ hx _ e0 s0) as [d h].
    generalize h; intro h'.
    apply he in h'.
    subst d; apply h.

    simpl.
    simpl in fv2; apply vsSubsetSing in fv2.

    generalize (pAdd_nexv _ env env' _ e0); simpl; intro.
    rewrite <-H0; clear H0; auto.
    rewrite <-(is_eqc _ _ _ hx).
    apply H.

    simpl in *.
    rewrite <-(is_eqc _ _ _ hx).
    rewrite <-(is_eqc _ _ _ hx).
    apply H.
  Qed.
  
  Lemma neq_abstract_U_sem:  forall (D: Dom srcSig) (env: Env srcSig D) (Itp: Interp D) Itp' t (hx: isExtItp Itp Itp' t) s (t1 t2: term srcSig s) (he: ItpEnvSing env Itp' t)
  (fv1: forall s, SV.subset (tm_vars srcSig t1 s) (vsUnion _ exv allv s))
  (fv2: forall s, SV.subset (tm_vars srcSig t2 s) (vsUnion _ exv allv s)),
    forall env' : Env dstSig (tfr_dom D),
      tm_sem srcSig (pAdd env (get_pe env')) t1 <> tm_sem srcSig (pAdd env (get_pe env')) t2 ->
        fm_sem dstSig (Itp:=Itp') env' (neq_abstract_U t1 t2) t.
  Proof.
    intros.
    unfold neq_abstract_U.
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
    apply H; rewrite (is_eqc _ _ _ hx); apply H0.

    simpl in fv1; apply vsSubsetSing in fv1.
    rewrite (pAdd_nexv D) with (v:=e) in H; auto.
    simpl.
    rewrite <-(is_eqc _ _ _ hx); apply H.

    destruct (SV.In_dec e0 (exv s)).
    rewrite pAdd_exv with (v:=e0) in H; auto.
    unfold neq_yd; simpl; intro.
    apply he in H0.
    apply H; rewrite (is_eqc _ _ _ hx); symmetry; apply H0.

    simpl.
    simpl in fv2; apply vsSubsetSing in fv2.
    rewrite (pAdd_nexv D) with (v:=e0) in H; auto.
    rewrite <-(is_eqc _ _ _ hx); apply H.
    
    do 2 rewrite <-(is_eqc _ _ _ hx); apply H.
  Qed.

  Lemma at_abstract_U_sem: forall (D: Dom srcSig) Itp Itp' t (hx: isExtItp Itp Itp' t) (env: Env srcSig D) (he: ItpEnvSing env Itp' t) a (fv: vsSubset _ (at_free _ a) (vsUnion _ exv allv)),
    forall env', 
      at_sem srcSig (Itp:=Itp) (pAdd env (get_pe env')) a t ->
        fm_sem dstSig (Itp:=Itp') env' (at_abstract_U a) t.
  Proof.
    intros.
    destruct a; simpl.
    revert H; apply lt_abstract_U_sem; auto.
    revert H; apply nlt_abstract_U_sem; auto.
    revert H; apply eq_abstract_U_sem; auto.
      apply vsSubsetUnion_elim_l in fv; auto.
      apply vsSubsetUnion_elim_r in fv; auto.
    revert H; apply neq_abstract_U_sem; auto.
      apply vsSubsetUnion_elim_l in fv; auto.
      apply vsSubsetUnion_elim_r in fv; auto.
  Qed.

  (*
    |- (EX ALL phi) => ALL abs(phi)
  *)
  
  Lemma abstract_U_sem: forall (D: Dom srcSig) Itp Itp' t (hx: isExtItp Itp Itp' t) (env: Env srcSig D) (he: ItpEnvSing env Itp' t) f (nfo: isProp srcSig f) (fv: vsSubset _ (free _ f) (vsUnion _ exv allv)),
    forall env', 
      fm_sem srcSig (Itp:=Itp) (pAdd env (get_pe env')) f t ->
        fm_sem dstSig (Itp:=Itp') env' (abstract_U f nfo fv) t.
  Proof.
    induction f; intros; try (simpl; tauto).
    - revert H; apply at_abstract_U_sem; eauto.
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
    getAll (fm_dstSig V f) = vsMap V (fun s v => inl v) (getAll f).
  Proof.
    induction f; simpl; intros; auto.
    simpl in *; rewrite IHf.
    apply (vsMap_add V s e (fun s v => inl v)).
    unfold isInj; intros.
    injection H; auto.
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
    forall s v, SV.set_In (inl v) (vsVars (dstSig V) (fun k => inl (vk k)) s) <->
      SV.set_In v (vsVars srcSig vk s).
  Proof.
    intros; auto.
    unfold vsVars; split; intros.
    apply SV.InCUnion_elim in H.
    destruct H as [u [h1 [h2 h3]]].
    apply SV.InCUnion_intro with (u0:=u); auto; intro.
    apply h3 in h2; clear h3 h.
    change (vsIn (dstSig V) (inl v) (vsSing (dstSig V) (inl (vk u)))) in h2.
    apply vsSing_elim in h2.
    change (vsIn _ v (vsSing srcSig (vk u))).
    injection h2; clear h2; intros; subst.
    apply inj_pair2_eq_dec in H; try apply eq_dec; subst.
    apply vsSing_intro.
    
    apply SV.InCUnion_elim in H.
    destruct H as [u [h1 [h2 h3]]].
    apply SV.InCUnion_intro with (u0:=u); auto; intro.    
    apply h3 in h2; clear h3 h.
    change (vsIn (dstSig V) (inl v) (vsSing (dstSig V) (inl (vk u)))).
    change (vsIn _ v (vsSing srcSig (vk u))) in h2.
    apply vsSing_elim in h2.
    injection h2; clear h2; intros; subst.
    apply inj_pair2_eq_dec in H; try apply eq_dec; subst.
    apply vsSing_intro.
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

  Definition neE V :=
    IAnd (dstSig V) Sort (fun s =>
      (IAnd (dstSig V) (asFinite (V s)) 
        (fun y => Atom (dstSig V) (Literal (dstSig V) 
          (Ey V (proj1_sig y) (InFin _ _) (proj1_sig y)))))).

  (* Definition 23 *)
  Definition bar f :=
    And (dstSig (getExF f))
      (AxE (getExF f))
      (mkEx (Sg:=dstSig (getExF f)) (vsMap (getExF f) (fun s v => inl v) (getExF f))
        (And (dstSig (getExF f))
          (neE (getExF f))
          (mkAll (Sg:=dstSig (getExF f)) (vsMap (getExF f) (fun s v => inl v) (getAll (EX f))) (fm_dstSig (getExF f) (EX_ALL f)))
        )).

  Lemma free_neE: forall V s (v: variable s), vsIn _ v (free _ (neE V)) -> exists v', v = inl v' /\ vsIn _ v' V.
  Proof.
    unfold neE; simpl; intros.
    apply free_IAnd_sub in H.
    apply (vsGUnion_elim (dstSig V)) in H; destruct H as [s' H].
    apply free_IAnd_sub in H.
    apply (vsGUnion_elim (dstSig V)) in H; destruct H as [v' H].
    simpl in H.
    apply (vsGUnion_elim (dstSig V)) in H; destruct H as [i H].
    apply vsSing_elim in H.
    injection H; clear H; intros; subst s'.
    apply inj_pair2_eq_dec in H; try apply eq_dec; subst v.
    exists (proj1_sig v'); split; auto.
    destruct v'; simpl in *.
    apply s0.
  Qed.

  Lemma free_AxE: forall f s (v: variable s), not (vsIn _ v (free _ (AxE f))).
  Proof.
    unfold AxE; intros; intro.
    simpl in H.
    apply free_IAnd_sub in H.
    apply (vsGUnion_elim (dstSig f)) in H; destruct H as [s' H].
    apply free_IAnd_sub in H.
    apply (vsGUnion_elim (dstSig f)) in H; destruct H as [v' H].
    simpl in H.
    apply vsInRemove_elim in H; destruct H as [H h1].
    apply vsInRemove_elim in H; destruct H as [H h2].
    apply vsUnion_elim in H; destruct H.
    apply SV.InUnion in H; destruct H.
    apply SV.InCUnion_elim in s0.
    destruct s0 as [i [k1 [k2 k3]]]; apply k3 in k2; clear k3.
    apply (vsSing_elim (dstSig f)) in k2.
    inversion k2; subst s'.
    apply inj_pair2_eq_dec in H1; try apply eq_dec; subst v; now auto.
    apply SV.InCUnion_elim in s0.
    destruct s0 as [i [k1 [k2 k3]]]; apply k3 in k2; clear k3.
    apply (vsSing_elim (dstSig f)) in k2.
    inversion k2; subst s'.
    apply inj_pair2_eq_dec in H1; try apply eq_dec; subst v; now auto.
    apply (vsUnion_elim (dstSig f)) in H; destruct H; apply (vsSing_elim (dstSig f)) in H.
    inversion H; subst s'.
    apply inj_pair2_eq_dec in H2; try apply eq_dec; subst v; now auto.
    inversion H; subst s'.
    apply inj_pair2_eq_dec in H2; try apply eq_dec; subst v; now auto.
  Qed.

  Lemma free_bar: forall f (fv: forall s, SV.is_empty (free _ f s))  s (v: variable s), not (vsIn _ v (free _ (bar f))).
  Proof.
    intros; intro.
    unfold bar in H.
    rewrite free_And in H.
    apply vsUnion_elim in H; destruct H.
    now apply free_AxE in H.
    unfold mkEx in H.
    apply (free_IEx (dstSig (getExF f))) in H; destruct H.
    rewrite free_And in H.
    apply vsUnion_elim in H; destruct H.
    apply free_neE in H.
    destruct H as [v' [h H]]; subst v.
    apply (vsMap_In_intro (getExF f) (fun s v => inl v)) in H.
    set (w := existT (fun s => asFinite (vsMap _ (fun s v=>inl v) (getExF f) s)) s 
      (exist _ (inl v') H)).
    apply (H0 w).
    reflexivity.
    
    apply (free_IAll (dstSig (getExF f))) in H; destruct H.
    apply free_dstSig in H.
    generalize (vsMap_In_ran _ _ H); intro.
    destruct H2 as [v' H2]; subst v.
    apply (vsMap_In_elim _ (fun s v=>inl v)) in H.

    apply close_EXfALL in H; auto.
    apply vsUnion_elim in H; destruct H.
    apply (vsMap_In_intro (getExF f) (fun s v => inl v)) in H.
    set (w := existT (fun s => asFinite (vsMap _ (fun s v=>inl v) (getExF f) s)) s 
      (exist _ (inl v') H)).
    apply (H0 w).
    reflexivity.
    apply (vsMap_In_intro (getAll (EX f)) (fun s v => inl v)) in H.
    set (w := existT (fun s => asFinite (vsMap _ (fun s v=>inl v) (getAll (EX f)) s)) s 
      (exist _ (inl v') H)).
    apply (H1 w).
    reflexivity.
    
    repeat intro.
    injection H2; tauto.
  Qed.

  Definition abstract_U_ExAll f (hf: isExAll _ f) (fv: forall s, SV.is_empty (free _ f s)) :=
    (mkAll (Sg:=dstSig (getExF f)) (vsMap _ (fun s v => inl v) (getExF f)) (mkAll (Sg:=dstSig (getExF f)) (vsMap _ (fun s v => inl v) (getAll (EX f))) (abstract_U _ _ (EX_ALL f) (isExAll_Prop _ hf) (close_EXfALL fv) ))).
  
  Definition tfr_env {D: Dom srcSig} V (env: Env srcSig D): Env (dstSig V) (tfr_dom V D) := 
    fun s v => match v with inl v' => env s v' | inr v' => neDom s end.

  Program Definition rtfr_itp' {V} {D: Dom srcSig} (itp: Interp (tfr_dom V D)): Interp D := {|
    csem s (c: constant (Sig:=srcSig) s) := csem (Interp:=itp) (c: constant s);
    psem p := psem (Interp := itp) (OldPred _ p)
  |}.

  Lemma AxE_sem: forall {f: formula srcSig} {D: Dom srcSig} {env} {itp: Interp (tfr_dom _ D)} {t},
    fm_sem (Itp:=itp) (dstSig (getExF f)) env (AxE (getExF f)) t ->
      forall {s v h a1 a2}, psem (Interp:=itp) (NewPred (getExF f) s v h) t a1 -> psem (Interp:=itp) (NewPred (getExF f) s v h) t a2 -> forall i, a1 i = a2 i.
  Proof.
    intro f; generalize (getExF f); clear f; intro V; intros.
    unfold AxE in H; simpl in H.
    specialize (H t (le_n t)).
    match goal with
      H: fm_sem (dstSig V) env
       (IAnd (dstSig V) Sort ?fk ) t |- _ => set (fks := fk)
    end.
    generalize (proj1 (IAnd_sem (dstSig V) (tfr_dom _ D) itp _ Sort fks t) H (pr_args (NewPred V s v h) i)); clear H; intro H.
    unfold fks in H; clear fks; simpl in H.
    match goal with
      H: fm_sem (dstSig V) env
       (IAnd (dstSig V) _ ?fk ) t |- _ => set (fkv := fk)
    end.
    generalize (proj1 (IAnd_sem (dstSig V) (tfr_dom _ D) itp _ _ fkv t) H); clear H; intro H.
    unfold fkv in H; clear fkv; simpl in H.
    specialize (H (exist _ v h) (a1 i) (a2 i)).
    simpl in H.
    rewrite add_ne, add_eq in H; try discriminate.
    rewrite add_eq in H.
    rewrite (proof_irrelevance _ _ h) in H.
    destruct H; auto.
    destruct H; exfalso; apply H; clear H.
    clear H1; psemTac.
    simpl in i.
    assert (i=x); subst; auto.
    apply (Fin.caseS' i (fun u => u=x)); clear i; intros; auto.
    apply (Fin.caseS' x (fun u => F1=u)); clear x; intros; auto.
    generalize (Fin.case0 (fun u => False) p); intro; tauto.
    generalize (Fin.case0 (fun u => False) p); intro; tauto.

    clear H0; psemTac.
    simpl in i.
    assert (i=x); subst; auto.
    apply (Fin.caseS' i (fun u => u=x)); clear i; intros; auto.
    apply (Fin.caseS' x (fun u => F1=u)); clear x; intros; auto.
    generalize (Fin.case0 (fun u => False) p); intro; tauto.
    generalize (Fin.case0 (fun u => False) p); intro; tauto.

  Qed.

  Lemma E_sem: forall {f: formula srcSig} {D: Dom srcSig} {env env'} {itp: Interp (tfr_dom _ D)} {t},
    fm_sem (Itp:=itp) (dstSig (getExF f)) env (neE (getExF f)) t ->
      fm_sem (Itp:=itp) (dstSig (getExF f)) env' (AxE (getExF f)) t ->
        forall s (v: variable s) h a, psem (NewPred _ s v h) t a <-> a Fin.F1 = env s (inl v).
  Proof.
    intros.
    unfold neE in H.
    match goal with
      H: fm_sem (dstSig (getExF f)) env
       (IAnd (dstSig (getExF f)) Sort ?fk ) t |- _ => set (fks := fk)
    end.
    generalize (proj1 (IAnd_sem (dstSig (getExF f)) (tfr_dom _ D) itp _ Sort fks t) H); clear H; intro H.
    specialize (H s); unfold fks in H; clear fks.

    match goal with
      H: fm_sem (dstSig (getExF f)) env
       (IAnd (dstSig (getExF f)) _ ?fk ) t |- _ => set (fkv := fk)
    end.
    generalize (proj1 (IAnd_sem (dstSig (getExF f)) (tfr_dom _ D) itp _ _ fkv t) H); clear H; intro H.
    specialize (H (exist _ v h)).
    unfold fkv in H; clear fkv; simpl in H.
    rewrite (proof_irrelevance _ _ h) in H.
    split; intro.
    apply (AxE_sem H0 H1 H).
    assert (a = (fun _ : Fin.t 1 => env s (inl v))).
    apply functional_extensionality_dep; intro i.
    simpl in i, a.
    rewrite <-H1; clear H H1.
    f_equal; clear a.
    apply (Fin.caseS' i (fun u => u=F1)); intros; auto.
    generalize (Fin.case0 (fun u => False) p); intro; tauto.
    subst a; apply H.
  Qed.
  
  Lemma preLemma4: forall (f: formula srcSig) (hf: isExAll _ f) (hv: forall s, SV.is_empty (free _ f s)),
    forall D (env: Env srcSig D) itp t, fm_sem (Itp:=itp) (dstSig _) (tfr_env _ env) (bar f) t -> fm_sem (dstSig _) (Itp:=itp) (tfr_env _ env) (abstract_U_ExAll f hf hv) t.
  Proof.
    intros.
    assert (forall s0 : Sort, SV.disjoint (getExF f s0) (getAll (EX f) s0)) as dsj.
      repeat intro.
      destruct H0.
      unfold getExF in H0.
      apply vsInter_elim in H0; destruct H0.
      apply (getAll_nfree _ _ _ (conj H1 H2)); tauto.      
    unfold bar in H.
    destruct H as [H1 H2].
    apply semEx_elim in H2.
    destruct H2 as [pe1 H2].
    destruct H2 as [H2 H3].
    unfold abstract_U_ExAll.
    apply semAll_intro; intro pe2.
    apply semAll_intro; intro pe3.
    apply semAll_elim with (pe:=pe3) in H3.
    set (pe' := fun s v h => pe1 s (inl v) (vsMap_In_intro _ (fun s v => inl v) h)).
    set (env' := (pAdd (pAdd env pe')
     (get_pe (getExF f) (getAll (EX f))
        (pAdd (pAdd (tfr_env (getExF f) env) pe2) pe3))) ).
    
    rewrite <-fm_dst_sem with (env:=env') (Itp:=rtfr_itp' itp) in H3.
    - apply (abstract_U_sem (getExF f) (getAll (EX f))) with (D:=D) (Itp:=rtfr_itp' itp) (env:=pAdd env pe'); simpl.
      * apply dsj.
      * split; intros.
        apply (AxE_sem H1 H H0 Fin.F1).
        generalize (E_sem H2 H1 s v h); intro.
        exists (pAdd (tfr_env (getExF f) env) pe1 s (inl v)).
        now rewrite H.
        unfold rtfr_itp'; simpl.
        reflexivity.
        reflexivity.
      * repeat intro.
        simpl in H.
        rewrite (E_sem H2 H1) in H.
        unfold pe'.
        revert H; unfold tfr_env, pAdd; simpl.
        destruct (SV.set_In_dec v (getExF f s)); try tauto.
        match goal with |- context [match ?cnd with _=>_ end] => destruct cnd end.
        intro; rewrite (proof_irrelevance _ _ i0); symmetry; now auto.
        exfalso; apply n; clear n.
        apply vsMap_In_intro with (f:=fun s v => inl v); now auto.
      * apply H3.
    - now apply isExAll_Prop.
    - split; intros.
      apply (AxE_sem H1 H H0 Fin.F1).
      generalize (E_sem H2 H1 s v h); intro.
      exists (pAdd (tfr_env (getExF f) env) pe1 s (inl v)).
      now rewrite H.
      unfold rtfr_itp'; simpl.
      reflexivity.
      reflexivity.
    - unfold env'; repeat intro.
      unfold get_pe, pAdd, tfr_env.
      destruct (SV.set_In_dec v (getAll (EX f) s)).
      destruct (SV.set_In_dec (inl v)
    (vsMap (getExF f) (fun (s0 : Sort) (v0 : variable s0) => inl v0)
       (getAll (EX f)) s)); auto.
      exfalso; apply n; clear n.
      apply (vsMap_In_intro _ (fun s v => inl v)); now auto.
      destruct (SV.set_In_dec (inl v)
    (vsMap (getExF f) (fun (s0 : Sort) (v0 : variable s0) => inl v0)
       (getAll (EX f)) s)).
      exfalso; apply n; clear n.
      apply (vsMap_In_elim _ (fun s v => inl v)) in i; auto.
      repeat intro; injection H; tauto.
      destruct (SV.set_In_dec v (getExF f s)).
      destruct (SV.set_In_dec (inl v)
    (vsMap (getExF f) (fun (s0 : Sort) (v0 : variable s0) => inl v0)
       (getExF f) s)).
      unfold pe'; f_equal; apply proof_irrelevance.
      exfalso; apply n1; clear n1.
      apply (vsMap_In_intro _ (fun s v => inl v)); now auto.
      destruct (SV.set_In_dec (inl v)
    (vsMap (getExF f) (fun (s0 : Sort) (v0 : variable s0) => inl v0)
       (getExF f) s)); auto.
      exfalso; apply n1; clear n1.
      apply (vsMap_In_elim _ (fun s v=>inl v)) in i; auto.
      repeat intro; injection H; tauto.
  Qed.
  
  Definition rtfr_dom {V} (D: Dom (dstSig V)) : Dom srcSig := {|
    ssemT (s: Sort (Sig:=srcSig)) := ssemT (Sg:=dstSig V) s;
    ssem s := ssem (Sg:=dstSig V) s;
    neDom s := neDom (Sg:=dstSig V) s 
  |}.
  
  Lemma tfr_rtfr_dom: forall {V} (D: Dom (dstSig V)), tfr_dom V (rtfr_dom D) = D.
  Proof.
    intros; destruct D; simpl; auto.
  Qed. 
  
  Definition rtfr_env {V} {D: Dom (dstSig V)} (env: Env _ D): Env _ (rtfr_dom D) :=
    fun s v => env s (inl v).
  
  (* PaperLemma 4 *)
  Lemma Lemma4: forall (f: formula srcSig) (hf: isExAll _ f) (hv: forall s, SV.is_empty (free _ f s)),
    forall (D: Dom (dstSig _)) (env: Env _ D) itp t, fm_sem (Itp:=itp) (dstSig _) env (bar f) t -> 
      fm_sem (dstSig _) (Itp:=itp) env (abstract_U_ExAll f hf hv) t.
  Proof.
    intros until D.
    rewrite <-(tfr_rtfr_dom D); intro env.
    intros itp t.
    intro.
    set (env' := tfr_env (getExF f) (rtfr_env env)).

    apply fm_sem_equiv with (e1:=env').
    intros.
    unfold abstract_U_ExAll, mkAll in H0; simpl in H0.
    match goal with
     H:SV.set_In v (free _ (IAll _ _ _ _ ?f) s) |- _ => set (fk := f)
    end.
    apply free_IAll with (f0:=fk) in H0; apply proj1 in H0; unfold fk in H0; clear fk.
    match goal with
     H: vsIn _ v (free _ (IAll _ _ _ _ ?f)) |- _ => set (fk := f)
    end.
    apply free_IAll with (f0:=fk) in H0; apply proj1 in H0; unfold fk in H0; clear fk.
    apply free_abstract_U in H0.
    apply vsMap_In_ran in H0.
    destruct H0 as [v' H0]; subst v.
    reflexivity.
    apply fm_sem_equiv with (e1:=env') in H.
    revert H; apply preLemma4.
    intros.
    apply free_bar in H1; tauto.
  Qed.
  
  Lemma AxE_sem_intro: forall V D (env: Env srcSig D) itp pe t,
    fm_sem (Itp:=tfr_itp V itp pe) (dstSig V) (tfr_env V env) (AxE V) t.
  Proof.
    unfold AxE; intros.
    apply G_sem; intros.
    apply IAnd_sem; intro s.
    apply IAnd_sem; intro v.
    apply All_sem; intro d1.
    apply All_sem; intro d2.
    apply Imp_sem; intro H1.
    rewrite And_sem in H1.
    destruct H1 as [H1 H2].
    simpl in *.
    rewrite add_eq in *.
    rewrite add_ne in *.
    rewrite add_eq in *.
    subst d2; auto.
    discriminate.
    discriminate.
  Qed.
  
  Lemma neE_sem_intro: forall V D (env: Env srcSig D) itp pe t,
    (forall s v h, pe t s v h = env s v) ->
      fm_sem (Itp:=tfr_itp V itp pe) (dstSig V) (tfr_env V env) (neE V) t.
  Proof.
    unfold neE; intros.
    apply IAnd_sem; intro s.
    apply IAnd_sem; intro v.
    simpl; auto.
  Qed.

  Lemma getExF_dst_sub1: forall V g,
      vsSubset (dstSig (getExF g)) (vsMap V (fun s v => inl v) (getExF g)) (getExF (fm_dstSig V g)) .
  Proof.
    induction g; simpl; repeat intro; auto.
    unfold getExF in *; simpl in *.
    destruct (vsMap_In_ran _ _ H); subst v.
    apply (vsMap_In_elim _ (fun s v => inl v)) in H.
    apply vsInter_elim in H; destruct H.
    apply vsAdd_elim in H.
    apply (vsInter_intro (dstSig V)).
    destruct H.
    injection H; clear H; intros; subst s0.
    apply inj_pair2_eq_dec in H; try apply eq_dec; subst e.
    apply (vsAdd_l (dstSig V)).
    apply (vsAdd_r (dstSig V)).
    assert (vsIn _ x (vsInter srcSig (getEx g) (free srcSig (EX g)))).
      now apply vsInter_intro.
    apply (vsMap_In_intro V (fun s v => inl v)) in H1.
    apply IHg in H1.
    apply (vsInter_elim (dstSig V)) in H1; tauto.
    rewrite <-fm_dst_EX.
    apply free_dstSig.
    apply (vsMap_In_intro V (fun s v => inl v)); auto.
    repeat intro.
    injection H0; tauto.
  Qed.

  
  Program Definition tfr_pe {V} {D} (pe: pEnv D V): 
    pEnv (tfr_dom V D) (vsMap V (fun s v => inl v) V) :=
  fun s v => match v return vsIn _ v (vsMap V (fun s v => inl v) V) -> _ with
    inl v' => fun h => pe s v' _
   | inr _ => fun h => _
   end.
  Next Obligation.
    apply (vsMap_In_elim _ (fun s v => inl v)) in h.
    apply h.
    repeat intro; injection H; intros; auto.
  Qed.
  Next Obligation.
    apply vsMap_In_ran in h.
    exfalso; destruct h as [v' h]; discriminate.
  Qed.
  
  Lemma pAdd_tfr: forall V D (env: Env srcSig D) (pe: pEnv D V),
    pAdd (tfr_env V env) (tfr_pe pe) = tfr_env V (pAdd env pe).
  Proof.
    unfold pAdd, tfr_env, tfr_pe; simpl; intros.
    apply functional_extensionality_dep; intro s.
    apply functional_extensionality_dep; intro v.
    destruct v; simpl in *.
    destruct (SV.set_In_dec e (V s)).
    match goal with
      |- match ?cnd with _=>_ end=_ => destruct cnd
    end.
    now rewrite (proof_irrelevance _ _ i).
    exfalso; apply n; clear n.
    now apply (vsMap_In_intro _ (fun s v => inl v)).
    match goal with
      |- match ?cnd with _=>_ end=_ => destruct cnd; auto
    end.
    exfalso; apply n; clear n.
    apply (vsMap_In_elim _ (fun s v => inl v)) in i; auto.
    repeat intro; injection H; tauto.
    match goal with
      |- match ?cnd with _=>_ end=_ => destruct cnd; auto
    end.
    exfalso; apply vsMap_In_ran in i.
    destruct i as [v' h]; discriminate.
  Qed.
  
  Lemma pAdd_rtfr: forall V V' D (env: Env srcSig D) pe,
    tfr_env V (pAdd env (rtfr_pe V V' pe)) = pAdd (tfr_env V env) pe.
  Proof.
    unfold pAdd, tfr_env, rtfr_pe; simpl; intros.
    apply functional_extensionality_dep; intro s.
    apply functional_extensionality_dep; intro v.
    destruct v; simpl; auto.
    destruct (SV.set_In_dec e (V' s)).
    match goal with
      |- context [match ?cnd with _=>_ end] => destruct cnd
    end.
    rewrite (proof_irrelevance _ _ i0); now auto.
    exfalso; apply n; clear n.
    apply (vsMap_In_intro _ (fun s v => inl v)); auto.
    match goal with
      |- context [match ?cnd with _=>_ end] => destruct cnd; auto
    end.
    exfalso; apply (vsMap_In_elim _ (fun s v => inl v)) in i; auto.
    repeat intro; injection H; tauto.
    match goal with
      |- context [match ?cnd with _=>_ end] => destruct cnd; auto
    end.
    exfalso; apply (vsMap_In_ran _ (fun s v => inl v)) in i.
    destruct i as [v' h]; discriminate.
  Qed.
  
  Lemma isExtEnv_tfr: forall V D (env: Env srcSig D), isExtEnv V env (tfr_env V env).
  Proof.
    unfold tfr_env; simpl; intros.
    split; intros; auto.
  Qed.
    
  Lemma GEX_sem_t: forall (f: formula srcSig) (D: Dom srcSig) itp (env: Env srcSig D) t,
    fm_sem (Itp:=itp) srcSig env (G _ f) t ->
      exists (pe: nat -> pEnv D (getExF f)), forall t', t' >= t -> fm_sem (Itp:=itp) srcSig (pAdd env (pe t')) (EX f) t'.
  Proof.
    intros.
    apply (functional_choice (fun t' y => t' >= t -> fm_sem srcSig (pAdd env y) (EX f) t')); intro t'.
    simpl in H.
    assert (t'>=t -> exists y : pEnv D (getExF f), fm_sem srcSig (pAdd env y) (EX f) t').
    intro.
    specialize (H t' H0).
    apply mkEx_getExF in H.
    apply semEx_elim in H.
    destruct H as [pe H].
    exists pe.
    apply H.
    elim (classic (t' >= t)); intro.
    apply H0 in H1; clear H0.
    destruct H1 as [y H1]; exists y; intros; auto.
    exists (fun s v h => neDom s); intros; tauto.
  Qed.
  
  Lemma preLemma5: forall (f g: formula srcSig) (hg: isExAll srcSig g) (hv: forall s, SV.is_empty (free _ g s)) 
    {D} (env: Env srcSig D) itp t, 
    fm_sem (Itp:=itp) srcSig env (And _ f (G _ g)) t -> exists pe, 
      fm_sem (Itp:=tfr_itp (getExF g) itp pe) (dstSig (getExF g)) (tfr_env (getExF g) env)
        (And _ (fm_dstSig _ f) 
          (And _ (G _ (abstract_U_ExAll g hg hv)) (AxE (getExF g)))) t.
  Proof.
    intros.
    rewrite And_sem in H; destruct H.
    apply GEX_sem_t in H0.
    destruct H0 as [pe H0].
    exists pe.
    rewrite And_sem; split.
    eapply fm_dst_sem_intro with (env':=tfr_env (getExF g) env) in H.
    apply H.
    repeat (intro || split); simpl in *; auto.
    now subst y.
    now exists (pe t0 s v h).
    repeat (intro || split); simpl in *; tauto.
    
    rewrite And_sem; split.
    apply G_sem; intros.
    specialize (H0 t' H1).
    apply Lemma4; auto.
    unfold bar.
    rewrite And_sem; split.
    apply AxE_sem_intro.
    apply semEx_intro.
    exists (tfr_pe (pe t')).
    apply And_sem; split.
    rewrite pAdd_tfr.
    apply neE_sem_intro; intros; auto.
    unfold pAdd.
    destruct (SV.set_In_dec v (getExF g s)); try tauto.
    f_equal; apply proof_irrelevance.
    
    rewrite pAdd_tfr.
    apply semAll_intro; intro pe2.
    rewrite <-ALL_sem in H0.
    apply semAll_elim with (pe0:=rtfr_pe _ _ pe2) in H0.
    eapply fm_dst_sem_intro with (env':=(pAdd (tfr_env (getExF g) (pAdd env (pe t'))) pe2)) in H0.
    apply H0; intros; now auto.
    
    repeat intro.
    split; intros; simpl in *; auto.
    subst y; apply H2.
    now exists (pe t0 s v h).
    reflexivity.
    
    rewrite <-pAdd_rtfr.
    apply isExtEnv_tfr.
    apply AxE_sem_intro.
  Qed.
  
  (* PaperLemma 5 *)
  Lemma Lemma5: forall (f g: formula srcSig) (hg: isExAll srcSig g) (hv: forall s, SV.is_empty (free _ g s)),
    isSat _ (And _ f (G _ g)) ->
      isSat _ (And _ (fm_dstSig _ f) 
          (And _ (G _ (abstract_U_ExAll g hg hv)) (AxE (getExF g)))).
  Proof.
    intros.
    destruct H as [D [itp [env [t H]]]].
    apply preLemma5 with (hg:=hg) (hv:=hv) in H.
    destruct H as [pe H].
    exists (tfr_dom _ D).
    exists (tfr_itp _ itp pe).
    exists (tfr_env _ env).
    exists t.
    apply H.
  Qed.

End Abstraction.
