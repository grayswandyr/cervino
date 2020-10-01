Add LoadPath "$HOME/COQ/FO-LTL" as Top.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import Eqdep_dec.

Require Import Top.foltl.
Require Import Top.dec.
Require Import Top.finite.
Require Import Top.subItp.
Require Import Top.set.

Section FiniteModel_HdEx.

  Context {Ts: Type} {Tv: Ts->Type} {Tc: Ts->Type} {Tp: Type} {Ta: Tp -> Type}.
  Variable srcSig: @Sig Ts Tv Tc Tp Ta.
  Existing Instance srcSig.

  Inductive abs_ssem {D: Dom srcSig} (Itp: Interp D) (env: Env srcSig D) s :=
  | Cdom (d: ssem s) (h: exists c, csem (Interp:=Itp) (s:=s) c = d)
  | Vdom (d: ssem s) (hv: exists v, isEq (env s v) d) (hc: forall c, csem (Interp:=Itp) (s:=s) c <> d)
  | Default (noc: constant s -> False) (nov: variable s -> False).
  
  Definition cVal {D: Dom srcSig} (Itp: Interp D) {env: Env srcSig D} s (ad: abs_ssem Itp env s) :=
    match ad with
      Cdom _ _ _ d _ => d
    | Vdom _ _ _ d _ _ => d
    | Default _ _ _ _ _ => neDom s
    end.
    
  Lemma abs_ssem_dec {D: Dom srcSig} (Itp: Interp D) (env: Env srcSig D) s:
    EqDecType (abs_ssem Itp env s).
  Proof.
    intros.
    intros d1 d2.
    destruct d1; destruct d2.
    destruct (eq_dec d d0).
    subst d0.
    left.
    rewrite (proof_irrelevance _ h h0); reflexivity.
    right; intro.
    injection H; clear H; intros.
    apply (n H).
    right; discriminate.
    right; discriminate.
    destruct (eq_dec d d0).
    subst d0.
    left.
    destruct h as [c h].
    destruct (hc _ h).
    right; intro.
    discriminate.
    destruct (eq_dec d d0).
    subst d0.
    left.
    rewrite (proof_irrelevance _ hc hc0).
    rewrite (proof_irrelevance _ hv hv0).
    reflexivity.
    right; intro.
    injection H; clear H; intros.
    apply (n H).
    exfalso; destruct hv as [v hv].
    tauto.
    right; discriminate.
    right; discriminate.
    left.
    rewrite (proof_irrelevance _ noc noc0).
    rewrite (proof_irrelevance _ nov nov0).
    auto.
  Defined.
  
  Instance abs_ssemDec {D: Dom srcSig} (Itp: Interp D) (env: Env srcSig D) s: @EqDec (abs_ssem Itp env s) := {| eq_dec := abs_ssem_dec Itp env s |}.

  #[ program ] Definition abs_ssemSet {D: Dom srcSig} (Itp: Interp D) (env: Env srcSig D) s: SV.set (abs_ssemDec Itp env s) :=
    let abs :=
    (SV.union
     (SV.image  (fun c => Cdom Itp env s (csem c) (ex_intro _ c eq_refl)) (fin_set (T:=constant s)))
     (SV.CUnion
      (fun v => AllDecidable (all_dec (fun c => NotDec (isEq (csem c) (env s v)))))
      (fin_set (T:=variable s))
      (fun v h => SV.sing (abs_ssemDec Itp env s) (Vdom Itp env s (env s v) (ex_intro _ v eq_refl) h))))
    in
      match SV.is_empty_dec (fin_set) with
        left ev => match SV.is_empty_dec (fin_set (T:=constant s)) with
                      left ec => SV.add (Default Itp env s (fun (c: constant s) => ec c (fin_all c)) (fun (v: variable s) => ev v (fin_all v))) abs
                    | _ => abs
                    end
      | _ => abs
      end.
    
  Program Instance abs_ssemFin {D: Dom srcSig} (Itp: Interp D) (env: Env srcSig D) s: Finite := {|
    fin_dec := abs_ssemDec Itp env s;
    fin_set := abs_ssemSet Itp env s;
  |}.
  Next Obligation.
    unfold abs_ssemSet.
    match goal with |- SV.set_In x (match ?cnd with _=>_ end _) => destruct cnd end.
    match goal with |- SV.set_In x (match ?cnd with _=>_ end _) => destruct cnd end.
    destruct x.
    destruct h as [c h]; destruct (i0 c (fin_all c)).
    destruct hv as [v hv]; destruct (i v (fin_all v)).
    rewrite (proof_irrelevance _ (fun c : constant s => i0 c (fin_all c)) noc).
    rewrite (proof_irrelevance _ (fun v : variable s => i v (fin_all v)) nov).
    apply SV.InAdd_l.

    destruct x.
    apply SV.InUnion_l.
    destruct h as [c h].
    apply SV.InImage_intro with (w:=c); auto.
    subst d.
    f_equal; auto.
    apply fin_all.
    
    destruct hv as [v hv].
    apply SV.InUnion_r.
    apply SV.InCUnion_intro with (u:=v); simpl; intros; auto.
    apply fin_all.
    simpl in hv.
    subst d; apply hc; auto.

    simpl in hv; subst d.
    left; f_equal; apply proof_irrelevance.
    exfalso.
    apply n; clear n; repeat intro; tauto.
    
    destruct x.
    apply SV.InUnion_l.
    destruct h as [c h].
    apply SV.InImage_intro with (w:=c); auto.
    subst d.
    f_equal; auto.
    apply fin_all.
    
    destruct hv as [v hv].
    apply SV.InUnion_r.
    apply SV.InCUnion_intro with (u:=v); simpl; intros; auto.
    apply fin_all.
    simpl in hv.
    subst d; apply hc; auto.

    simpl in hv; subst d.
    left; f_equal; apply proof_irrelevance.
    exfalso.
    apply n; clear n; repeat intro; tauto.
  Qed.

  Definition default_value {D: Dom srcSig} (Itp: Interp D) (env: Env srcSig D) s: abs_ssem Itp env s :=
    match SV.is_empty_dec (T:=constant s) (fin_set (T:=constant s)) with
      left ec =>
        match SV.is_empty_dec (T:=variable s) (fin_set (T:=variable s)) with
          left ev => (Default Itp env s (fun (c: constant s) => ec c (fin_all c)) (fun (v: variable s) => ev v (fin_all v)))
        | right _ hv => 
            let v := SV.choose (T:=variable s) hv in
            @Vdom D Itp env s (env s v)
              (ex_intro _ v eq_refl) 
              (fun c => match ec c (fin_all c) with end)
        end
    | right _ hc => 
      let c := SV.choose (T:=constant s) hc in
      @Cdom D Itp env s (csem (Interp:=Itp) c) (ex_intro _ c eq_refl)
    end.
  
  Definition abs_dom {D: Dom srcSig} (Itp: Interp D) (env: Env srcSig D) := {| 
    ssem := abs_ssemFin Itp env;
    neDom := default_value Itp env;
  |}.
  
  Program Definition abs_itp {D: Dom srcSig} (Itp: Interp D) (env: Env srcSig D) : Interp (abs_dom Itp env) :=
  {|
    csem s c := Cdom Itp env s (csem c) (ex_intro _ c eq_refl);
    psem p t a := psem (Interp:=Itp) p t (fun i => cVal Itp _ (a i))
  |}.
  
  Lemma abs_subItp: forall {D: Dom srcSig} (Itp: Interp D) (env: Env srcSig D),
    subInterp _ (abs_itp Itp env) Itp.
  Proof.
    intros.
    split with (si_m := cVal (env:=env) Itp); intros; auto.
    destruct d1; destruct d2; simpl in *; subst; try discriminate.
      - f_equal; apply proof_irrelevance.
      - exfalso.
       destruct h as [c h].
       destruct hv as [k hv].
       apply hc in h; tauto.
     - exfalso.
       destruct h as [c h]; apply (noc c).
     - exfalso.
       destruct h as [c h].
       apply hc in h; tauto.
     - rewrite (proof_irrelevance _ hv0 hv); clear hv0.
       rewrite (proof_irrelevance _ hc0 hc).
       reflexivity.
     - exfalso.
       destruct hv as [v h]; apply (nov v).
     - exfalso.
       destruct h as [c h]; apply (noc c).
     - exfalso.
       destruct hv as [v h]; apply (nov v).
     - rewrite (proof_irrelevance _ noc0 noc).
       rewrite (proof_irrelevance _ nov0 nov).
       reflexivity.
     - unfold abs_itp; simpl in *.
       reflexivity.
  Defined.
  
  Program Definition abs_env {D: Dom srcSig} (Itp: Interp D) (env: Env srcSig D): Env srcSig (abs_dom Itp env) :=
    fun s v =>
      match ex_dec (fun c => isEq (csem c) (env s v)) with
        inleft _ (exist _ c h1) => Cdom Itp env s (csem c) (ex_intro _ c eq_refl)
      | inright hc => 
        match ex_dec (fun w => isEq (env s v) (env s w)) with
          inleft _ (exist _ w h) => Vdom Itp env _ (env s w) (ex_intro _ v h) _
        | inright h => match (h v eq_refl) with end
        end
      end.
  Next Obligation.
    rewrite <-h; apply (hc c).
  Qed.

  Lemma abs_subEnv:  forall {D: Dom srcSig} (Itp: Interp D) (env: Env srcSig D),
    subEnv _ (abs_subItp Itp env) (abs_env Itp env) env.
  Proof.
    repeat intro.
    unfold abs_env.
    unfold abs_subItp; simpl.
    destruct (ex_dec
       (fun c : constant s =>
        isEq (csem c) (env s v))); simpl.
    destruct s0.
    destruct d; simpl.
    reflexivity.

    destruct (ex_dec
       (fun w : variable s => isEq (env s v) (env s w)) ).
    destruct s0; simpl.
    apply d.
    
    destruct (n0 v eq_refl).
  Qed.
    
  Definition abs_domDec {D:Dom srcSig} (Itp: Interp D) (env: Env srcSig D): EqDec :=
    PairDec Sort (fun s => abs_ssemDec Itp env s).
    
  Definition abs_domFin {D:Dom srcSig} (Itp: Interp D) (env: Env srcSig D): Finite :=
    PairFin Sort (fun s => abs_ssemFin Itp env s).
  
  Theorem finiteModel_HdEx:
    forall f, noEx srcSig f -> isSat _ f ->
        exists (D: Dom srcSig), isFinite domType /\
          exists (Itp: Interp D), exists env, exists t,
          fm_sem _ env f t.
   Proof.
    intros.
    destruct H0 as [D [Itp [env [t h]]]].
    exists (abs_dom Itp env).
    split.
    apply (FiniteIsFinite (abs_domFin Itp env)).
    
    exists (abs_itp Itp env).
    exists (abs_env Itp env).
    exists t.
    revert h; apply fm_siSat with (si:=(abs_subItp Itp env)); auto.
    apply abs_subEnv; auto.
   Qed.
End FiniteModel_HdEx.
