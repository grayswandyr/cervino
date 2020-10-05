Require Import JMeq.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Classical.

Require Import foltl.
Require Import set.
Require Import dec.
Require Import finite.
Require Import varset.
Require Import vars.

(*
associer a un predicat p de la signature une liste de predicats g de meme arite

g => (p <-> X p)

conditions du cadre remplacees par I => X I

on doit avoir condition du cadre ==> I stable

==> correction de la cond syntaxique

hyp: r(xi) --> phi(xi)

*)

Section Stability.
  Context {Ts: Type} {Tv: Ts->Type} {Tc: Ts->Type} {Tp: Type}.
  Variable (Sg: @Sig Ts Tv Tc Tp).

  Variable D : Dom Sg.
  Variable itp: Interp D.
  Variable FC : predicate (Sig:=Sg) -> formula Sg.
  Variable FC_fo: forall p, isFO Sg (FC p).
  Variable FCv: forall p (i: Fin.t (pr_arity p)), variable (pr_args p i).
  (*
  Variable FCf: forall p i, vsIn Sg (FCv p i) (free Sg (FC p)).
  Variable FCr: forall (p: @predicate Sg) (s: @Sort Sg) (v: variable s), vsIn Sg v (free Sg (FC p)) -> exists (i: pr_arity p), JMeq (FCv p i) v.
  *)

  Definition inst (p: predicate) m : formula Sg :=
    IEx Sg (uptoFinite (pr_arity p)) (pr_args p)
        (FCv p) 
        (And Sg (FC p)
                  (IAnd Sg (uptoFinite (pr_arity p)) 
                      (fun i => Atom Sg (Eq Sg _ (Var Sg _ (FCv p i)) (m i))))
        ).

  Lemma inst_FO: forall p m, isFO Sg (inst p m).
  Proof.
    intros.
    unfold inst.
    apply isFO_IEx.
    apply isFO_And; split.
    apply FC_fo.
    apply isFO_IAnd; intros.
    simpl; auto.
  Qed.

(*
  r(x) et -r(x) stables si FC(r)(x) est en hypothese
  ==> ajouter r(x) et -r(x) dans l'env a droite de =>
*)

  Inductive atStable (V: SV.set (ltDec Sg)) : atom Sg -> Prop :=
    stbL: forall l, SV.set_In l V -> atStable V (Literal Sg l)
  | stbNL: forall l, SV.set_In l V -> atStable V (NLiteral Sg l)
  | stbEq: forall s t1 t2, atStable V (Eq Sg s t1 t2)
  | stbNEq: forall s t1 t2, atStable V (NEq Sg s t1 t2).

  Inductive isStable (V: SV.set (ltDec Sg)) : formula Sg -> Prop :=
    stbT: isStable V (FTrue _)
  | stbF: isStable V (FFalse _)
  | stbA: forall a, atStable V a -> isStable V (Atom Sg a)
  | stbAnd: forall f1 f2 V1 V2, SV.subset (T:=ltDec Sg) V1 V -> SV.subset (T:=ltDec Sg) V2 V ->
    isStable V1 f1 -> isStable V2 f2 -> isStable V (And Sg f1 f2)
  | stbOr: forall f1 f2 V1 V2, SV.subset (T:=ltDec Sg) V1 V -> SV.subset (T:=ltDec Sg) V2 V ->
    isStable V1 f1 -> isStable V2 f2 -> isStable V (Or Sg f1 f2)
  | stbAll: forall f s (v: variable s), isStable V f -> 
    (forall l, SV.set_In l V -> not (vsIn Sg v (lt_vars Sg l))) ->
      isStable V (All Sg s v f)
  | stbEx: forall f s (v: variable s), isStable V f -> 
    (forall l, SV.set_In l V -> not (vsIn Sg v (lt_vars Sg l))) ->
      isStable V (Ex Sg s v f)
  | stbFC: forall f p m, 
    isStable (SV.add (T:=ltDec Sg) (PApp Sg 0 p m) V) f -> 
      isStable V (inst p m) ->
        isStable V (Imp Sg (inst p m) f).
   
  Definition stable env (f: formula Sg) t: Prop :=
      fm_sem Sg env f t <-> fm_sem Sg env f (S t).
  
  Definition lt_stable (env: Env Sg D) l t :=
    lt_sem Sg env l t <-> lt_sem Sg env l (S t).
  
  Lemma stable_And: forall env f1 f2 t,
    stable env f1 t -> stable env f2 t -> stable env (And Sg f1 f2) t.
  Proof.
    repeat (split || intro); simpl in *; auto.
    apply H; now auto.
    apply H0; now auto.
    
    apply H; now auto.
    apply H0; now auto.
  Qed.

  Lemma stable_Or: forall env f1 f2 t,
    stable env f1 t -> stable env f2 t -> stable env (Or Sg f1 f2) t.
  Proof.
    repeat (split || intro); simpl in *; auto.
    destruct H1; [left; apply H | right; apply H0]; now auto.
    destruct H1; [left; apply H | right; apply H0]; now auto.
  Qed.
    
  Lemma stable_All: forall V s (v: variable s) f t,
    (forall l, SV.set_In (T:=ltDec Sg) l V -> ~ vsIn Sg v (lt_vars Sg l)) ->
      forall env2, 
        (forall env1, 
          (forall l s' (w: variable s'), SV.set_In (T:=ltDec Sg) l V -> vsIn Sg w (lt_vars Sg l) ->
            env1 s' w = env2 s' w) -> stable env1 f t) ->
          stable env2 (All Sg s v f) t.
  Proof.
    repeat (intro || split); simpl in *.
    apply H0; intros; auto.
    destruct (eq_dec s s').
    subst s'.
    destruct (eq_dec v w).
    subst w.
    apply H in H3; tauto.
    rewrite add_ne; now auto.
    rewrite add_ne2; auto.
    simpl; intro.
    injection H4; clear H4; intros; subst s'; tauto.
    
    apply H0; intros; auto.
    destruct (eq_dec s s').
    subst s'.
    destruct (eq_dec v w).
    subst w.
    apply H in H3; tauto.
    rewrite add_ne; now auto.
    rewrite add_ne2; auto.
    simpl; intro.
    injection H4; clear H4; intros; subst s'; tauto.
  Qed.

  Lemma stable_Ex: forall V s (v: variable s) f t,
    (forall l, SV.set_In (T:=ltDec Sg) l V -> ~ vsIn Sg v (lt_vars Sg l)) ->
      forall env2, 
        (forall env1, 
          (forall l s' (w: variable s'), SV.set_In (T:=ltDec Sg) l V -> vsIn Sg w (lt_vars Sg l) ->
            env1 s' w = env2 s' w) -> stable env1 f t) ->
          stable env2 (Ex Sg s v f) t.
  Proof.
    repeat (intro || split); simpl in *.
    destruct H1 as [d H1]; exists d.
    apply H0; intros; auto.
    destruct (eq_dec s s').
    subst s'.
    destruct (eq_dec v w).
    subst w.
    apply H in H3; tauto.
    rewrite add_ne; now auto.
    rewrite add_ne2; auto.
    simpl; intro.
    injection H4; clear H4; intros; subst s'; tauto.
    
    destruct H1 as [d H1]; exists d.
    apply H0; intros; auto.
    destruct (eq_dec s s').
    subst s'.
    destruct (eq_dec v w).
    subst w.
    apply H in H3; tauto.
    rewrite add_ne; now auto.
    rewrite add_ne2; auto.
    simpl; intro.
    injection H4; clear H4; intros; subst s'; tauto.
  Qed.
  
  Ltac psemTac :=
    match goal with
      H:psem _ _ ?sa |- psem _ _ ?sa' => assert (sa' = sa) as ae;
          try (rewrite ae; assumption); (apply functional_extensionality_dep; intros)
    end.

  Lemma lt_stable_env: forall env1 env2 V l t,
    lt_noX Sg l -> SV.set_In (T:=ltDec Sg) l V ->
   (forall l' (s' : Sort) (w : variable s'),
     SV.set_In (T:=ltDec Sg) l' V -> vsIn Sg w (lt_vars Sg l') -> env1 s' w = env2 s' w) ->
   lt_stable env1 l t -> lt_stable env2 l t.
  Proof.
    repeat (split || intro).
    generalize (H1 l); clear H1; intro H1.
    destruct l; simpl in *.
    subst n; simpl in *.
    assert (psem p t (fun i : Fin.t (pr_arity p) => tm_sem Sg env1 (t0 i))).    
    psemTac.
    destruct (t0 x) eqn:e; simpl; auto.
    apply H1; simpl; auto.
    apply SV.InCUnion_intro with (u:=x); simpl; try apply fin_all; simpl; intros.
    exact (fin_all (T:=uptoFinite (pr_arity p)) x).
    exact (fin_all (T:=uptoFinite (pr_arity p)) x).
    rewrite e; simpl; auto.
    apply vsSing_intro.
    apply H2 in H; simpl in H.
    psemTac.
    destruct (t0 x) eqn:e; simpl; auto.
    symmetry; apply H1; simpl; auto.
    apply SV.InCUnion_intro with (u:=x); simpl; try apply fin_all; simpl; intros.
    exact (fin_all (T:=uptoFinite (pr_arity p)) x).
    exact (fin_all (T:=uptoFinite (pr_arity p)) x).
    rewrite e; simpl; auto.
    apply vsSing_intro.
    
    generalize (H1 l); clear H1; intro H1.
    destruct l; simpl in *.
    subst n; simpl in *.
    assert (psem p (S t) (fun i : Fin.t (pr_arity p) => tm_sem Sg env1 (t0 i))).
    psemTac.
    destruct (t0 x) eqn:e; simpl; auto.
    apply H1; simpl; auto.
    apply SV.InCUnion_intro with (u:=x); simpl; try apply fin_all; simpl; intros.
    exact (fin_all (T:=uptoFinite (pr_arity p)) x).
    exact (fin_all (T:=uptoFinite (pr_arity p)) x).
    rewrite e; simpl; auto.
    apply vsSing_intro.
    apply H2 in H; simpl in H.
    psemTac.
    destruct (t0 x) eqn:e; simpl; auto.
    symmetry; apply H1; simpl; auto.
    apply SV.InCUnion_intro with (u:=x); simpl; try apply fin_all; simpl; intros.
    exact (fin_all (T:=uptoFinite (pr_arity p)) x).
    exact (fin_all (T:=uptoFinite (pr_arity p)) x).
    rewrite e; simpl; auto.
    apply vsSing_intro.
  Qed.
  
  Hypothesis stability:
    forall env t p m,
      fm_sem Sg env (inst p m) t -> lt_stable env (PApp Sg 0 p m) t.
  
  Theorem isStable_stable: 
    forall f V env t (fo: isFO Sg f) 
      (nx: forall l, SV.set_In (T:=ltDec Sg) l V -> lt_noX Sg l),
      (forall l, SV.set_In (T:=ltDec Sg) l V -> lt_stable env l t) ->
        isStable V f -> stable env f t.
  Proof.
    intros.
    revert env H; induction H0; intros; simpl in *; auto.
  - repeat (split || intro); simpl in *; auto.
  - repeat (split || intro); simpl in *; auto.
  - destruct a; simpl in *; auto.
    inversion H; clear H.
    apply H0 in H2; clear H0.
    repeat (split || intro); simpl in *; auto; apply H2; now auto.
    inversion H; clear H.
    apply H0 in H2; clear H0.    
    repeat (split || intro); simpl in *; apply H; apply H2; now auto.
    repeat (split || intro); simpl in *; now auto.
    repeat (split || intro); simpl in *; now auto.
  - apply stable_And.
    apply IHisStable1; clear IHisStable1 IHisStable2; intros; auto; try tauto.
    apply nx; apply H; now auto.
    apply H1; clear H1; intros; auto.
    apply H; now auto.
    apply IHisStable2; clear IHisStable1 IHisStable2; intros; auto; try tauto.
    apply nx; apply H0; now auto.
    apply H1; clear H1; intros; auto.
    apply H0; now auto.
  - apply stable_Or.
    apply IHisStable1; clear IHisStable1 IHisStable2; intros; auto; try tauto.
    apply nx; apply H; now auto.
    apply H1; clear H1; intros; auto.
    apply H; now auto.
    apply IHisStable2; clear IHisStable1 IHisStable2; intros; auto; try tauto.
    apply nx; apply H0; now auto.
    apply H1; clear H1; intros; auto.
    apply H0; now auto.
  - apply stable_All with (V:=V); intros.
    apply H; now auto.
    apply IHisStable; clear IHisStable; auto.
    intros.
    generalize (H1 _ H3); apply lt_stable_env with (V:=V); intros; auto.
    symmetry; apply H2 with (l:=l'); clear H2; intros; auto.
  - apply stable_Ex with (V:=V); intros.
    apply H; now auto.
    apply IHisStable; clear IHisStable; auto.
    intros.
    generalize (H1 _ H3); apply lt_stable_env with (V:=V); intros; auto.
    symmetry; apply H2 with (l:=l'); clear H2; intros; auto.
  - split; intro.
    rewrite Imp_sem in H0; rewrite Imp_sem; intro.
    destruct (classic (fm_sem Sg env (inst p m) t)).
    apply IHisStable1; clear IHisStable1; intros; auto; try tauto.
    apply SV.InAdd in H3; destruct H3; auto.
    subst l; simpl; now auto.
    apply SV.InAdd in H3; destruct H3; auto.    
    subst l.
    apply stability; now auto.
    exfalso; apply H2; clear H2.
    apply IHisStable2; intros; auto; try tauto.
    apply inst_FO.
    
    rewrite Imp_sem in H0; rewrite Imp_sem; intro.
    assert (fm_sem Sg env (inst p m) (S t)).
    apply IHisStable2; clear IHisStable2; intros; auto; try tauto.
    apply inst_FO.
    apply H0 in H2.
    apply IHisStable1; clear IHisStable1; intros; auto; try tauto.
    apply SV.InAdd in H3; destruct H3; auto.
    subst l; simpl; now auto.
    apply SV.InAdd in H3; destruct H3; auto.    
    subst l.
    apply stability; now auto.
  Qed.
  
End Stability.
