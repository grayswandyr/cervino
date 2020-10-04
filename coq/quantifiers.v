Add LoadPath "$HOME/COQ/FO-LTL" as Top.

Require Import Coq.Logic.FunctionalExtensionality.
Require Import Eqdep_dec.
Require Import ProofIrrelevance.

Require Import Top.foltl.
Require Import Top.dec.
Require Import Top.finite.
Require Import Top.set.
Require Import Top.env.
Require Import Top.varset.
Require Import Top.fosem.
Require Import Top.vars.


  Fixpoint getEx `{Sg: Sig} (f: formula Sg): VarSet Sg :=
  match f with
  | Ex _ s v f => vsAdd _ v (getEx f)
  | _ => vsEmpty _
  end.

  Fixpoint getAll `{Sg: Sig} (f: formula Sg): VarSet Sg :=
  match f with
  | All _ s v f => vsAdd _ v (getAll f)
  | _ => vsEmpty _
  end.
  
  Fixpoint EX `{Sg: Sig} (f: formula Sg): formula Sg :=
  match f with
  | Ex _ s v f => EX f
  | _ => f
  end.

  Fixpoint ALL `{Sg: Sig} (f: formula Sg): formula Sg :=
  match f with
  | All _ s v f => ALL f
  | _ => f
  end.

  Definition EX_ALL `{Sg: Sig} (f: formula Sg): formula Sg :=
    ALL (EX f).

  Program Definition mkEx `{Sg: Sig} (vs: VarSet Sg) (f: formula Sg) :=
    IEx Sg (vsFinite Sg vs) (fun k => projT1 k) (fun k => projT2 k) f.
  
  Program Definition mkAll `{Sg: Sig} (vs: VarSet Sg) (f: formula Sg) :=
    IAll Sg (vsFinite Sg vs) (fun k => projT1 k) (fun k => projT2 k) f.
  
  Ltac psemTac :=
    match goal with
      H:psem _ _ ?sa |- psem _ _ ?sa' => assert (sa' = sa) as ae;
          try (rewrite ae; assumption); (apply functional_extensionality_dep; intros)
    end.
  
  Lemma iaddEmpty: forall `{Sg: Sig} (D: Dom Sg) sk vk dk (env: Env Sg D),
    iadd Sg (vsFinite Sg (vsEmpty Sg)) sk vk dk env = env.
  Proof.
    intros.
    apply functional_extensionality_dep; intro s.
    apply functional_extensionality_dep; intro v.
    unfold iadd; simpl.
    match goal with |- match ?cnd with _=>_ end =_=> destruct cnd; simpl; auto end.
    destruct s0; simpl in *.
    destruct x.
    destruct e; tauto.
  Qed.

  Lemma foldl_empty: forall `(T: EqDec) R (f: R -> T -> R) (a: R) (l: list T),
    SV.is_empty l -> List.fold_left f l a = a.
  Proof.
    intros.
    destruct l; simpl; auto.
    exfalso; apply (H e); simpl; auto.
  Qed.

  Lemma foldr_empty: forall `(T: EqDec) R (f: T -> R -> R) (a: R) (l: list T),
    SV.is_empty l -> List.fold_right f a l = a.
  Proof.
    intros.
    destruct l; simpl; auto.
    exfalso; apply (H e); simpl; auto.
  Qed.

  Lemma addlEmpty: forall `{Sg: Sig} (D: Dom Sg) sk vk dk (env: Env Sg D),
    addl Sg (vsFinite Sg (vsEmpty Sg)) sk vk dk env = env.
  Proof.
    intros.
    unfold addl.
    apply functional_extensionality_dep; intro s.
    apply functional_extensionality_dep; intro v.    
    destruct (last_dec
     (fun k : vsFinite Sg (vsEmpty Sg) => isEq2 (sk k) (vk k) s v)); auto.
    destruct s0 as [[k h1] h2].
    destruct h1.
    destruct s0.
  Qed.

  Lemma addrEmpty: forall `{Sg: Sig} (D: Dom Sg) sk vk dk (env: Env Sg D),
    addr Sg (vsFinite Sg (vsEmpty Sg)) sk vk dk env = env.
  Proof.
    intros.
    unfold addr.
    apply functional_extensionality_dep; intro s.
    apply functional_extensionality_dep; intro v.    
    destruct (first_dec
     (fun k : vsFinite Sg (vsEmpty Sg) => isEq2 (sk k) (vk k) s v)); auto.
    destruct s0 as [[k h1] h2].
    destruct h1.
    destruct s0.
  Qed.
  
  Ltac fm_semTac :=
    match goal with
      H: fm_sem _ ?e1 ?f ?t |- fm_sem _ ?e2 ?f ?t => assert (e1 = e2) as eeq;
        try (rewrite eeq in H; assumption); 
        apply functional_extensionality_dep; intro; 
        apply functional_extensionality_dep; intro
    end.
  
  Lemma tm_iaddEmpty: forall `{Sg: Sig} {D: Dom Sg} (Itp: Interp D) {s} (tm: term Sg s) sk vk dk (env: Env _ D),
    tm_sem Sg
      (iadd Sg (vsFinite Sg (vsEmpty Sg))
         sk vk dk env) tm = tm_sem Sg env tm.
  Proof.
    intros.
    rewrite (iaddEmpty D); auto.
  Qed.

  Lemma tm_addlEmpty: forall `{Sg: Sig} {D: Dom Sg} (Itp: Interp D) {s} (tm: term Sg s) sk vk dk (env: Env _ D),
    tm_sem Sg
      (addl Sg (vsFinite Sg (vsEmpty Sg))
         sk vk dk env) tm = tm_sem Sg env tm.
  Proof.
    intros.
    rewrite (addlEmpty D); auto.
  Qed.

  Lemma tm_addrEmpty: forall `{Sg: Sig} {D: Dom Sg} (Itp: Interp D) {s} (tm: term Sg s) sk vk dk (env: Env _ D),
    tm_sem Sg
      (addr Sg (vsFinite Sg (vsEmpty Sg))
         sk vk dk env) tm = tm_sem Sg env tm.
  Proof.
    intros.
    rewrite (addrEmpty D); auto.
  Qed.

  Lemma at_iaddEmpty: forall `{Sg: Sig} {D: Dom Sg} (Itp: Interp D) sk vk dk (env: Env _ D) (a: atom Sg) t,
    at_sem Sg
      (iadd Sg (vsFinite Sg (vsEmpty Sg))
         sk vk dk env) a t <-> at_sem Sg env a t.
  Proof.
    intros.
    rewrite (iaddEmpty D); reflexivity.
  Qed.

  Lemma at_laddEmpty: forall `{Sg: Sig} {D: Dom Sg} (Itp: Interp D) sk vk dk (env: Env _ D) (a: atom Sg) t,
    at_sem Sg
      (addl Sg (vsFinite Sg (vsEmpty Sg))
         sk vk dk env) a t <-> at_sem Sg env a t.
  Proof.
    intros.
    rewrite (addlEmpty D); reflexivity.
  Qed.

  Lemma at_raddEmpty: forall `{Sg: Sig} {D: Dom Sg} (Itp: Interp D) sk vk dk (env: Env _ D) (a: atom Sg) t,
    at_sem Sg
      (addr Sg (vsFinite Sg (vsEmpty Sg))
         sk vk dk env) a t <-> at_sem Sg env a t.
  Proof.
    intros.
    rewrite (addrEmpty D); reflexivity.
  Qed.
  
  Lemma fm_iaddEmpty: forall `{Sg: Sig} {D: Dom Sg} (Itp: Interp D) sk vk dk (f: formula Sg) (env: Env _ D)  t,
    fm_sem Sg
      (iadd Sg (vsFinite Sg (vsEmpty Sg))
         sk vk dk env) f t <-> fm_sem Sg env f t.
  Proof.
    intros.
    rewrite (iaddEmpty D); reflexivity.
  Qed.

  Lemma fm_addlEmpty: forall `{Sg: Sig} {D: Dom Sg} (Itp: Interp D) sk vk dk (f: formula Sg) (env: Env _ D)  t,
    fm_sem Sg
      (addl Sg (vsFinite Sg (vsEmpty Sg))
         sk vk dk env) f t <-> fm_sem Sg env f t.
  Proof.
    intros.
    rewrite (addlEmpty D); reflexivity.
  Qed.

  Lemma fm_addrEmpty: forall `{Sg: Sig} {D: Dom Sg} (Itp: Interp D) sk vk dk (f: formula Sg) (env: Env _ D)  t,
    fm_sem Sg
      (addr Sg (vsFinite Sg (vsEmpty Sg))
         sk vk dk env) f t <-> fm_sem Sg env f t.
  Proof.
    intros.
    rewrite (addrEmpty D); reflexivity.
  Qed.
  
  Lemma IEx_empty: forall `{Sg: Sig} (D: Dom Sg) (Itp: Interp D) sk vk f (env: Env Sg D) t,
    fm_sem Sg env (IEx Sg (vsFinite Sg (vsEmpty Sg)) sk vk f) t <-> fm_sem Sg env f t.
  Proof.
    intros; simpl; split; intros; auto.
    apply IEx_sem in H.
    destruct H as [dk H].
    rewrite (addlEmpty D) in H; auto.

    apply IEx_sem.
    exists (fun (k : {x : Sort & {_ : variable x | False}}) => 
      match proj2_sig (projT2 k) with end); auto.
   rewrite (addlEmpty D); auto.
  Qed.
  
  Lemma not_not: forall (P:Prop), ~ (~ P) <-> P.
  Proof.
    intros.
    tauto.
  Qed.
  
  Lemma Not_mkAll: forall `{Sg: Sig} e (f: formula Sg),
    Not Sg (mkAll e f) = mkEx e (Not _ f).
  Proof.
    unfold mkAll, mkEx.
    induction f; simpl; intros; auto; apply (Not_IAll Sg).
  Qed.
  
  Lemma Not_ALL: forall `{Sg: Sig} (f: formula Sg),
    (Not Sg (ALL f)) = EX (Not _ f).
  Proof.
    induction f; simpl; intros; auto.
  Qed.
  
  Lemma getEx_Not: forall `{Sg: Sig} (f: formula Sg),
    getEx (Not Sg f) = getAll f.
  Proof.
    induction f; simpl; intros; auto.
    rewrite IHf; auto.
  Qed.
  
  Definition getExAll `{Sg: Sig} (f: formula Sg) := let g := EX f in (getEx f, getAll g).

  Lemma getEx_equiv: forall `{Sg: Sig} (D: Dom Sg) (Itp: Interp D) e,
    forall (f1 f2: formula Sg), (forall env t, fm_sem Sg env f1 t <-> fm_sem Sg env f2 t) ->
      (forall env t, fm_sem Sg env (mkEx e f1) t <-> fm_sem Sg env (mkEx e f2) t).
  Proof.
    unfold mkEx; simpl; intros; split; intros.
    apply IEx_sem in H0; apply IEx_sem.
    destruct H0 as [dk H0].
    exists dk.
    revert H0; apply H.
    apply IEx_sem in H0; apply IEx_sem.
    destruct H0 as [dk H0].
    exists dk.
    revert H0; apply H.    
  Qed.
  
  Lemma isAll_Prop: forall `{Sg: Sig} (f: formula Sg),
    isAll _ f -> isProp _ (ALL f).
  Proof.
    induction f; simpl; intros; auto.
  Qed.
  
  Lemma isExAll_Prop: forall `{Sg: Sig} (f: formula Sg),
    isExAll _ f -> isProp _ (EX_ALL f).
  Proof.
    induction f; simpl; intros; auto.
    unfold EX_ALL in *; simpl in *; auto.
    apply isAll_Prop; auto.
  Qed.

  Lemma mkAll_sem: forall `{Sg: Sig} (D: Dom Sg) (Itp: Interp D) (f: formula Sg) vars t,
    (forall env, fm_sem Sg env (mkAll vars f) t) <-> (forall env, fm_sem Sg env f t).
  Proof.
    intros.
    split; intros.

    unfold mkAll in H; simpl in H.
    set (dk (k: {x : Sort & {x0 : variable x | SV.set_In x0 (vars x)}}) :=
      match k return ssem (projT1 k) with
        existT _ s (exist _ v h) => env s v
      end).
    simpl in dk.
    setoid_rewrite IAll_sem in H.
    specialize H with env dk.
    revert H; apply fm_sem_equiv; intros; auto.
    unfold addl; simpl.
    match goal with |- _=match ?cnd with _=>_ end => destruct cnd; auto end.
    destruct s0; auto.
    simpl in d.
    destruct x; simpl in *.
    destruct e; simpl in *.
    injection d; intros; subst.
    apply inj_pair2_eq_dec in H0; try apply eq_dec; subst; auto.
    rewrite (proof_irrelevance _ d eq_refl); auto.

    unfold mkAll.
    apply IAll_sem; intros.
    apply H.
  Qed.


  Lemma semAll_intro: forall `{Sg: Sig} (D: Dom Sg) env (Itp: Interp D) (f: formula Sg) (V: VarSet Sg) t,
    (forall pe:pEnv D V,  fm_sem Sg (pAdd env pe) f t) ->
      fm_sem Sg env (mkAll V f) t.
  Proof.
    intros.
    unfold mkAll; simpl; intros.
    apply IAll_sem; intros.
    unfold addl; simpl.
    set (pe := fun s v h => dk (existT _ s (exist _ v h))).
    simpl in pe; specialize H with pe.
    revert H; apply fm_sem_equiv; intros; auto.
    match goal with |- match ?cnd with _=>_ end=_ => destruct cnd end.
    destruct s0; simpl in *; auto.
    destruct x as [s0 [w h]]; simpl in *.
    injection d; intros; subst s0.
    apply inj_pair2_eq_dec in H0; try apply eq_dec; subst w.
    rewrite (proof_irrelevance _ d eq_refl).
    unfold pAdd.
    destruct (SV.set_In_dec v (V s)); try tauto.
    unfold pe.
    rewrite (proof_irrelevance _ i h); reflexivity.
    
    generalize (fun k => n k (fin_all k)); clear n; intro n.
    
    simpl in *.
    unfold pAdd.
    destruct (SV.set_In_dec v (V s)); auto.
    specialize n with (existT (fun x => {x0 : variable x | SV.set_In x0 (V x)}) s (exist (fun x0 => SV.set_In x0 (V s)) v i)).
    simpl in n.
    exfalso; apply n; intros; auto.
  Qed.

  Lemma semAll_elim: forall `{Sg: Sig} (D: Dom Sg) env (Itp: Interp D) (f: formula Sg) (V: VarSet Sg) t,
    fm_sem Sg env (mkAll V f) t ->
      (forall pe:pEnv D V,  fm_sem Sg (pAdd env pe) f t).
  Proof.
    intros.
    unfold mkAll in H; simpl in H; intros.
    unfold addl in H; simpl in H.
    set (dk k := match k return ssem (projT1 k) with
        existT _ s (exist _ v h) => pe s v h end).
    setoid_rewrite IAll_sem in H.
    simpl in dk; specialize H with dk.
    revert H; apply fm_sem_equiv; intros; auto.
    unfold addl.
    match goal with |- _=match ?cnd with _=>_ end => destruct cnd end.
    destruct s0; simpl in *; auto.
    destruct x as [s0 [w h]]; simpl in *.
    injection d; intros; subst s0.
    apply inj_pair2_eq_dec in H0; try apply eq_dec; subst.
    rewrite (proof_irrelevance _ d eq_refl).
    unfold pAdd.
    destruct (SV.set_In_dec v (V s)); try tauto.
    rewrite (proof_irrelevance _ i h); reflexivity.
    
    generalize (fun k => n k (fin_all k)); clear n; intro n.
    simpl in *.
    unfold pAdd.
    destruct (SV.set_In_dec v (V s)); auto.
    specialize n with (existT (fun s => {x0 : variable s | SV.set_In x0 (V s)}) s (exist (fun x0 => SV.set_In x0 (V s)) v i)).
    simpl in n.
    tauto.
  Qed.

  Lemma semEx_intro: forall `{Sg: Sig} (D: Dom Sg) env (Itp: Interp D) (f: formula Sg) (V: VarSet Sg) t,
    (exists pe:pEnv D V,  fm_sem Sg (pAdd env pe) f t) ->
      fm_sem Sg env (mkEx V f) t.
  Proof.
    intros.
    unfold mkEx; simpl; intros.
    destruct H as [pe H].
    set (dk k := match k return ssem (projT1 k) with
        existT _ s (exist _ v h) => pe s v h end).
    apply IEx_sem.
    simpl in dk; exists dk.
    revert H; apply fm_sem_equiv; intros; auto.
    unfold addl.
    match goal with |- match ?cnd with _=>_ end=_ => destruct cnd end.
    destruct s0; simpl in *; auto.
    destruct x as [s0 [w h]]; simpl in *.
    injection d; intros; subst s0.
    apply inj_pair2_eq_dec in H0; try apply eq_dec; subst.
    rewrite (proof_irrelevance _ d eq_refl).
    unfold pAdd.
    destruct (SV.set_In_dec v (V s)); try tauto.
    rewrite (proof_irrelevance _ i h); reflexivity.
    
    generalize (fun k => n k (fin_all k)); clear n; intro n. 
    simpl in *.
    unfold pAdd.
    destruct (SV.set_In_dec v (V s)); auto.
    specialize n with (existT (fun x => {x0 : variable x | SV.set_In x0 (V x)}) s (exist (fun x0 => SV.set_In x0 (V s)) v i)).
    simpl in n; tauto.
  Qed.
  
  Lemma semEx_elim: forall `{Sg: Sig} (D: Dom Sg) env (Itp: Interp D) (f: formula Sg) (V: VarSet Sg) t,
    fm_sem Sg env (mkEx V f) t ->
      exists pe:pEnv D V,  fm_sem Sg (pAdd env pe) f t.
  Proof.
    intros.
    unfold mkEx in H; simpl in H; intros.
    apply IEx_sem in H.
    destruct H as [dk H].
    unfold addl in H; simpl in H.
    set (pe := fun s v h => dk (existT _ s (exist _ v h))).
    simpl in pe; exists pe.
    revert H; apply fm_sem_equiv; intros; auto.
    match goal with |- _=match ?cnd with _=>_ end => destruct cnd end.
    destruct s0; simpl in *; auto.
    destruct x as [s0 [w h]]; simpl in *.
    injection d; intros; subst s0.
    apply inj_pair2_eq_dec in H0; try apply eq_dec; subst.
    rewrite (proof_irrelevance _ d eq_refl).
    unfold pAdd.
    destruct (SV.set_In_dec v (V s)); try tauto.
    unfold pe.
    rewrite (proof_irrelevance _ i h); reflexivity.
    
    generalize (fun k => n k (fin_all k)); clear n; intro n. 
    simpl in *.
    unfold pAdd.
    destruct (SV.set_In_dec v (V s)); auto.
    specialize n with (existT (fun x => {x0 : variable x | SV.set_In x0 (V x)}) s (exist (fun x0 => SV.set_In x0 (V s)) v i)).
    simpl in n.
    tauto.
  Qed.

  Lemma mkEx_intro: forall `{Sg: Sig} (D: Dom Sg) (Itp: Interp D) (f: formula Sg) env vars t,
    fm_sem Sg env f t -> fm_sem Sg env (mkEx vars f) t.
  Proof.
    intros.
    apply semEx_intro.
    exists (fun s v h => env s v).
    revert H; apply fm_sem_equiv; intros; auto.
    unfold pAdd.
    destruct (SV.set_In_dec v (vars s)); auto.
  Qed.

  Lemma ALL_IAll: forall `{Sg: Sig} `(K: Finite) sk (vk: forall k, variable (sk k)) (f: formula Sg) , ALL (IAll Sg K sk vk f) = ALL f.
  Proof.
    induction f; simpl; intros; auto;
      try (unfold IAll; induction fin_set; simpl; intros; tauto).
  Qed.

  Lemma EX_IEx: forall `{Sg: Sig} `(K: Finite) sk (vk: forall k, variable (sk k)) (f: formula Sg) , EX (IEx Sg K sk vk f) = EX f.
  Proof.
    induction f; simpl; intros; auto;
      try (unfold IEx; induction fin_set; simpl; intros; tauto).
  Qed.

  Lemma ALL_mkAll: forall `{Sg: Sig} (f: formula Sg) (V: VarSet Sg),
    ALL (mkAll V f) = ALL f.
  Proof.
    intros.
    apply ALL_IAll.
  Qed.
  
  Lemma EX_mkEX: forall `{Sg: Sig} (f: formula Sg) (V: VarSet Sg),
    EX (mkEx V f) = EX f.
  Proof.
    intros; apply EX_IEx.
  Qed.

  Lemma EX_EX: forall `{Sg: Sig} (f: formula Sg), EX (EX f) = EX f.
  Proof.
    induction f; simpl; intros; auto.
  Qed.
  
  Definition empty_pEnv `{Sg: Sig} (D: Dom Sg) : pEnv D (vsEmpty Sg).
    repeat intro.
    destruct H.
  Defined.
  
  Lemma mkAll_empty: forall `{Sg: Sig} (D: Dom Sg) (Itp: Interp D) (f: formula Sg) env t,
    fm_sem Sg env (mkAll (vsEmpty Sg) f) t <-> fm_sem Sg env f t.
  Proof.
    intros.
    split; intro.
    
    apply (semAll_elim D) with (pe := empty_pEnv D) in H.
    revert H; apply fm_sem_equiv; intros; now auto.
    
    apply semAll_intro; intro.
    revert H; apply fm_sem_equiv; intros; now auto.
  Qed.

  Lemma mkEx_free: forall `{Sg: Sig} (D: Dom Sg) env (Itp: Interp D) (f: formula Sg) (V: VarSet Sg) t,
    fm_sem Sg env (mkEx V f) t <->
      fm_sem Sg env (mkEx (vsInter Sg V (free Sg f)) f) t.
  Proof.
    intros.
    split; intro.
    apply semEx_elim in H.
    destruct H as [pe H].
    apply semEx_intro.
    exists (fun s v (h: SV.set_In v (vsInter Sg V (free Sg f) s)) => pe s v (proj1 (vsInter_elim _ h))).
    revert H; apply fm_sem_equiv; intros.
    unfold pAdd; simpl.
    destruct (SV.set_In_dec v (vsInter Sg V (free Sg f) s)).
    destruct (SV.set_In_dec v (V s)).
    rewrite (proof_irrelevance _ _ i0); auto.
    exfalso; apply vsInter_elim in i; tauto.
    destruct (SV.set_In_dec v (V s)); auto.
    exfalso; apply n; clear n; apply vsInter_intro; tauto.

    apply semEx_elim in H.
    destruct H as [pe H].
    apply semEx_intro.
    set (pe' := fun s v (h: SV.set_In v (V s)) =>
      match SV.set_In_dec v (free Sg f s) with
        left h' => pe s v (vsInter_intro _ h h')
      | right h' => neDom s
      end).
    exists pe'.
    
    revert H; apply fm_sem_equiv; intros.
    unfold pAdd, pe'; simpl.
    destruct (SV.set_In_dec v (vsInter Sg V (free Sg f) s)).
    destruct (SV.set_In_dec v (V s)).
    destruct (SV.set_In_dec v (free Sg f s)); try tauto.
    rewrite (proof_irrelevance _ _ i); auto.
    exfalso; apply vsInter_elim in i; tauto.
    destruct (SV.set_In_dec v (V s)); auto.
    destruct (SV.set_In_dec v (free Sg f s)); try tauto.
    exfalso; apply n; clear n; apply vsInter_intro; tauto.
  Qed.
  
   Lemma vsUnionCases: forall `{Sg: Sig} `{K:Finite} {sk:K->Sort} {vk: forall k, variable (sk k)} {V: VarSet _} {s} {v:variable s},
    SV.set_In v (vsUnion Sg (vsVars Sg vk) V s) ->
    ~ SV.set_In v (V s) ->
    (forall k : K, ~ (isEq2 (U:=variable) (sk k) (vk k) s v)) ->
    False.
  Proof.
    intros.
    apply vsUnion_elim in H; destruct H.
    apply vsVars_elim in H.
    destruct H as [k H].
    specialize H1 with k.
    apply H1; clear H1.
    apply H.
    apply (H0 H).
  Qed.

   Lemma vsAddCases: forall `{Sg: Sig} {e: VarSet Sg} {s s'} {x: variable s} {v:variable s'},
    vsIn Sg v (vsAdd Sg x e) ->
    ~ vsIn Sg v e ->
    (~ isEq2 (U:=variable) s x s' v) ->
    False.
  Proof.
    intros.
    apply vsAdd_elim in H; destruct H.
    unfold isEq2 in *; simpl in *.
    symmetry in H; tauto.
    apply (H0 H).
  Qed.
  
  Lemma pAdd_iadd: forall `{Sg: Sig} (D: Dom Sg) (env: Env Sg D) `(K: Finite) sk vk (V: VarSet Sg) (pe: pEnv D (vsUnion Sg (vsVars Sg vk) V)) s' v',
  pAdd env pe s' v' =
  pAdd
  (iadd Sg K sk vk
     (fun k => pe (sk k) (vk k) (vsUnion_l Sg (vsVars_intro Sg vk k))) env)
     (fun (s : Sort) (v : variable s) (h : SV.set_In v (V s))
      => pe s v (vsUnion_r Sg h)) s' v'.
  Proof.
    intros.
    unfold pAdd, iadd.
    destruct (SV.set_In_dec v' (V s')).
    destruct (SV.set_In_dec v' (vsUnion Sg (vsVars Sg vk) V s')).
    f_equal; apply proof_irrelevance.
    exfalso; apply n; clear n.
    apply vsUnion_r; auto.
    
    destruct (ex_dec (fun k : K => isEq2 (sk k) (vk k) s' v')).
    destruct s.
    simpl in d.
    injection d; intros; subst s'.
    generalize d; intro d'.
    apply inj_pair2_eq_dec in d; try apply eq_dec; subst v'.
    rewrite (proof_irrelevance _ d' eq_refl).
    destruct (SV.set_In_dec (vk x) (vsUnion Sg (vsVars Sg vk) V (sk x))).
    f_equal; apply proof_irrelevance.

    exfalso; apply n0.
    apply vsUnion_l.
    apply vsVars_intro.
    
    destruct (SV.set_In_dec v' (vsUnion Sg (vsVars Sg vk) V s')); auto.
    exfalso; apply vsUnion_elim in i.
    destruct i.
    apply vsVars_elim in H.
    destruct H as [k H].
    apply (n0 k H).
    apply (n H).
  Qed.

  Lemma pAdd_addl: forall `(Sg: Sig) (D: Dom Sg) (env: Env Sg D) `(K: Finite) sk vk (V: VarSet Sg) (pe: pEnv D (vsUnion Sg (vsVars Sg vk) V)) s' v',
  pAdd env pe s' v' =
  pAdd
  (addl Sg K sk vk
     (fun k => pe (sk k) (vk k) (vsUnion_l Sg (vsVars_intro Sg vk k))) env)
     (fun (s : Sort) (v : variable s) (h : SV.set_In v (V s))
      => pe s v (vsUnion_r Sg h)) s' v'.
  Proof.
    intros.
    unfold pAdd, addl.
    destruct (SV.set_In_dec v' (V s')).
    destruct (SV.set_In_dec v' (vsUnion Sg (vsVars Sg vk) V s')).
    f_equal; apply proof_irrelevance.
    exfalso; apply n; clear n.
    apply vsUnion_r; auto.
    
    destruct (last_dec (fun k : K => isEq2 (sk k) (vk k) s' v')).
    destruct s.
    simpl in d.
    injection d; intros; subst s'.
    generalize d; intro d'.
    apply inj_pair2_eq_dec in d; try apply eq_dec; subst v'.
    rewrite (proof_irrelevance _ d' eq_refl).
    destruct (SV.set_In_dec (vk x) (vsUnion Sg (vsVars Sg vk) V (sk x))).
    f_equal; apply proof_irrelevance.

    exfalso; apply n0.
    apply vsUnion_l.
    apply vsVars_intro.
    
    destruct (SV.set_In_dec v' (vsUnion Sg (vsVars Sg vk) V s')); auto.
    exfalso; apply vsUnion_elim in i.
    destruct i.
    apply vsVars_elim in H.
    destruct H as [k H].
    apply (n0 k (fin_all k) H).
    apply (n H).
  Qed.

  Lemma pAdd_iadd2: forall `{Sg: Sig} (D: Dom Sg) V env (pe: pEnv D V) `(K: Finite) sk vk dk s' v',
  pAdd (iadd Sg K sk vk dk env) pe s' v' =
  pAdd env
  (fun (s : Sort) (v : variable s)
     (h : SV.set_In v (vsUnion Sg (vsVars Sg vk) V s)) =>
   match SV.In_dec v (V s) with
   | left h1 => pe s v h1
   | right h2 =>
       match ex_dec (fun k : K => isEq2 (U:=variable) (sk k) (vk k) s v) with
       | inleft (exist _ k hk) =>
           match inj_pairT1 hk in (_ = s') return (ssem s') with
           | eq_refl => dk k
           end
       | inright nh =>
           match vsUnionCases h h2 nh return (ssem s) with
           end
       end
   end) s' v'.
  Proof.
    intros.
    unfold pAdd, iadd.
    destruct (SV.set_In_dec v' (vsUnion Sg (vsVars Sg vk) V s')); auto.
    unfold SV.set_In_dec, SV.In_dec.
    destruct (List.in_dec eq_dec v' (V s')); auto.
    destruct (ex_dec (fun k : K => isEq2 (sk k) (vk k) s' v')); auto.
    destruct s; auto.
    match goal with
      |- _=match ?cnd with _=>_ end => destruct cnd; auto
    end.
    generalize d; intro d'.
    apply inj_pair2_eq_dec in d; try apply eq_dec; subst v'; auto.
    rewrite (proof_irrelevance _ d' eq_refl); auto.
    destruct (vsUnionCases i n n0).

    destruct (SV.set_In_dec v' (V s')); auto.
    exfalso; apply n; clear n.
    apply vsUnion_r; auto.
    
    destruct (ex_dec (fun k : K => isEq2 (sk k) (vk k) s' v')); auto.
    destruct s; auto.
    assert (sk x = s').
    injection d; intro; subst; auto.
    subst s'.
    assert (vk x = v').
    apply inj_pair2_eq_dec in d; try apply eq_dec; subst; auto.
    subst v'.
    exfalso; apply n.
    apply vsUnion_l.
    apply vsVars_intro.
  Qed.

  Lemma pAdd_addl2: forall `{Sg: Sig} (D: Dom Sg) V env (pe: pEnv D V) `(K: Finite) sk vk dk s' v',
  pAdd (addl Sg K sk vk dk env) pe s' v' =
  pAdd env
  (fun (s : Sort) (v : variable s)
     (h : SV.set_In v (vsUnion Sg (vsVars Sg vk) V s)) =>
   match SV.In_dec v (V s) with
   | left h1 => pe s v h1
   | right h2 =>
       match last_dec (fun k : K => isEq2 (U:=variable) (sk k) (vk k) s v) with
       | inleft (exist _ k hk) =>
           match inj_pairT1 hk in (_ = s') return (ssem s') with
           | eq_refl => dk k
           end
       | inright nh =>
           match vsUnionCases h h2 (fun k => nh k (fin_all k)) return (ssem s) with
           end
       end
   end) s' v'.
  Proof.
    intros.
    unfold pAdd, addl.
    destruct (SV.set_In_dec v' (vsUnion Sg (vsVars Sg vk) V s')); auto.
    unfold SV.set_In_dec, SV.In_dec.
    destruct (List.in_dec eq_dec v' (V s')); auto.
    destruct (last_dec (fun k : K => isEq2 (sk k) (vk k) s' v')); auto.
    destruct s; auto.
    match goal with
      |- _=match ?cnd with _=>_ end => destruct cnd; auto
    end.
    generalize d; intro d'.
    apply inj_pair2_eq_dec in d; try apply eq_dec; subst v'; auto.
    rewrite (proof_irrelevance _ d' eq_refl); auto.
    destruct (vsUnionCases i n (fun k => n0 k (fin_all k))).

    destruct (SV.set_In_dec v' (V s')); auto.
    exfalso; apply n; clear n.
    apply vsUnion_r; auto.
    
    destruct (last_dec (fun k : K => isEq2 (sk k) (vk k) s' v')); auto.
    destruct s; auto.
    assert (sk x = s').
    injection d; intro; subst; auto.
    subst s'.
    assert (vk x = v').
    apply inj_pair2_eq_dec in d; try apply eq_dec; subst; auto.
    subst v'.
    exfalso; apply n.
    apply vsUnion_l.
    apply vsVars_intro.
  Qed.
  
  Lemma EX_sem_elim: forall `{Sg: Sig} (D: Dom Sg) f,
    forall Itp env t, fm_sem Sg (Itp:=Itp) env (mkEx (getEx f) (EX f)) t -> fm_sem Sg (Itp:=Itp) env f t.
  Proof.
    induction f; intros; auto;
    match goal with
      |- fm_sem _ _ (Ex _ _ _ _) _  => idtac
    | _ => revert H; apply IEx_empty
    end.
    
    change (EX (Ex Sg s e f)) with (EX f) in H.
    apply semEx_elim in H.
    destruct H as [pe H].
    simpl.
    simpl in pe.
    exists (pe s e (vsAdd_l _ _ _)).
    apply IHf; clear IHf.
    apply semEx_intro.
    exists (fun s v h => pe s v (vsAdd_r _ _ _ h)).
    revert H; apply fm_sem_equiv; intros.
    
    unfold pAdd.
    simpl.
    destruct (SV.set_In_dec v (getEx f s0)).
    destruct (SV.set_In_dec v (vsAdd Sg e (getEx f) s0)).
    rewrite (proof_irrelevance _ _ i0); now auto.
    exfalso; apply n; apply vsAdd_r; now auto.
    destruct (SV.set_In_dec v (vsAdd Sg e (getEx f) s0)).
    destruct (vsAdd_elim _ _ _ i); intros.
    injection H0; intros; subst s0.
    apply inj_pair2_eq_dec in H0; try apply eq_dec; subst e.
    unfold add.
    destruct (eq_dec s s); try tauto.
    rewrite (proof_irrelevance _ _ eq_refl).
    destruct (eq_dec v v); try tauto.
    rewrite (proof_irrelevance _ _ i); now auto.
    tauto.
    rewrite add_ne2; auto.
    intro.
    injection H0; intros; subst s0.
    apply inj_pair2_eq_dec in H0; try apply eq_dec; subst e.
    apply n0; apply vsAdd_l.
  Qed.

  Lemma EX_sem_intro: forall `{Sg: Sig} (D: Dom Sg) f,
    forall Itp env t, fm_sem Sg (Itp:=Itp) env f t -> fm_sem Sg (Itp:=Itp) env (mkEx (getEx f) (EX f)) t.
  Proof.
    induction f; intros;
    match goal with
      H: fm_sem _ _ (Ex _ _ _ _) _ |- _ => idtac
    | _ => revert H; apply IEx_empty
    end.
    
    change (EX (Ex Sg s e f)) with (EX f).
    apply semEx_intro.
    simpl in H.
    destruct H as [d H].
    apply IHf in H; clear IHf.
    apply semEx_elim in H.
    destruct H as [pe H].
    simpl.
    exists (fun s' (v: variable (Tv:=Tv) s') (h: vsIn Sg v (vsAdd Sg e (getEx f))) =>
      match SV.In_dec v (getEx f s') with
        left h1 => pe s' v h1
      | right h2 => 
        match @dc_dec (isEq2 (U:=variable) s e s' v) with 
          left hk => 
            match (inj_pairT1 hk) in _=s' return ssem s' with eq_refl => d end
        | right nh => match (vsAddCases h h2 nh) with end
        end
      end).
    revert H; apply fm_sem_equiv; intros; auto.

    unfold pAdd.
    destruct (SV.set_In_dec v (vsAdd Sg e (getEx f) s0)).
    destruct (vsAdd_elim _ _ _ i).
    injection H0; intros; subst s0.
    apply inj_pair2_eq_dec in H0; try apply eq_dec; subst e.
    destruct (SV.In_dec v (getEx f s)); auto.
    destruct (SV.set_In_dec v (getEx f s)); try tauto.
    rewrite (proof_irrelevance _ i0 s0); now auto.
    destruct ( SV.set_In_dec v (getEx f s)); simpl in *; try tauto.
    destruct (dec.isEq2_obligation_1 _ Sort _ (fun x : Sort => variable x) s v s v); try tauto.
    destruct (vsAddCases i n n0).
    destruct (  dec.isEq2_obligation_1 _ Sort _ (fun x : Sort => variable x) s v s v); try tauto.
    rewrite (proof_irrelevance _ _ eq_refl).
    rewrite add_eq; now auto.
    destruct (vsAddCases i n n1).
    simpl in *.
    destruct (SV.In_dec v (getEx f s0)); try tauto.
    destruct (SV.set_In_dec v (getEx f s0)); try tauto.
    rewrite (proof_irrelevance _ s1 i0); now auto.
    destruct (n H0).
    destruct (SV.set_In_dec v (getEx f s0)).
    exfalso; apply n.
    apply vsAdd_r; tauto.
    rewrite add_ne2; auto.
    intro.
    injection H0; intros; subst s0.
    apply inj_pair2_eq_dec in H0; try apply eq_dec; subst e.
    apply n; apply vsAdd_l.
  Qed.

  Lemma EX_sem: forall `{Sg: Sig} (D: Dom Sg) f,
    forall Itp env t, fm_sem Sg (Itp:=Itp) env (mkEx (getEx f) (EX f)) t <-> fm_sem Sg (Itp:=Itp) env f t.
  Proof.
    intros.
    split; intro.
    apply EX_sem_elim in H; auto.
    apply EX_sem_intro; auto.
  Qed.
  
  Lemma ALL_sem: forall `{Sg: Sig} (D: Dom Sg) f,
    forall Itp env t, fm_sem Sg (Itp:=Itp) env (mkAll (getAll f) (ALL f)) t <-> fm_sem Sg (Itp:=Itp) env f t.
  Proof.
    intros.
    match goal with |- ?p1 <-> ?p2 => generalize (@not_iff_compat (not p1) (not p2)); intro end.
    repeat rewrite not_not in H.
    apply H; clear H.
    do 2 rewrite <-Not_sem.
    rewrite Not_mkAll.
    rewrite Not_ALL.
    rewrite <-getEx_Not.
    apply EX_sem.
  Qed.

  Lemma EX_free: forall `{Sg: Sig} (f: formula Sg), forall s, SV.subset (free _ (EX f) s) (vsUnion Sg (free _ f) (getEx f) s).
  Proof.
    induction f; simpl; intros; auto; try apply SV.empty_subset; 
      try apply SV.subset_union_l.
    repeat intro.
    apply IHf in H; clear IHf.
    apply vsUnion_elim in H; destruct H; auto.
    destruct (@dc_dec (isEq2 (U:=variable) s e s0 v)).
    apply vsUnion_r.
    injection d; intros; subst s0.
    apply inj_pair2_eq_dec in d; try apply eq_dec; subst e.
    apply vsAdd_l.
    apply vsUnion_l.
    apply vsInRemove_intro; now auto.
    apply vsUnion_r.
    apply vsAdd_r; now auto.
  Qed.

  Lemma ALL_free: forall `{Sg: Sig} (f: formula Sg), forall s, SV.subset (free _ (ALL f) s) (vsUnion Sg (free _ f) (getAll f) s).
  Proof.
    induction f; simpl; intros; auto; try apply SV.empty_subset; 
      try apply SV.subset_union_l.
    repeat intro.
    apply IHf in H; clear IHf.
    apply vsUnion_elim in H; destruct H; auto.
    destruct (@dc_dec (isEq2 (U:=variable) s e s0 v)).
    apply vsUnion_r.
    injection d; intros; subst s0.
    apply inj_pair2_eq_dec in d; try apply eq_dec; subst e.
    apply vsAdd_l.
    apply vsUnion_l.
    apply vsInRemove_intro; now auto.
    apply vsUnion_r.
    apply vsAdd_r; now auto.
  Qed.

  Lemma close_EXALL: forall `{Sg: Sig} {f: formula Sg},
    (forall s, SV.is_empty (free Sg f s)) ->
    (forall s : Sort,
      SV.subset (free Sg (EX_ALL f) s)
                (SV.union (getEx f s) (getAll (EX f) s))).
  Proof.
    repeat intro.
    unfold EX_ALL in H0.
    apply ALL_free in H0.
    apply vsUnion_elim in H0; destruct H0.
    apply EX_free in H0.
    apply vsUnion_elim in H0; destruct H0.
    apply H in H0; destruct H0.
    apply vsUnion_l; auto.
    apply vsUnion_r; auto.
  Qed.

  Lemma getEx_nfree: forall `{Sg: Sig} (f: formula Sg) s, SV.disjoint (getEx f s) (free Sg f s).
  Proof.
    induction f; simpl; intros; auto;
      try (repeat intro; destruct H; destruct H);
      try (repeat intro; destruct H0; destruct H0).
    repeat intro.
    destruct H.
    apply vsAdd_elim in H; destruct H.
    unfold removeVars in H0.
    apply vsInRemove_elim in H0; destruct H0.
    apply (H1 (sym_eq H)).
    apply vsInRemove_elim in H0.
    destruct H0.
    apply (IHf s0 v (conj H H0)).
  Qed.

  Lemma getAll_nfree: forall `{Sg: Sig} (f: formula Sg) s, SV.disjoint (getAll f s) (free Sg f s).
  Proof.
    induction f; simpl; intros; auto;
      try (repeat intro; destruct H; destruct H);
      try (repeat intro; destruct H0; destruct H0).
    repeat intro.
    destruct H.
    apply vsAdd_elim in H; destruct H.
    unfold removeVars in H0.
    apply vsInRemove_elim in H0; destruct H0.
    apply (H1 (sym_eq H)).
    apply vsInRemove_elim in H0.
    destruct H0.
    apply (IHf s0 v (conj H H0)).
  Qed.

  Definition getExF `{Sg: Sig} (f: formula Sg) := vsInter Sg (getEx f) (free Sg (EX f)).

  Lemma close_EXfALL: forall `{Sg: Sig} {f: formula Sg},
    (forall s, SV.is_empty (free Sg f s)) ->
    (forall s : Sort,
      SV.subset (free Sg (EX_ALL f) s)
                (SV.union (getExF f s) (getAll (EX f) s))).
  Proof.
    repeat intro.
    unfold EX_ALL in H0.
    apply ALL_free in H0.
    apply vsUnion_elim in H0; destruct H0.
    apply vsUnion_l; apply vsInter_intro; auto.
    apply EX_free in H0.
    apply vsUnion_elim in H0; destruct H0; auto.
    apply H in H0; destruct H0.
    
    apply vsUnion_r; auto.
  Qed.


  Lemma mkEx_getExF: forall `{Sg: Sig} (f: formula Sg) (D: Dom Sg) (Itp: Interp D) env t,
    fm_sem Sg env f t <-> fm_sem Sg env (mkEx (getExF f) (EX f)) t.
  Proof.
    intros.
    split; intro; auto.
    apply EX_sem_intro in H; auto.
    apply semEx_elim in H.
    destruct H as [pe H].
    apply semEx_intro.
    exists (fun s v h => pe s v (proj1 (vsInter_elim _ h))).
    revert H; apply fm_sem_equiv; intros.
    unfold pAdd.
    
    destruct (SV.set_In_dec v (getEx f s)).
    destruct (SV.set_In_dec v (getExF f s)); auto.
    rewrite (proof_irrelevance _ _ i); now auto.
    exfalso.
    apply n; clear n; apply vsInter_intro; auto.
    
    destruct (SV.set_In_dec v (getExF f s)); auto.
    exfalso; apply vsInter_elim in i; tauto.

    apply EX_sem_elim.
    apply semEx_elim in H.
    destruct H as [pe H].
    apply semEx_intro.
    exists (fun s v h => 
      match SV.set_In_dec v (free Sg (EX f) s) with
        left h' => pe s v (vsInter_intro _ h h')
      | right _ => env s v
      end).
    revert H; apply fm_sem_equiv; intros.
    unfold pAdd.
    destruct (SV.set_In_dec v (free Sg (EX f) s)); try tauto.
    clear H.
    destruct (SV.set_In_dec v (getEx f s)).
    destruct (SV.set_In_dec v (getExF f s)); auto.
    rewrite (proof_irrelevance _ _ i1); now auto.
    exfalso; apply n; clear n; apply vsInter_intro; tauto.
    destruct (SV.set_In_dec v (getExF f s)); auto.
    exfalso; apply vsInter_elim in i0; tauto.
  Qed.
  
