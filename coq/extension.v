Require Import foltl.
Require Import dec.
Require Import finite.
Require Import Coq.Init.Logic.
Include EqNotations.
Require Import ProofIrrelevance.
Require Import FunctionalExtensionality.
Require Import set.

Definition isInj {T1 T2} (f: T1 -> T2) := forall x1 x2, f x1 = f x2 -> x1 = x2.

Record Extension `(sg1: Sig) `(sg2: Sig) := {
  ext_srt : Sort (Sig := sg1) -> Sort (Sig := sg2);
  ext_srt_inj: isInj ext_srt;
  ext_var : forall s, variable (Sig:=sg1) s -> variable (Sig:=sg2) (ext_srt s);
  ext_var_inj: forall s, isInj (ext_var s);
  ext_cst: forall s, constant (Sig:=sg1) s -> constant (Sig:=sg2) (ext_srt s);
  ext_cst_inj: forall s, isInj (ext_cst s);
  ext_prd: predicate (Sig:=sg1) -> predicate (Sig:=sg2);
  ext_prd_inj: isInj ext_prd;
  ext_ar: forall p, pr_arity (ext_prd p) = pr_arity p;
  ext_art: forall p, Fin.t (pr_arity (ext_prd p)) -> Fin.t (pr_arity p) :=
    fun p i => rew ext_ar p in i;
  ext_ars: forall p i, pr_args (ext_prd p) i = ext_srt (pr_args p (ext_art p i)) 
}.
Arguments ext_srt [_ _ _ _ _ _ _ _ _ _] _.
Arguments ext_srt_inj [_ _ _ _ _ _ _ _ _ _] _.
Arguments ext_var [_ _ _ _ _ _ _ _ _ _] _.
Arguments ext_var_inj [_ _ _ _ _ _ _ _ _ _] _.
Arguments ext_cst [_ _ _ _ _ _ _ _ _ _] _.
Arguments ext_cst_inj [_ _ _ _ _ _ _ _ _ _] _.
Arguments ext_prd [_ _ _ _ _ _ _ _ _ _] _.
Arguments ext_prd_inj [_ _ _ _ _ _ _ _ _ _] _.
Arguments ext_ar [_ _ _ _ _ _ _ _ _ _] _.
Arguments ext_art [_ _ _ _ _ _ _ _ _ _] _.
Arguments ext_ars [_ _ _ _ _ _ _ _ _ _] _.

Definition ext_tm `{sg1: Sig} `{sg2: Sig} (ext: Extension sg1 sg2) (s: Sort (Sig:=sg1)) (tm: term sg1 s): term sg2 (ext_srt ext s) :=
  match tm with
    Cst _ _ c => Cst _ (ext_srt ext s) (ext_cst ext s c)
  | Var _ _ v => Var _ (ext_srt ext s) (ext_var ext s v)
  end.
  
Definition ext_lit `{sg1: Sig} `{sg2: Sig} (ext: Extension sg1 sg2) (lt: literal sg1): literal sg2 :=
  match lt with 
    PApp _ n p a => PApp _ n (ext_prd ext p) (fun i => rew <-(ext_ars ext p i) in ext_tm ext (pr_args p (ext_art ext p i)) (a (ext_art ext p i)))
  end.

Definition ext_atm `{sg1: Sig} `{sg2: Sig} (ext: Extension sg1 sg2) (a: atom sg1): atom sg2 :=
  match a with
    Eq _ s t1 t2 => Eq _ (ext_srt ext s) (ext_tm ext s t1) (ext_tm ext s t2) 
  | NEq _ s t1 t2 => NEq _ (ext_srt ext s) (ext_tm ext s t1) (ext_tm ext s t2) 
  | Literal _ lt => Literal _ (ext_lit ext lt)
  | NLiteral _ lt => NLiteral _ (ext_lit ext lt)
  end.
  
Fixpoint ext_fm `{sg1: Sig} `{sg2: Sig} (ext: Extension sg1 sg2) (f: formula sg1): formula sg2 :=
  match f with
    FTrue _ => FTrue sg2
  | FFalse _ => FFalse sg2
  | Atom _ a => Atom sg2 (ext_atm ext a)
  | And _ f1 f2 => And sg2 (ext_fm ext f1) (ext_fm ext f2)
  | Or _ f1 f2 => Or sg2 (ext_fm ext f1) (ext_fm ext f2)
  | Ex _ s v f => Ex sg2 (ext_srt ext s) (ext_var ext _ v) (ext_fm ext f)
  | All _ s v f => All sg2 (ext_srt ext s) (ext_var ext _ v) (ext_fm ext f)
  | F _ f => F sg2 (ext_fm ext f)
  | G _ f => G sg2 (ext_fm ext f)
  end.

Lemma lookup_set `{F1: Finite} `{F2: Finite} (s: SV.set F1) (f: F1 -> F2) (y: F2) : 
  {x : F1 | SV.set_In x s /\ f x = y} + {forall x, SV.set_In x s -> f x <> y}.
Proof.
  induction s; simpl; intros; auto.
  destruct IHs.
  destruct s0 as [x [h1 h2]].
  left; exists x; split; now auto.
  destruct (eq_dec (f a) y).
  left; exists a; split; now auto.
  right; intros; auto.
  destruct H; auto.
  subst a; auto.
Defined.

Lemma lookup `{F1: Finite} `{F2: Finite} (f: F1 -> F2) (y: F2) : 
  {x : F1 | f x = y} + {forall x, f x <> y}.
Proof.
  destruct (lookup_set (fin_set (Finite:=F1)) f y).
  destruct s as [x [_ h]]; left; exists x; now auto.
  right; intros.
  apply (n x (fin_all x)).
Defined.

Lemma lookup_eq: forall `{F1: Finite} `{F2: Finite} (f: F1->F2) (injF: isInj f) x,
  lookup f (f x) = inleft (exist _ x eq_refl).
Proof.
  intros.
  destruct (lookup f (f x)).
  f_equal.
  destruct s as [u h].
  generalize h; intro h1; apply injF in h; subst u.
  f_equal; apply proof_irrelevance.
  exfalso; apply (n x eq_refl).
Qed.

Definition ext_dom `{sg1: Sig} `{sg2: Sig} (ext: Extension sg1 sg2) (D: Dom sg1): Dom sg2 := {|
  ssemT s2 := match lookup (ext_srt ext) s2 with 
    inleft (exist _ s1 h) => ssemT s1
  | _ => OneDec
  end;
  ssem s2 := match lookup (ext_srt ext) s2 as r return 
    @EqDec (match r with inleft (exist _ s1 h) => ssemT s1
    | _ => One
    end )
  with 
    inleft (exist _ s1 h) => ssem s1
  | _ => OneDec
  end;
  neDom s2 := match lookup (ext_srt ext) s2 as r return 
     (match r with inleft (exist _ s1 h) => ssemT s1
    | _ => One
    end )
  with 
    inleft (exist _ s1 h) => neDom s1
  | _ => one
  end;
|}.

Definition ext_val `{sg1: Sig} `{sg2: Sig} (ext: Extension sg1 sg2) {s1: Sort (Sig:=sg1)} {D: Dom sg1}: ssem s1 -> ssem (Dom:=ext_dom ext D) (ext_srt ext s1) :=
  match lookup (ext_srt ext) (ext_srt ext s1) as s0 return ssem s1 ->
    (match s0 return @EqDec (match s0 with
                                  | inleft (exist _ s _) => ssemT s
                                  | inright _ => One end) 
     with
     | inleft (exist _ s _) => ssem s
     | inright _ => _
     end)
  with
  | inleft (exist _ s h) => fun v => rew <-[ssem] ext_srt_inj ext _ s1 h in v
  | inright n => fun _ => match (n s1 eq_refl) with end
  end.

Definition ext_val_r `{sg1: Sig} `{sg2: Sig} (ext: Extension sg1 sg2) {s1: Sort (Sig:=sg1)} {D: Dom sg1}: ssem (Dom:=ext_dom ext D) (ext_srt ext s1) -> ssem s1 :=
  match lookup (ext_srt ext) (ext_srt ext s1) as s0 return 
    (match s0 return @EqDec (match s0 with
                                  | inleft (exist _ s _) => ssemT s
                                  | inright _ => One end) 
     with
     | inleft (exist _ s _) => ssem s
     | inright _ => _
     end -> ssem s1)
  with
  | inleft (exist _ s h) => fun v => rew [ssem] ext_srt_inj ext _ s1 h in v
  | inright n => fun _ => match (n s1 eq_refl) with end
  end.

Lemma ext_val_r_id `{sg1: Sig} `{sg2: Sig} (ext: Extension sg1 sg2) {s: Sort (Sig:=sg1)} {D: Dom sg1} (v: ssem s):
  ext_val_r ext (ext_val ext v) = v.
Proof.
  unfold ext_val, ext_val_r.
  rewrite lookup_eq; simpl.
  generalize (ext_srt_inj ext s s eq_refl); intro.
  rewrite (proof_irrelevance _ e eq_refl).
  reflexivity.
  apply ext_srt_inj.
Qed.

Lemma ext_val_id `{sg1: Sig} `{sg2: Sig} (ext: Extension sg1 sg2) {s: Sort (Sig:=sg1)} {D: Dom sg1} (v: ssem (ext_srt ext s)):
  ext_val ext (ext_val_r ext v) = v.
Proof.
  unfold ext_val, ext_val_r, ext_dom in *.
  simpl in v; revert v.
  destruct D; simpl in *.
  destruct (lookup (ext_srt ext) (ext_srt ext s)).
  destruct s0 as [s1 h]; intros.
  generalize (ext_srt_inj ext _ _ h); intro; subst s1.
  reflexivity.
  destruct (n _ eq_refl).
Qed.

Definition ext_arg `{sg1: Sig} `{sg2: Sig} (ext: Extension sg1 sg2) {D: Dom sg1} {p1 p2} (hp : ext_prd ext p1 = p2) i :=
  rew [Fin.t] (eq_trans (sym_eq (ext_ar ext p1)) (f_equal pr_arity hp)) in i.

Lemma ext_ind: forall `{sg1: Sig} `{sg2: Sig} (ext: Extension sg1 sg2) {D: Dom sg1} p x,
  (ext_art ext p (ext_arg ext eq_refl x)) = x.
Proof.
  intros.
  unfold ext_art, ext_arg; simpl.
  generalize (ext_ar ext p); intro.
  generalize e; rewrite e; clear e; intro e.
  rewrite (proof_irrelevance _ e eq_refl).
  reflexivity.
Qed.

Definition ext_arg_r `{sg1: Sig} `{sg2: Sig} (ext: Extension sg1 sg2) {D: Dom sg1} {p1 p2} (hp : ext_prd ext p1 = p2) i:
  ssem (pr_args p2 (ext_arg ext hp i)) -> ssem (pr_args p1 i) := 
    match hp as e in _=p return ssem (pr_args p (ext_arg ext e i)) -> ssem (pr_args p1 i) with
    eq_refl => 
      let i1 := ext_arg ext eq_refl i in
      fun v => 
        let v1 := rew [ssem] ext_ars ext p1 i1 in v in
        let v2 := ext_val_r ext v1 in
        rew [fun i => ssem (pr_args p1 i)] (ext_ind ext p1 i) in v2
    end .

Definition ext_itp `{sg1: Sig} `{sg2: Sig} (ext: Extension sg1 sg2) {D: Dom sg1} (itp: Interp D): Interp (ext_dom ext D) := {|
  csem s2 c2 := 
    match lookup (ext_srt ext) s2 return ssem s2 with
      inleft (exist _ s1 hs) =>
        match lookup (ext_cst ext s1) (rew <-[constant] hs in c2) return ssem s2 with
          inleft (exist _ c1 hc) => rew [ssem] hs in ext_val ext (csem c1)
        | _ => neDom s2
        end
    | _ => neDom s2
    end;
  psem p2 t :=
    match lookup (ext_prd ext) p2 return (forall i, ssem (pr_args p2 i)) -> Prop with
      inleft (exist _ p1 hp) => fun a => 
        psem p1 t (fun i => ext_arg_r ext hp i (a (ext_arg ext hp i)))
    | _ => fun a => False
    end
|}.

Definition ext_env `{sg1: Sig} `{sg2: Sig} (ext: Extension sg1 sg2) {D: Dom sg1} (env: Env sg1 D): Env sg2 (ext_dom ext D) :=
  fun s2 => 
    match lookup (ext_srt ext) s2 with
      inleft (exist _ s1 hs) => fun v2 =>
        match lookup (ext_var ext s1) (rew <-[variable] hs in v2) with
          inleft (exist _ v1 hv) => rew [ssem] hs in ext_val ext (env s1 v1)
        | _ => neDom s2
        end
    | _ => fun v2 => neDom s2
    end.

Ltac psemTac :=
    match goal with
      H:psem _ _ ?sa |- psem _ _ ?sa' => assert (sa' = sa) as ae;
          try (rewrite ae; assumption); (apply functional_extensionality_dep; intros)
    end.

Lemma ext_sat_env: forall `{sg1: Sig} `{sg2: Sig} (ext: Extension sg1 sg2) (D: Dom sg1) env s v,
  ext_val_r ext (ext_env ext env (ext_srt ext s) (ext_var ext s v)) = env s v.
Proof.
  intros.
  unfold ext_env.
  rewrite lookup_eq; simpl.
  unfold eq_rect_r; simpl.
  rewrite lookup_eq; simpl.
  apply ext_val_r_id.
  apply ext_var_inj.
  apply ext_srt_inj.
Qed.

Lemma ext_sat_cst: forall `{sg1: Sig} `{sg2: Sig} (ext: Extension sg1 sg2) (D: Dom sg1) (itp: Interp D) s c,
  csem (Interp:=ext_itp ext itp) (ext_cst ext s c) = ext_val ext (csem c).
Proof.
  intros.
  unfold csem at 1.
  unfold ext_itp.
  destruct (lookup (ext_srt ext) (ext_srt ext s)).
  destruct s0 as [s1 h].
  generalize h; intro h0.
  apply ext_srt_inj in h; subst s1.
  rewrite (proof_irrelevance _ h0 eq_refl); clear h0.
  change (rew <- [fun s0 : Sort => constant s0] eq_refl in ext_cst ext s c) with (ext_cst ext s c).
  rewrite lookup_eq.
  reflexivity.
  apply ext_cst_inj.
  exfalso; apply (n _ eq_refl).
Qed.

Lemma ext_sat_tm_r:  forall `{sg1: Sig} `{sg2: Sig} (ext: Extension sg1 sg2) (D: Dom sg1) (itp: Interp D) (env: Env sg1 D) s tm,
  ext_val_r ext
    (tm_sem sg2 (Itp:=ext_itp ext itp) (ext_env ext env) (ext_tm ext s tm)) =
      tm_sem sg1 env tm.
Proof.
  intros.
  destruct tm; intros; auto.
  - simpl.
    apply ext_sat_env.
  - unfold tm_sem at 1.
    unfold ext_itp, ext_tm.
    generalize (ext_sat_cst ext D itp s e); intro.
    unfold tm_sem.
    apply (f_equal (ext_val_r ext)) in H.
    rewrite ext_val_r_id in H.
    rewrite <-H; clear H.
    reflexivity.
Qed.

Lemma ext_sat_tm: forall `{sg1: Sig} `{sg2: Sig} (ext: Extension sg1 sg2) (D: Dom sg1) (itp: Interp D) (env: Env sg1 D) s tm,
  tm_sem sg2 (Itp:=ext_itp ext itp) (ext_env ext env) (ext_tm ext s tm) = ext_val ext (tm_sem sg1 env tm).
Proof.
  intros.
  generalize (ext_sat_tm_r ext D itp env s tm); intro.
  apply (f_equal (ext_val ext)) in H.
  rewrite ext_val_id in H.
  apply H.
Qed.

Lemma ext_sat_lt: forall `{sg1: Sig} `{sg2: Sig} (ext: Extension sg1 sg2) (D: Dom sg1) (itp: Interp D) (env: Env sg1 D) l t,
  lt_sem sg1 env l t <-> lt_sem (Itp:=ext_itp ext itp) sg2 (ext_env ext env) (ext_lit ext l) t.
Proof.
  intros.
  destruct l.
  simpl.
  destruct (lookup (ext_prd ext) (ext_prd ext p)).
  destruct s as [x h].
  generalize (ext_prd_inj ext _ _ h); intro.
  subst x.
  rewrite (proof_irrelevance _ h eq_refl); clear h.
  split; intro H; psemTac; clear H.
  
  generalize (ext_ars ext p (ext_arg ext eq_refl x)).
  rewrite (ext_ind ext p x); intro.
  unfold ext_arg_r.
  generalize (ext_ars ext p (ext_arg ext eq_refl x)).
  generalize e; rewrite e; clear e; intro e.
  rewrite (proof_irrelevance _ e eq_refl); clear e.
  change (rew <- [term sg2] eq_refl in ext_tm ext (pr_args p x) (t0 x)) 
    with (ext_tm ext (pr_args p x) (t0 x)).
  generalize (ext_ind ext p x).
  rewrite (ext_ind ext p x); intros.
  rewrite (proof_irrelevance _ e eq_refl); clear e.
  rewrite (proof_irrelevance _ e0 eq_refl); clear e0.
  simpl.
  rewrite ext_sat_tm_r.
  reflexivity.

  generalize (ext_ars ext p (ext_arg ext eq_refl x)).
  rewrite (ext_ind ext p x); intro.
  unfold ext_arg_r.
  generalize (ext_ars ext p (ext_arg ext eq_refl x)).
  generalize e; rewrite e; clear e; intro e.
  rewrite (proof_irrelevance _ e eq_refl); clear e.
  change (rew <- [term sg2] eq_refl in ext_tm ext (pr_args p x) (t0 x)) 
    with (ext_tm ext (pr_args p x) (t0 x)).
  generalize (ext_ind ext p x).
  rewrite (ext_ind ext p x); intros.
  rewrite (proof_irrelevance _ e eq_refl); clear e.
  rewrite (proof_irrelevance _ e0 eq_refl); clear e0.
  simpl.
  rewrite ext_sat_tm_r.
  reflexivity.

  exfalso; apply (n0 _ eq_refl).
Qed.

Lemma ext_sat_at: forall `{sg1: Sig} `{sg2: Sig} (ext: Extension sg1 sg2) (D: Dom sg1) (itp: Interp D) (env: Env sg1 D) a t,
  at_sem sg1 env a t -> at_sem (Itp:=ext_itp ext itp) sg2 (ext_env ext env) (ext_atm ext a) t.
Proof.
  intros.
  destruct a; simpl in H|-*.
  - revert H; apply ext_sat_lt.
  - intro; apply H; clear H.
    revert H0; apply ext_sat_lt.
  - do 2 rewrite ext_sat_tm.
    rewrite H.
    reflexivity.
  - intro; apply H; clear H.
    do 2 rewrite ext_sat_tm in H0.
    generalize (f_equal (ext_val_r ext) H0); clear H0; intro.
    do 2 rewrite ext_val_r_id in H.
    apply H.
Qed.

Lemma ext_env_out `{sg1: Sig} `{sg2: Sig} (ext: Extension sg1 sg2) (D: Dom sg1) env s w:
  (forall x, ext_var ext s x <> w) -> ext_env ext env (ext_srt ext s) w = neDom _.
Proof.
  intro ne.
  unfold ext_env, ext_itp, ext_dom, ext_val in *.
  destruct (lookup (ext_srt ext) (ext_srt ext s)); auto.
  destruct s0 as [s' h].
  generalize (ext_srt_inj ext _ _ h); intro; subst s'.
  rewrite (proof_irrelevance _ h eq_refl); clear h; simpl.
  unfold eq_rect_r; simpl.
  destruct (lookup (ext_var ext s) w).
  destruct s0.
  apply ne in e; destruct e.
  rewrite lookup_eq; auto.
  apply ext_srt_inj.
Qed.

Lemma ext_env_nos `{sg1: Sig} `{sg2: Sig} (ext: Extension sg1 sg2) (D: Dom sg1) env s w:
  (forall x, ext_srt ext x <> s) -> ext_env ext env s w = neDom _.
Proof.
  intro ne.
  unfold ext_env, ext_itp, ext_dom, ext_val in *.
  destruct (lookup (ext_srt ext) s); auto.
  destruct s0 as [s' h]; subst s.
  exfalso; destruct (ne _ eq_refl).
Qed.

Lemma ext_env_add `{sg1: Sig} `{sg2: Sig} (ext: Extension sg1 sg2) (D: Dom sg1) env s v d:
  (add sg2 (ext_var ext s v) (ext_val ext d) (ext_env ext env)) =  (ext_env ext (add sg1 v d env)).
Proof.
  apply functional_extensionality_dep; intro s'.
  apply functional_extensionality_dep; intro w.
  destruct (eq_dec (ext_srt ext s) s').
  subst s'; simpl.
  destruct (eq_dec (ext_var ext s v) w).
  subst w.
  rewrite add_eq.
  generalize (f_equal (ext_val ext) (ext_sat_env ext D (add sg1 v d env) s v)); intro.
  rewrite ext_val_id in H.
  rewrite H.
  rewrite add_eq.
  reflexivity.

  rewrite add_ne; auto.
  destruct (eq_dec (env s v) d).
  rewrite <-e, add_id; now auto.
  generalize (fun u => add_ne sg1 D env s v u d).
  generalize (add_eq sg1 D env s v d).
  generalize (add sg1 v d env); intros env' H1 H2.
  rewrite <-H1 in n0; clear H1 d.
  
  destruct (lookup (ext_var ext s) w).
  destruct s0 as [x h].
  subst w.
  generalize (f_equal (ext_val ext) (ext_sat_env ext D env s x)); intro.
  rewrite ext_val_id in H.
  rewrite H; clear H.
  generalize (f_equal (ext_val ext) (ext_sat_env ext D env' s x)); intro.
  rewrite ext_val_id in H.
  rewrite H; clear H.
  rewrite H2; auto.
  intro; apply n; subst x; now auto.
  
  rewrite (ext_env_out ext D env _ _ n1).
  rewrite (ext_env_out ext D env' _ _ n1).
  reflexivity.

  rewrite add_ne2; auto.
  destruct (lookup (ext_srt ext) s'); auto.
  destruct s0 as [s1 h].
  subst s'.
  unfold ext_env, add.
  destruct (lookup (ext_srt ext) (ext_srt ext s1)); auto.
  destruct s0 as [s2 h].
  generalize (ext_srt_inj ext _ _ h); intro; subst s2.
  rewrite (proof_irrelevance _ h eq_refl); clear h; simpl.
  unfold eq_rect_r; simpl.
  destruct (lookup (ext_var ext s1) w); auto.
  destruct s0 as [y h].
  subst w.
  destruct (eq_dec s s1); auto.
  subst s1; try (exfalso; tauto); now auto.
  rewrite (ext_env_nos ext D env _ _ n0).
  rewrite (ext_env_nos ext D _ _ _ n0).
  now auto.
  
  intro.
  inversion H.
  injection H; clear H; intros; subst.
  apply (n H0).
Qed.

Lemma ext_sat `{sg1: Sig} `{sg2: Sig} (ext: Extension sg1 sg2):
  forall f, isSat _ f -> isSat _ (ext_fm ext f).
Proof.
  intros.
  destruct H as [D [itp [env [t H]]]].

  exists (ext_dom ext D).
  exists (ext_itp ext itp).
  exists (ext_env ext env).
  exists t.
  
  revert t env H; induction f; intros; try (apply H).
  - simpl in H |- *.
    revert H; apply ext_sat_at.
  - apply And_sem in H; destruct H.
    apply IHf1 in H; apply IHf2 in H0; clear IHf1 IHf2.
    apply And_sem; now auto.
  - apply Or_sem in H; destruct H; [left | right]; auto.
  - apply (proj1 (Ex_sem _ _ _ _ _ _ f t)) in H.
    destruct H as [d H].
    apply IHf in H; clear IHf.
    apply Ex_sem.
    exists (ext_val ext d).
    rewrite ext_env_add.
    apply H.
  - apply All_sem; intro.
    fold (ext_fm ext).
    generalize (proj1 (All_sem _ _ _ _ _ _ f t) H (ext_val_r ext d)); clear H; intro.
    apply IHf in H; clear IHf.
    generalize (ext_val_id ext d); intro.
    revert H H0; generalize (ext_val_r ext d) as d'; intros; subst d.
    rewrite (ext_env_add ext).
    apply H.
  - apply (proj1 (F_sem _ _ f t)) in H.
    destruct H as [t' [h1 h2]].
    apply F_sem.
    fold (ext_fm ext).
    exists t'; split; auto.
  - apply G_sem.
    fold (ext_fm ext); intros.
    apply (proj1 (G_sem _ _ f t) ) with (t'0:=t') in H; auto.
Qed.
