Add LoadPath "$HOME/COQ/FO-LTL" as Top.

Require Import Top.foltl.
Require Import Top.set.
Require Import Top.dec.
Require Import Top.finite.

Require Import List.
Include ListNotations.
Require Import Recdef.

(*
https://www.ibisc.univ-evry.fr/~belardinelli/Documents/Verification/lec12.pdf
*)

Definition lt_sub `{Sg: Sig} (l: literal Sg): SV.set (ltDec Sg) :=
  match l with
    PApp _ n p args => List.map (fun i => PApp Sg i p args) (seq 0 n)
  end.

Definition at_sub `{Sg: Sig} (a: atom Sg): SV.set (atDec Sg) :=
  match a with
    Literal _ lt | NLiteral _ lt=>
      SV.union
        (SV.image (T1:=ltDec Sg) (T2:=atDec Sg) (Literal Sg) (lt_sub lt))
        (SV.image (T1:=ltDec Sg) (T2:=atDec Sg) (NLiteral Sg) (lt_sub lt))
  | Eq _ s tm1 tm2 | NEq _ s tm1 tm2 => SV.pair (T:=atDec Sg) (Eq Sg s tm1 tm2) (NEq Sg s tm1 tm2)
  end.

Fixpoint subForm `{Sg: Sig} (f: formula Sg): SV.set (fmDec Sg) :=
  match f with
  | FTrue _ | FFalse _ => SV.pair (T:=fmDec Sg) (FTrue Sg) (FFalse Sg)
  | Atom _ a => SV.union (T:=fmDec Sg) (SV.pair (T:=fmDec Sg) (FTrue Sg) (FFalse Sg)) (SV.image (T1:=atDec Sg) (T2:=fmDec Sg) (Atom Sg) (at_sub a))
  | And _ f1 f2 | Or _ f1 f2 => 
    SV.add (T:=fmDec Sg) (And Sg f1 f2) 
      (SV.add (T:=fmDec Sg) (Or Sg f1 f2) (SV.union (T:=fmDec Sg) (subForm f1) (subForm f2))) 
  | Ex _ s v f' | All _ s v f' => 
    SV.add (T:=fmDec Sg) (Ex Sg s v f') (SV.add (T:=fmDec Sg) (All Sg s v f') (subForm f'))
  | F _ f' | G _ f' => 
    SV.add (T:=fmDec Sg) (F Sg f') (SV.add (T:=fmDec Sg) (G Sg f') (subForm f'))
  end.

Lemma subTrue: forall `(Sg: Sig) (f: formula Sg), SV.set_In (T:=fmDec Sg) (FTrue Sg) (subForm f).
Proof.
  induction f; simpl; intros; auto.
  - apply SV.InPair; left; auto.
  - apply SV.InPair; left; auto.
  - apply SV.InUnion_l; apply SV.InPair; left; auto.
  - apply SV.InAdd_r; apply SV.InAdd_r; apply SV.InUnion_l; auto.
  - apply SV.InAdd_r; apply SV.InAdd_r; apply SV.InUnion_l; auto.
  - apply SV.InAdd_r; apply SV.InAdd_r; auto.
  - apply SV.InAdd_r; apply SV.InAdd_r; auto.
  - apply SV.InAdd_r; apply SV.InAdd_r; auto.
  - apply SV.InAdd_r; apply SV.InAdd_r; auto.
Qed.

Lemma subFalse: forall `(Sg: Sig) (f: formula Sg), SV.set_In (T:=fmDec Sg) (FFalse Sg) (subForm f).
Proof.
  induction f; simpl; intros; auto.
  - apply SV.InPair; right; auto.
  - apply SV.InPair; right; auto.
  - apply SV.InUnion_l; apply SV.InPair; right; auto.
  - apply SV.InAdd_r; apply SV.InAdd_r; apply SV.InUnion_l; auto.
  - apply SV.InAdd_r; apply SV.InAdd_r; apply SV.InUnion_l; auto.
  - apply SV.InAdd_r; apply SV.InAdd_r; auto.
  - apply SV.InAdd_r; apply SV.InAdd_r; auto.
  - apply SV.InAdd_r; apply SV.InAdd_r; auto.
  - apply SV.InAdd_r; apply SV.InAdd_r; auto.
Qed.

Record Stable `{Sg: Sig} (sf: SV.set (fmDec Sg)) := {
  stb_And: forall f1 f2, SV.set_In (T:=fmDec Sg) (And Sg f1 f2) sf -> SV.set_In (T:=fmDec Sg) f1 sf /\ SV.set_In (T:=fmDec Sg) f2 sf;
  stb_Or: forall f1 f2, SV.set_In (T:=fmDec Sg) (Or Sg f1 f2) sf -> SV.set_In (T:=fmDec Sg) f1 sf \/ SV.set_In (T:=fmDec Sg) f2 sf;
  stb_Or1: forall f1 f2, SV.set_In (T:=fmDec Sg) (Or Sg f1 f2) sf -> SV.set_In (T:=fmDec Sg) f1 sf \/ SV.set_In (T:=fmDec Sg) (Not Sg f1) sf;
  stb_Or2: forall f1 f2, SV.set_In (T:=fmDec Sg) (Or Sg f1 f2) sf -> SV.set_In (T:=fmDec Sg) f2 sf \/ SV.set_In (T:=fmDec Sg) (Not Sg f2) sf;
  stb_F: forall f, SV.set_In (T:=fmDec Sg) (F Sg f) sf -> (SV.set_In (T:=fmDec Sg) f sf \/ SV.set_In (T:=fmDec Sg) (Not Sg f) sf);
  stb_G: forall f, SV.set_In (T:=fmDec Sg) (G Sg f) sf -> SV.set_In (T:=fmDec Sg) f sf;
  stb_N: forall f, not (SV.set_In (T:=fmDec Sg) f sf /\ SV.set_In (T:=fmDec Sg) (Not Sg f) sf);
}.

Lemma stbAnd_dec `{Sg: Sig} (sf: SV.set (fmDec Sg)): 
  {forall f1 f2, SV.set_In (T:=fmDec Sg) (And Sg f1 f2) sf -> SV.set_In (T:=fmDec Sg) f1 sf /\ SV.set_In (T:=fmDec Sg) f2 sf}
  +
  {not (forall f1 f2, SV.set_In (T:=fmDec Sg) (And Sg f1 f2) sf -> SV.set_In (T:=fmDec Sg) f1 sf /\ SV.set_In (T:=fmDec Sg) f2 sf)}.
Proof.
  intros.
  destruct (@dc_dec (all1_dec (fun (f: asFinite sf) =>
    match proj1_sig f with
      And _ f1 f2 => AndDec (SV.InPred _ sf f1) (SV.InPred _ sf f2)
    | _ => TrueDec
    end))); [left | right]; intros.
  simpl in d.
  specialize d with (exist (fun x => SV.set_In x sf) (And Sg f1 f2) H); simpl in d; tauto.
  intro; apply n; clear n; simpl; intros.
  destruct x as [f h]; simpl.
  destruct f; simpl in *; auto.
  apply H in h; auto.
Qed.

Lemma stbOr_dec `{Sg: Sig} (sf: SV.set (fmDec Sg)): 
  {forall f1 f2, SV.set_In (T:=fmDec Sg) (Or Sg f1 f2) sf -> SV.set_In (T:=fmDec Sg) f1 sf \/ SV.set_In (T:=fmDec Sg) f2 sf}
  +
  {not (forall f1 f2, SV.set_In (T:=fmDec Sg) (Or Sg f1 f2) sf -> SV.set_In (T:=fmDec Sg) f1 sf \/ SV.set_In (T:=fmDec Sg) f2 sf)}.
Proof.
  intros.
  destruct (@dc_dec (all1_dec (fun (f: asFinite sf) =>
    match proj1_sig f with
      Or _ f1 f2 => OrDec (SV.InPred _ sf f1) (SV.InPred _ sf f2)
    | _ => TrueDec
    end))); [left | right]; intros.
  simpl in d.
  specialize d with (exist (fun x => SV.set_In x sf) (Or Sg f1 f2) H); simpl in d; tauto.
  intro; apply n; clear n; simpl; intros.
  destruct x as [f h]; simpl.
  destruct f; simpl in *; auto.
  apply H in h; auto.
Qed.

Lemma stbOr1_dec `{Sg: Sig} (sf: SV.set (fmDec Sg)): 
  {forall f1 f2, SV.set_In (T:=fmDec Sg) (Or Sg f1 f2) sf -> SV.set_In (T:=fmDec Sg) f1 sf \/ SV.set_In (T:=fmDec Sg) (Not Sg f1) sf}
  +
  {not (forall f1 f2, SV.set_In (T:=fmDec Sg) (Or Sg f1 f2) sf -> SV.set_In (T:=fmDec Sg) f1 sf \/ SV.set_In (T:=fmDec Sg) (Not Sg f1) sf)}.
Proof.
  intros.
  destruct (@dc_dec (all1_dec (fun (f: asFinite sf) =>
    match proj1_sig f with
      Or _ f1 f2 => OrDec (SV.InPred _ sf f1) (SV.InPred _ sf (Not Sg f1))
    | _ => TrueDec
    end))); [left | right]; intros.
  simpl in d.
  specialize d with (exist (fun x => SV.set_In x sf) (Or Sg f1 f2) H); simpl in d; tauto.
  intro; apply n; clear n; simpl; intros.
  destruct x as [f h]; simpl.
  destruct f; simpl in *; auto.
  apply H in h; auto.
Qed.

Lemma stbOr2_dec `{Sg: Sig} (sf: SV.set (fmDec Sg)): 
  {forall f1 f2, SV.set_In (T:=fmDec Sg) (Or Sg f1 f2) sf -> SV.set_In (T:=fmDec Sg) f2 sf \/ SV.set_In (T:=fmDec Sg) (Not Sg f2) sf}
  +
  {not (forall f1 f2, SV.set_In (T:=fmDec Sg) (Or Sg f1 f2) sf -> SV.set_In (T:=fmDec Sg) f2 sf \/ SV.set_In (T:=fmDec Sg) (Not Sg f2) sf)}.
Proof.
  intros.
  destruct (@dc_dec (all1_dec (fun (f: asFinite sf) =>
    match proj1_sig f with
      Or _ f1 f2 => OrDec (SV.InPred _ sf f2) (SV.InPred _ sf (Not Sg f2))
    | _ => TrueDec
    end))); [left | right]; intros.
  simpl in d.
  specialize d with (exist (fun x => SV.set_In x sf) (Or Sg f1 f2) H); simpl in d; tauto.
  intro; apply n; clear n; simpl; intros.
  destruct x as [f h]; simpl.
  destruct f; simpl in *; auto.
  apply H in h; auto.
Qed.

Lemma stbF_dec `{Sg: Sig} (sf: SV.set (fmDec Sg)): 
  {forall f1, SV.set_In (T:=fmDec Sg) (F Sg f1) sf -> SV.set_In (T:=fmDec Sg) f1 sf \/ SV.set_In (T:=fmDec Sg) (Not Sg f1) sf}
  +
  {not (forall f1, SV.set_In (T:=fmDec Sg) (F Sg f1) sf -> SV.set_In (T:=fmDec Sg) f1 sf \/ SV.set_In (T:=fmDec Sg) (Not Sg f1) sf)}.
Proof.
  intros.
  destruct (@dc_dec (all1_dec (fun (f: asFinite sf) =>
    match proj1_sig f with
      F _ f1 => OrDec (SV.InPred _ sf f1) (SV.InPred _ sf (Not Sg f1))
    | _ => TrueDec
    end))); [left | right]; intros.
  simpl in d.
  specialize d with (exist (fun x => SV.set_In x sf) (F Sg f1) H); simpl in d; tauto.
  intro; apply n; clear n; simpl; intros.
  destruct x as [f h]; simpl.
  destruct f; simpl in *; auto.
  apply H in h; auto.
Qed.

Lemma stbG_dec `{Sg: Sig} (sf: SV.set (fmDec Sg)): 
  {forall f1, SV.set_In (T:=fmDec Sg) (G Sg f1) sf -> SV.set_In (T:=fmDec Sg) f1 sf}
  +
  {not (forall f1, SV.set_In (T:=fmDec Sg) (G Sg f1) sf -> SV.set_In (T:=fmDec Sg) f1 sf)}.
Proof.
  intros.
  destruct (@dc_dec (all1_dec (fun (f: asFinite sf) =>
    match proj1_sig f with
      G _ f1 => SV.InPred _ sf f1
    | _ => TrueDec
    end))); [left | right]; intros.
  simpl in d.
  specialize d with (exist (fun x => SV.set_In x sf) (G Sg f1) H); simpl in d; tauto.
  intro; apply n; clear n; simpl; intros.
  destruct x as [f h]; simpl.
  destruct f; simpl in *; auto.
  apply H in h; auto.
Qed.

Lemma stbN_dec `{Sg: Sig} (sf: SV.set (fmDec Sg)): 
  {forall f, not (SV.set_In (T:=fmDec Sg) f sf  /\ SV.set_In (T:=fmDec Sg) (Not Sg f) sf)}
  +
  {not (forall f, not (SV.set_In (T:=fmDec Sg) f sf  /\ SV.set_In (T:=fmDec Sg) (Not Sg f) sf))}.
Proof.
  intros.
  destruct (@dc_dec (all1_dec (fun (f: asFinite sf) =>
    NotDec (SV.InPred _ sf (Not Sg (proj1_sig f)))))); [left | right]; intros.
  simpl in d.
  intro.
  destruct H.
  specialize d with (exist (fun x => SV.set_In x sf) f H); simpl in d; tauto.
  intro; apply n; clear n; simpl; intros.
  destruct x as [f h]; simpl.
  intro.
  apply (H f); tauto.
Qed.

Lemma Stable_dec `{Sg: Sig} (sf: SV.set (fmDec Sg)): Decidable.
Proof.
  exists (Stable sf).
  destruct (stbAnd_dec sf); [idtac | right; repeat intro; destruct H; tauto].
  destruct (stbOr_dec sf); [idtac | right; repeat intro; destruct H; tauto].
  destruct (stbOr1_dec sf); [idtac | right; repeat intro; destruct H; tauto].
  destruct (stbOr2_dec sf); [idtac | right; repeat intro; destruct H; tauto].
  destruct (stbF_dec sf); [idtac | right; repeat intro; destruct H; tauto].
  destruct (stbG_dec sf); [idtac | right; repeat intro; destruct H; tauto].
  destruct (stbN_dec sf); [idtac | right; repeat intro; destruct H; tauto].
  left; split; auto.
Defined.

Section SAT.
  Context {Ts: Type} {Tv: Ts->Type} {Tc: Ts->Type} {Tp: Type} {Ta: Tp -> Type}.
  Variable Sg: @Sig Ts Tv Tc Tp Ta.
  Variable phi: formula Sg.
  Definition SF := subForm phi.
  
  Definition State := asFinite (SV.Filter (T:=SV.setDec (fmDec Sg)) Stable_dec (SV.pow SF)).
  
  Definition Init (st: State) := SV.set_In (T:= fmDec Sg) phi (proj1_sig st).

  Record Next (sf1 sf2: State) := {
    nxt_X: forall f, SV.set_In (T:=fmDec Sg) (X Sg f) SF ->  
      SV.set_In (T:=fmDec Sg) (X Sg f) (proj1_sig sf1) <-> SV.set_In (T:=fmDec Sg) f (proj1_sig sf2);
    nxf_F: forall f, SV.set_In (T:=fmDec Sg) (F Sg f) SF ->
      SV.set_In (T:=fmDec Sg) (F Sg f) (proj1_sig sf1) <-> (SV.set_In (T:=fmDec Sg) f (proj1_sig sf1) \/ SV.set_In (T:=fmDec Sg) (F Sg f) (proj1_sig sf2));
    nxt_G: forall f, SV.set_In (T:=fmDec Sg) (G Sg f) SF ->
      SV.set_In (T:=fmDec Sg) (G Sg f) (proj1_sig sf1) -> SV.set_In (T:=fmDec Sg) (G Sg f) (proj1_sig sf2);
  }.
  
  Lemma nxt_X_dec: forall (sf1 sf2: State),
    (forall f, SV.set_In (T:=fmDec Sg) (X Sg f) SF ->  
      SV.set_In (T:=fmDec Sg) (X Sg f) (proj1_sig sf1) <-> SV.set_In (T:=fmDec Sg) f (proj1_sig sf2)) 
  +
    (not (forall f, SV.set_In (T:=fmDec Sg) (X Sg f) SF ->  
      SV.set_In (T:=fmDec Sg) (X Sg f) (proj1_sig sf1) <-> SV.set_In (T:=fmDec Sg) f (proj1_sig sf2))).
  Proof.
    intros.
    destruct (all_dec (F:=asFinite SF) (fun f =>
      match isX_dec Sg (proj1_sig f) with
        inl (exist _ g h) => IffDec (SV.InPred _ (proj1_sig sf1) (proj1_sig f)) (SV.InPred _ (proj1_sig sf2) g)
      | inr k => TrueDec
      end)); [left | right]; repeat intro.
    generalize (d (exist _ (X Sg f) H)); clear d; simpl; intro.
    destruct (isX_dec Sg (X Sg f)); simpl in *.
    destruct s as [g h]; simpl in *.
    apply X_inj in h; subst g; now auto.
    destruct (n f); now auto.
    
    destruct s as [k h].
    destruct (isX_dec Sg (proj1_sig k)).
    destruct s as [g h']; subst.
    destruct k as [g' k]; simpl in *; subst.
    apply h; clear h; apply H; clear H; now auto.
    apply h; simpl; now auto.
  Qed.

  Lemma nxt_F_dec: forall (sf1 sf2: State),
    (forall f, SV.set_In (T:=fmDec Sg) (F Sg f) SF ->  
      SV.set_In (T:=fmDec Sg) (F Sg f) (proj1_sig sf1) <-> (SV.set_In (T:=fmDec Sg) f (proj1_sig sf1) \/ SV.set_In (T:=fmDec Sg) (F Sg f) (proj1_sig sf2)))
  +
    (not (forall f, SV.set_In (T:=fmDec Sg) (F Sg f) SF ->  
      SV.set_In (T:=fmDec Sg) (F Sg f) (proj1_sig sf1) <-> (SV.set_In (T:=fmDec Sg) f (proj1_sig sf1) \/ SV.set_In (T:=fmDec Sg) (F Sg f) (proj1_sig sf2)))).
  Proof.
    intros.
    destruct (all_dec (F:=asFinite SF) (fun f =>
      match (proj1_sig f) with
        F _ g => IffDec (SV.InPred _ (proj1_sig sf1) (proj1_sig f)) 
                        (OrDec (SV.InPred _ (proj1_sig sf1) g)
                                 (SV.InPred _ (proj1_sig sf2) (proj1_sig f)))
      | _ => TrueDec
      end)); [left | right]; repeat intro.
    generalize (d (exist _ (F Sg f) H)); clear d; simpl; intro.
    apply H0.
    
    destruct s as [k h].
    apply h; clear h.
    generalize (proj2_sig k).
    destruct (proj1_sig k); simpl; auto.
    apply H; auto.
  Qed.

  Lemma nxt_G_dec: forall (sf1 sf2: State),
    (forall f, SV.set_In (T:=fmDec Sg) (G Sg f) SF ->  
      SV.set_In (T:=fmDec Sg) (G Sg f) (proj1_sig sf1) -> SV.set_In (T:=fmDec Sg) (G Sg f) (proj1_sig sf2))
  +
    (not (forall f, SV.set_In (T:=fmDec Sg) (G Sg f) SF ->  
      SV.set_In (T:=fmDec Sg) (G Sg f) (proj1_sig sf1) -> SV.set_In (T:=fmDec Sg) (G Sg f) (proj1_sig sf2))).
  Proof.
    intros.
    destruct (all_dec (F:=asFinite SF) (fun f =>
      match (proj1_sig f) with
        G _ g => ImpDec (SV.InPred _ (proj1_sig sf1) (proj1_sig f))
                           (SV.InPred _ (proj1_sig sf2) (proj1_sig f))
      | _ => TrueDec
      end)); [left | right]; repeat intro.
    generalize (d (exist _ (G Sg f) H)); clear d; simpl; intro.
    apply H1; now auto.
    
    destruct s as [k h].
    apply h; clear h.
    generalize (proj2_sig k).
    destruct (proj1_sig k); simpl; auto.
    apply H; auto.
  Qed.
  
  Lemma Next_dec: forall sf1 sf2, {Next sf1 sf2} + {not (Next sf1 sf2)}.
  Proof.
    intros.
    destruct (nxt_X_dec sf1 sf2); [idtac | right; repeat intro; destruct H; tauto].
    destruct (nxt_F_dec sf1 sf2); [idtac | right; repeat intro; destruct H; tauto].
    destruct (nxt_G_dec sf1 sf2); [idtac | right; repeat intro; destruct H; tauto].
    left; split; auto.
  Qed.

  Definition NextDec sf1 sf2 : Decidable := {| dc_dec := Next_dec sf1 sf2 |}.

  Definition getF (st: State): SV.set (fmDec Sg) :=
    SV.Filter (T:=fmDec Sg) (fun f => SV.InPred (fmDec Sg) (proj1_sig st) (F Sg f)) (proj1_sig st).


  Definition st_sat (D: Dom Sg) (st: State) := 
    exists (Itp: Interp (Sg:=Sg) D), exists env, exists t,
      forall f, SV.set_In f (proj1_sig st) -> fm_sem Sg env f t.
  
  Function st_satisfiable (D: Dom Sg) (seen: SV.set State) (hs: forall st, SV.set_In (T:=State) st seen -> SV.subset (T:=(fmDec Sg)) (proj1_sig st) SF) (F_req: SV.set (fmDec Sg)) (st: State) {measure (fun s => SV.card Sg (SV.diff SF s)) seen }: {st_sat D st} + {not (st_sat D st)} :=
    if SV.In_dec (T:=State) st seen then
      if SV.subset_dec F_req (proj1_sig st) then left _ else right _
    else
      if ex_dec (F := State) (fun st' =>
          AndDec (NextDec st st')
                 {| dc_dec := st_satisfiable D (SV.add st seen) 
                    _
                    (SV.diff (SV.union F_req (getF st)) (proj1_sig st))
                    st' |} )
      then left _ else right _.

  Definition Rec (f: formula Sg) (st: State): Decidable :=
    ImpDec (SV.InPred _ (proj1_sig st) (F _ f)) (SV.InPred _ (proj1_sig st) f).

  Record satisfiable f: Type := {
    st_exec: nat -> State;
    st_init: SV.set_In f (proj1_sig (st_exec 0));
    st_next: forall i, Next (st_exec i) (st_exec (S i));
    st_rec: forall g, SV.set_In g (subForm f) ->
      forall i, exists i', i' >=i /\ (@dcPred (Rec g (st_exec i')))
  }.

  Lemma subSubset: forall f, SV.set_In f SF -> SV.subset (subForm f) SF.
  Admitted.
    
  Lemma subStable: forall f, SV.set_In f SF -> Stable (subForm f).
  Proof.
  Admitted.
  
  Program Definition True2st : State := exist _ (SV.sing (fmDec Sg) (FTrue _)) _.
  Next Obligation.
    apply SV.InFilter_P_intro.
    apply SV.InSingPow_intro.
    apply subTrue.
    simpl.
    split; intros; try (destruct H; try discriminate; destruct H).
    intro.
    destruct H.
    destruct H; try destruct H.
    simpl in H0.
    destruct H0; try tauto.
    discriminate.
  Qed.
  
  (*
  Program Definition addF (st: State) : State := 
    exist _ (SV.union (T:=fmDec Sg) (proj1_sig st) (SV.inter (T:=fmDec Sg) SF (SV.image (T1:=fmDec Sg) (T2:=fmDec Sg) (F Sg) (proj1_sig st)))) _.
  Next Obligation.
    generalize H; intro H1.
    apply SV.FilterSubset in H.
    apply SV.InFilter_P in H1.
    apply SV.InFilter_P_intro.
    apply SV.pow_union; auto.
    apply SV.InPow_intro.
  Qed.
  *)
  
  Lemma sat_complete: forall f (h: SV.set_In f SF),
    isSat Sg f -> satisfiable f.
  Proof.
    induction f; intros; auto.
    - split with (fun t => True2st).
      left; reflexivity.
      intro; split; simpl; intros; auto.

      split; intro.
      left; destruct H1; try tauto.
      destruct f; simpl in H1; try discriminate; now auto.
      left; destruct H1; try tauto.
      subst f; reflexivity.
      
      split; intro.
      destruct H1; tauto.
      left; destruct H1.
      destruct H1; try tauto; subst f.
      destruct f; simpl in H1; try discriminate; now auto.
      left; destruct H1; try tauto.
      subst f; reflexivity.
      
  Qed.

  Lemma sat_correct: forall f (h: SV.set_In f SF),
    satisfiable f -> isSat Sg f.
  Proof.
  Qed.
  
End SAT.


Inductive nLTL :=
  nG : forall K, nFO -> n

(*
 norm: G (\/_i EX (pi & X qi))
 p: ALL ATM
 q: LTL_F (ALL ATM)
*)

Inductive Node F :=
| Leaf
| Next: bool -> F -> Node F.

Definition at2node {Sg} (a: atom Sg): Node (formula Sg) := Leaf _ .

Fixpoint fm2node {Sg} (f: formula Sg): Node (formula Sg) :=
  match f with
    Atom a => at2node a
  | F f => 
  end.

Fixpoint sat {Sg} (new: SV.set (formula Sg)) (h: forall f, SV.set_In f new -> noG f) :=
  match new with
    [] => True
  | (IAnd K fk :: r) => sat (SV.union (GUnion K fk) r) _
  | (IOr K fk :: r) => exists k, sat (SV.add (fk k) r) _ 
  | (ExD v f :: r) => sat (SV.add f r) _
  | (F f :: r) => sat (SV.add d r) _
  | (G f :: r) => match h (G f) _ with end
  | X f => sat (SV.add f r)
  end.
