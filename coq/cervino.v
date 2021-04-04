Require Import foltl.
Require Import stability.
Require Import closure.
Require Import dec.
Require Import finite.
Require Import set.
Require abstraction.
Require extension.

Definition allTm `{Prd: Type} `(Sg: Sig (Tp:=Prd)) (s: Sort): SV.set (tmDec Sg s) :=
  SV.union (T:=tmDec Sg s)
    (SV.image (T1:=variable (Sig:=Sg) s) (T2:=tmDec Sg s) (Var Sg s) (fin_set (Finite:=variable (Sig:=Sg) s)))
    (SV.image (T1:=constant (Sig:=Sg) s) (T2:=tmDec Sg s) (Cst Sg s) (fin_set (Finite:=constant (Sig:=Sg) s))).

(*
  { p x1,...xn | xi in Var + Cst & p : Pred }
*)

Definition allLit `(Sg: Sig): SV.set (ltDec Sg) :=
  SV.CUnion
    (U:=predicate (Sig:=Sg))
    (T0:=ltDec Sg)
    (fun _ => TrueDec)
    (fin_set (Finite:=predicate (Sig:=Sg)))
    (fun (p: predicate (Sig:=Sg)) _ => 
      SV.CUnion
        (U := DepFunFin (uptoFinite (pr_arity p)) (fun i => asFinite (allTm Sg (pr_args p i))))
        (T0 := ltDec Sg)
        (fun _ => TrueDec)
        (fin_set (Finite:=DepFunFin (uptoFinite (pr_arity p)) (fun i => asFinite (allTm Sg (pr_args p i)))))
        (fun a _ => SV.sing (ltDec Sg) (PApp Sg 0 p (fun i => proj1_sig (a i))))).

Structure Cervino := {
  CV_sortsType: Type;
  CV_varsType: CV_sortsType -> Type;
  CV_cstsType: CV_sortsType -> Type;
  CV_prdsType: Type;
  CV_sig: @Sig CV_sortsType CV_varsType CV_cstsType CV_prdsType;
  CV_hyps: formula CV_sig; (* NNF, pas de E dans A ou G - elim de =, skolem, instanciation *)
  CV_EventType: Type;
  CV_Event: @Finite CV_EventType;
  CV_modify: CV_Event -> formula CV_sig;
  CV_body: CV_Event -> formula CV_sig;
  CV_body_EA: forall ev, isExAll _ (CV_body ev);
  CV_body_FV: forall ev s, SV.is_empty (vars.free _ (CV_body ev) s);
  CV_stab: CV_Event -> formula CV_sig;
  (* contrainte : que du X *)
  CV_frm: predicate -> formula CV_sig;
  CV_pargs: forall p i, variable (Sig := CV_sig) (pr_args p i);
  CV_wf: forall ev, isStable CV_sig CV_frm CV_pargs (allLit CV_sig) (CV_stab ev)
}.
Coercion CV_sig: Cervino >-> Sig.

Definition CV_sem (cv: Cervino) :=
  And cv (CV_hyps cv)
    (G cv (IEx cv (DepPairFin Sort variable) (fun sv => projT1 sv) (fun sv => projT2 sv)
        (IOr cv (CV_Event cv) (fun ev => And cv (CV_modify cv ev)  (CV_body cv ev))))).

Definition TEA_ext {cv: Cervino} (ev: CV_Event cv) : 
  extension.Extension (abstraction.dstSig cv (quantifiers.getExF (CV_body cv ev)))
                        (abstraction.dstSig cv (fun s => fin_set (Finite:=variable s))).
Admitted.
(*
Program Definition TEA (cv: Cervino): Cervino := {|
  CV_sig := abstraction.dstSig (CV_sig cv) (fun s => fin_set (Finite:=variable s));
  CV_hyps := _;
  CV_Event := CV_Event cv;
  CV_body ev := extension.ext_fm (TEA_ext ev) (abstraction.abstract_ExAll _ (CV_body cv ev) (CV_body_EA cv ev) (CV_body_FV cv ev));
|}.

Lemma TEA_OK: forall cv, isSat (CV_sem cv) -> isSat (CV_sem (TEA cv)).
Admitted.
*)
