Require Import api.
Require Import api2coq.
Require Import abstraction.
Require Import foltl.
Require Import set.
Require Import finite.

(***
Record mlSignedFormula := { (* A REVOIR: changement de signature *)
  mlSfForm : mlFormula;
}.

Definition mlTransform (m: mlModel) (chk: mlCheck) : option mlSignedFormula.
Admitted.
***)
Module Transfo (Sg: MLSignature).
  Module Import AsCoq := ML2Coq(Sg).
  Import Cervino.

  Definition mlConj l := List.fold_right (fun a r => MLAnd a r) MLFTrue l.

  Definition mlDisj l := List.fold_right (fun a r => MLOr a r) MLFFalse l.

  Definition mlArgs2Ex l f := List.fold_right (fun v r => MLEx v r) f l.
   
  Definition mlEvtSem e :=
    mlArgs2Ex (mlEvArgs e) (mlEvBody e).

  Definition mdl_sem (m: mlModel) :=
    let axms := mlConj (mlAxioms m) in
    let evts := mlDisj (List.map mlEvtSem (mlEvents m)) in
    MLAnd axms evts.

  Definition applyTEA (m: mlModel) (chk: mlCheck) :=
    let f := mlChkBody chk in
    let cf := mlFormula2formula f in
    let fv s := vars.free coqSig cf s in 
    match isExAll_dec coqSig cf with
      left exAll => 
        match all_dec (fun s => SV.emptyDec (fv s)) with
          inl ise => Some (abstract_ExAll coqSig cf exAll ise)
        | inr _ => None
        end
    | right _ => None
    end.

  Definition mlTransform (m: mlModel) (chk: mlCheck) :=
    match mlChkUsing chk with
      TEA => applyTEA m chk
    | _ => None
    end.

End Transfo.
