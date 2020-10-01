Add LoadPath "$HOME/COQ/FO-LTL" as Top.

Require Import Top.foltl.

Module V1.

Definition fragment `(Sg: Sig) := formula Sg -> Prop.

Definition fragOp `(Sg: Sig) := fragment Sg -> fragment Sg.

Definition fcomp `{Sg: Sig} (F1 F2: fragOp Sg): fragOp Sg :=
  fun P f => (F1 (F2 P)) f.

Fixpoint EX `{Sg: Sig} (P: formula Sg -> Prop) (f: formula Sg) :=
  match f with
  | Ex _ s v f => EX P f
  | _ => P f
  end.

Fixpoint ALL `{Sg: Sig} (P: formula Sg -> Prop) (f: formula Sg) :=
  match f with
  | All _ s v f => ALL P f
  | _ => P f
  end.

Definition ATM `{Sg: Sig} (f: formula Sg) :=
  match f with
    FTrue _ | FFalse _ => True
  | Atom _ _ => True
  | _ => False
  end.

Fixpoint PROP `{Sg: Sig} (P: formula Sg -> Prop) (f: formula Sg) :=
  match f with
  | And _ f1 f2 | Or _ f1 f2 => PROP P f1 /\ PROP P f2
  | FTrue _ | FFalse _ => True
  | _ => P f
  end.

Fixpoint LTL `{Sg: Sig} (P: formula Sg -> Prop) (f: formula Sg) :=
  match f with
    F _ f => LTL P f
  | G _ f => LTL P f
  | And _ f1 f2 | Or _ f1 f2 => LTL P f1 /\ LTL P f2
  | FTrue _ | FFalse _ => True
  | _ => P f
  end.

Fixpoint FO `{Sg: Sig} (P: formula Sg -> Prop) (f: formula Sg) :=
  match f with
    FTrue _ | FFalse _ => True
  | And _ f1 f2 | Or _ f1 f2 => FO P f1 /\ FO P f2
  | Ex _ s v f | All _ s v f => FO P f
  | _ => P f
  end.

Notation "o # p" := (o p) (at level 48, right associativity).
Definition exemple `(Sg: Sig) :=
  EX # ALL # LTL # ATM.

End V1.

Module V2.
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

Definition ATM `{Sg: Sig} (f: formula Sg) :=
  match f with
    FTrue _ | FFalse _ => True
  | Atom _ _ => True
  | _ => False
  end.

Notation "t # p" := (fun f => p (t f)) (at level 48, right associativity).
Definition exemple `(Sg: Sig) :=
  EX # ALL # ATM.

End V2.

