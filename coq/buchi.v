Add LoadPath "$HOME/COQ/FO-LTL" as Top.

Require Import Top.foltl.

Fixpoint ALL `{Sg: Sig} P (f: formula Sg) :=
  match f with
  | And _ f1 f2 | Or _ f1 f2 => ALL P f1 /\ ALL P f2
  | All _ s v f => ALL P f
  | _ => P f
  end.

Fixpoint ELTL `{Sg: Sig} P (f: formula Sg) :=
  match f with
  | And _ f1 f2 | Or _ f1 f2 => ELTL P f1 /\ ELTL P f2  
  | Ex _ s v f => ELTL P f
  | F _ f => ELTL P f
  | G _ f => ELTL P f
  | _ => P f
  end.

Definition ATM `{Sg: Sig} (f: formula Sg) :=
  match f with
    FTrue _ | FFalse _ => True
  | Atom _ _ => True
  | _ => False
  end.

(*
Fixpoint split {Sg} (f: formula Sg) (h: ELTL (ALL ATM) f) :=
  *)
