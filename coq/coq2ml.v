Require Import String.

Require Import foltl.
Require Import api.
Require Import dec.
Require Import finite.
Require utils.

Section COQ2ML.

  Context {Ts: Type} {Tv: Ts->Type} {Tc: Ts->Type} {Tp: Type}.
  Variable Sg: @Sig Ts Tv Tc Tp.

  Variable sort2ml: Sort (Sig:=Sg) -> mlSort.
  Variable varName : forall {s: Sort (Sig:=Sg)}, variable (Sig:=Sg) s -> string.
  Variable cstName : forall {s: Sort (Sig:=Sg)}, constant (Sig:=Sg) s -> string.
  Variable relName : predicate (Sig:=Sg) -> string.

  Definition var2ml {s: Sort (Sig:=Sg)} (v: variable (Sig:=Sg) s) : mlVariable := {|
    mlVarName := varName v;
    mlVarSort := sort2ml s;
  |}.

  Definition cst2ml {s: Sort (Sig:=Sg)} (c: constant (Sig:=Sg) s) : mlConstant := {|
    mlCstName := cstName c;
    mlCstSort := sort2ml s;
  |}.

  Definition rel2ml (r: predicate (Sig:=Sg)) : string := relName r.

  Definition tm2ml {s} (tm: term Sg s) :=
    match tm with
      Var _ _ v => MLVar (var2ml v)
    | Cst _ _ c => MLCst (cst2ml c)
    end.

  Definition lt2ml (l: literal Sg) :=
    match l with
      PApp _ x p a => MLPApp x (rel2ml p) (utils.fmap (fun i => tm2ml (a i)))
    end.

  Definition at2ml (a: atom Sg) :=
  match a with
    Literal _ l => MLLiteral (lt2ml l)
  | NLiteral _ l => MLNLiteral (lt2ml l)
  | Eq _ s t1 t2 => MLEq (tm2ml t1) (tm2ml t2)
  | NEq _ s t1 t2 => MLNEq (tm2ml t1) (tm2ml t2)
  end.

  Fixpoint fm2ml (f: formula Sg) :=
  match f with
    | FTrue _ => MLFTrue
    | FFalse _ => MLFFalse
    | Atom _ a => MLAtom (at2ml a)
    | And _ f1 f2 => MLAnd (fm2ml f1) (fm2ml f2)
    | Or _ f1 f2 => MLOr (fm2ml f1) (fm2ml f2)
    | Ex _ s v f => MLEx (var2ml v) (fm2ml f)
    | All _ s v f => MLAll (var2ml v) (fm2ml f)
    | F _ f => MLF(fm2ml f)
    | G _ f => MLG (fm2ml f)
  end.

End COQ2ML.
