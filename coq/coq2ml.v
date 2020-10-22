Require Import String.

Require Import foltl.
Require api.
Require Import dec.
Require Import finite.
Require utils.

Section COQ2ML.

  Context {Ts: Type} {Tv: Ts->Type} {Tc: Ts->Type} {Tp: Type}.
  Variable Sg: @Sig Ts Tv Tc Tp.

  Variable sort2ml: Sort (Sig:=Sg) -> api.mlSort.
  Variable varName : forall {s: Sort (Sig:=Sg)}, variable (Sig:=Sg) s -> string.
  Variable cstName : forall {s: Sort (Sig:=Sg)}, constant (Sig:=Sg) s -> string.
  Variable relName : predicate (Sig:=Sg) -> string.

  Definition var2ml {s: Sort (Sig:=Sg)} (v: variable (Sig:=Sg) s) : api.variable := {|
    api.var_name := varName v;
    api.var_sort := sort2ml s;
  |}.

  Definition cst2ml {s: Sort (Sig:=Sg)} (c: constant (Sig:=Sg) s) : api.constant := {|
    api.cst_name := cstName c;
    api.cst_sort := sort2ml s;
  |}.

  Definition rel2ml (r: predicate (Sig:=Sg)) : string := relName r.

  Definition tm2ml {s} (tm: term Sg s) :=
    match tm with
      Var _ _ v => api.Var (var2ml v)
    | Cst _ _ c => api.Cst (cst2ml c)
    end.

  Definition lt2ml sgn (l: literal Sg): api.literal :=
    match l with
      PApp _ x p a => sgn x (rel2ml p) (utils.fmap (fun i => tm2ml (a i)))
    end.

  Definition at2ml (a: atom Sg) :=
  match a with
    Literal _ l => lt2ml api.Pos_app l
  | NLiteral _ l => lt2ml api.Neg_app l
  | Eq _ s t1 t2 => api.Eq (tm2ml t1) (tm2ml t2)
  | NEq _ s t1 t2 => api.Not_eq (tm2ml t1) (tm2ml t2)
  end.

  Fixpoint fm2ml (f: formula Sg) :=
  match f with
    | FTrue _ => api.True
    | FFalse _ => api.False
    | Atom _ a => api.Lit (at2ml a)
    | And _ f1 f2 => api.And (fm2ml f1) (fm2ml f2)
    | Or _ f1 f2 => api.Or (fm2ml f1) (fm2ml f2)
    | Ex _ s v f => api.Exists (var2ml v) (fm2ml f)
    | All _ s v f => api.All (var2ml v) (fm2ml f)
    | F _ f => api.F (fm2ml f)
    | G _ f => api.G (fm2ml f)
  end.

End COQ2ML.
