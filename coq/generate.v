Add LoadPath "$HOME/COQ/FO-LTL" as Top.

Require Import Top.foltl.
Require Import Top.abstraction.
Require Import Top.dec.
Require Import Top.finite.

Require Extraction.

(*
Extract Inlined Constant DataType => "int".
Extract Inlined Constant dZero => "0".
Extract Inlined Constant dAdd => "(+)".
Extract Inlined Constant dInc => "succ".

Require Import extraction.ExtrOcamlString.
Extract Inlined Constant print => "print_string".
Extract Inlined Constant String.append => "(^)".
Extract Inductive string => "string" [ """""" "(fun (a, b) -> (String.make 1 a) ^ b)"] "(fun e c s -> if s = """" then e else c s.[0] (String.sub s 1 (String.length s - 1)))".
*)

Require Import Coq.extraction.ExtrOcamlBasic.

Extract Inductive nat => int [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Extract Inlined Constant app => "(@)".

Extract Inductive sigT => "( * )" [ "" ].
Extract Inlined Constant projT1 => "fst".
Extract Inlined Constant projT2 => "snd".

Extraction "/tmp/generate.ml" abstract_ExAll.
