
Require Import String.

Require Import coqfo.api.
Require Import coqfo.dec.
Require Import coqfo.finite.
Require Import coqfo.abstraction.
Require coqfo.transfo.

Require Extraction.

Require Import Coq.extraction.ExtrOcamlBasic.

Require Import extraction.ExtrOcamlString.
Extract Inlined Constant String.append => "(^)".
Extract Inlined Constant String.string_dec => "(=)".
Extract Inductive string => "string" [ """""" "(fun (a, b) -> (String.make 1 a) ^ b)"] "(fun e c s -> if s = """" then e else c s.[0] (String.sub s 1 (String.length s - 1)))".

Extract Inductive nat => int [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Extract Inductive sigT => "( * )" [ "" ].
Extract Inlined Constant projT1 => "fst".
Extract Inlined Constant projT2 => "snd".

Extraction Inline eq_dec dc_dec.
Extraction Inline dec.OneDec dec.isEq2_obligation_1 dec.PairDec_obligation_1.
Extraction Inline finite.asDec_obligation_1 finite.asDec abstraction.newPredDec_obligation_1.

Extraction "/tmp/extract.ml" transfo.mlTransform.
