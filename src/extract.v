
Require Import String.

Require Import coqfo.api.

Require Extraction.

Require Import Coq.extraction.ExtrOcamlBasic.

Require Import extraction.ExtrOcamlString.
Extract Inlined Constant String.append => "(^)".
Extract Inlined Constant String.string_dec => "(=)".
Extract Inductive string => "string" [ """""" "(fun (a, b) -> (String.make 1 a) ^ b)"] "(fun e c s -> if s = """" then e else c s.[0] (String.sub s 1 (String.length s - 1)))".

Extract Inductive nat => int [ "0" "succ" ] "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

Extraction "extract.ml" MLCervino.