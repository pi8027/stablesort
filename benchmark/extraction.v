From mathcomp Require Import all_ssreflect.
From stablesort Require Import stablesort.
From Coq Require Import Extraction.

Set Extraction Flag 2031.

(******************************************************************************)

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].

Extract Inlined Constant negb => "Prelude.not".
Extract Inlined Constant eqb => "(Prelude.==)".

Extract Inductive list => "([])" ["([])" "(:)"].

Extraction "benchmark/MergesortCoqCbn.hs" CBN.sort.
Extraction "benchmark/MergesortCoqCbv.hs" CBV.sort.

(******************************************************************************)

Extraction Language OCaml.

Extract Inductive bool => "bool" ["true" "false"].

Extract Inlined Constant negb => "not".
Extract Inlined Constant eqb => "((=) : bool -> bool -> bool)".

Extract Inductive list => "list" ["[]" "(::)"].

Extract Inlined Constant catrev => "List.rev_append".
Extract Inlined Constant rev => "List.rev".

Extraction "benchmark/mergesort_coq.ml" CBN.sort CBV.sort.
