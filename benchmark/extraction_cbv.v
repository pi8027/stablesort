From mathcomp Require Import all_ssreflect.
From stablesort Require Import stablesort.
From Coq Require Import Extraction.

Set Extraction Flag 2031.

Include CBV.

(******************************************************************************)

Extraction Language Haskell.

Extract Inductive bool => "Prelude.Bool" ["Prelude.True" "Prelude.False"].

Extract Inlined Constant negb => "Prelude.not".
Extract Inlined Constant eqb => "(Prelude.==)".

Extract Inductive list => "([])" ["([])" "(:)"].

Extraction "benchmark/haskell/MergesortCoqCbv.hs" sort1 sort2 sort3 sortN.

(******************************************************************************)

Extraction Language OCaml.

Extract Inductive bool => "bool" ["true" "false"].

Extract Inlined Constant negb => "not".
Extract Inlined Constant eqb => "((=) : bool -> bool -> bool)".

Extract Inductive list => "list" ["[]" "(::)"].

Extract Inlined Constant catrev => "List.rev_append".
Extract Inlined Constant rev => "List.rev".

Extraction "benchmark/ocaml/mergesort_coq_cbv.ml" sort1 sort2 sort3 sortN.
