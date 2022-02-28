From Coq Require Import NArith List.
From mathcomp Require Import all_ssreflect.
From stablesort Require Import stablesort.
From benchmark Require Import benchmark.

Definition lazy_bench
  (sort : forall T : Type, rel T -> seq T -> seq T) (n : N) (xs : seq N) :=
  sorted N.leb (take (N.to_nat (N.div n 4)) (sort _ N.leb xs)).

Elpi sort_benchmark
  "lazy-partial-random" "lazy"
  9 (map (N.pow 2) (N_iota 3 10)) (id)
  "CBN.sort2"    (lazy_bench CBN.sort2)
  "CBN.sort3"    (lazy_bench CBN.sort3)
  "CBN.sortN"    (lazy_bench CBN.sortN)
  "CBV.sort2"    (lazy_bench CBV.sort2)
  "CBV.sort3"    (lazy_bench CBV.sort3)
  "CBV.sortN"    (lazy_bench CBV.sortN).

Elpi sort_benchmark
  "lazy-partial-smooth" "lazy"
  9 (map (N.pow 2) (N_iota 3 10)) (sort_blocks N.leb 50)
  "CBN.sort2"    (lazy_bench CBN.sort2)
  "CBN.sort3"    (lazy_bench CBN.sort3)
  "CBN.sortN"    (lazy_bench CBN.sortN)
  "CBV.sort2"    (lazy_bench CBV.sort2)
  "CBV.sort3"    (lazy_bench CBV.sort3)
  "CBV.sortN"    (lazy_bench CBV.sortN).

Elpi sort_benchmark
  "lazy-total-random" "lazy"
  9 (map (N.pow 2) (N_iota 3 10)) (id)
  "CBN.sort2"    (eager_bench CBN.sort2)
  "CBN.sort3"    (eager_bench CBN.sort3)
  "CBN.sortN"    (eager_bench CBN.sortN)
  "CBV.sort2"    (eager_bench CBV.sort2)
  "CBV.sort3"    (eager_bench CBV.sort3)
  "CBV.sortN"    (eager_bench CBV.sortN).

Elpi sort_benchmark
  "lazy-total-smooth" "lazy"
  9 (map (N.pow 2) (N_iota 3 10)) (sort_blocks N.leb 50)
  "CBN.sort2"    (eager_bench CBN.sort2)
  "CBN.sort3"    (eager_bench CBN.sort3)
  "CBN.sortN"    (eager_bench CBN.sortN)
  "CBV.sort2"    (eager_bench CBV.sort2)
  "CBV.sort3"    (eager_bench CBV.sort3)
  "CBV.sortN"    (eager_bench CBV.sortN).
