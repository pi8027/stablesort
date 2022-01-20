From Coq Require Import NArith List.
From mathcomp Require Import all_ssreflect.
From stablesort Require Import stablesort.
From benchmark Require Import benchmark.

Elpi sort_benchmark
  "compute-total-random" "compute"
  9 (map (N.pow 2) (N_iota 3 10)) (id)
  "CBN.sort2"    (eager_bench CBN.sort2)
  "CBN.sort3"    (eager_bench CBN.sort3)
  "CBN.sortN"    (eager_bench CBN.sortN)
  "CBV.sort2"    (eager_bench CBV.sort2)
  "CBV.sort3"    (eager_bench CBV.sort3)
  "CBV.sortN"    (eager_bench CBV.sortN).

Elpi sort_benchmark
  "compute-total-smooth" "compute"
  9 (map (N.pow 2) (N_iota 3 10)) (sort_blocks N.leb 50)
  "CBN.sort2"    (eager_bench CBN.sort2)
  "CBN.sort3"    (eager_bench CBN.sort3)
  "CBN.sortN"    (eager_bench CBN.sortN)
  "CBV.sort2"    (eager_bench CBV.sort2)
  "CBV.sort3"    (eager_bench CBV.sort3)
  "CBV.sortN"    (eager_bench CBV.sortN).
