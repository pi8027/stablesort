From Coq Require Import NArith.
From mathcomp Require Import all_ssreflect.
From stablesort Require Import stablesort.
From benchmark Require Import benchmark.

Elpi sort_benchmark
  "vm1" "vm_compute"
  (map (N.mul 1000) (N_iota 1 40)) (id)
  "CBN.sort1"    (eager_bench CBN.sort1)
  "CBN.sort2"    (eager_bench CBN.sort2)
  "CBN.sort3"    (eager_bench CBN.sort3)
  "CBN.sortN"    (eager_bench CBN.sortN)
  "CBNAcc.sort1" (eager_bench CBNAcc.sort1)
  "CBNAcc.sort2" (eager_bench CBNAcc.sort2)
  "CBNAcc.sort3" (eager_bench CBNAcc.sort3)
  "CBNAcc.sortN" (eager_bench CBNAcc.sortN)
  "CBV.sort1"    (eager_bench CBV.sort1)
  "CBV.sort2"    (eager_bench CBV.sort2)
  "CBV.sort3"    (eager_bench CBV.sort3)
  "CBV.sortN"    (eager_bench CBV.sortN)
  "CBVAcc.sort1" (eager_bench CBVAcc.sort1)
  "CBVAcc.sort2" (eager_bench CBVAcc.sort2)
  "CBVAcc.sort3" (eager_bench CBVAcc.sort3)
  "CBVAcc.sortN" (eager_bench CBVAcc.sortN).
