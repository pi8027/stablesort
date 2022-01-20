Random.self_init ();;
Gc.set { (Gc.get()) with Gc.minor_heap_size = 2 * 1024 * 1024 * 1024 };;

Benchlib.benchmark "ocaml1" (List.init 40 (fun i -> 25000 * (i + 1))) (fun xs -> xs)
  [("List.stable_sort",   List.stable_sort               (compare : int -> int -> int));
   ("CBN.sort1",          Mergesort_coq_cbn.sort1        ((<=) : int -> int -> bool));
   ("CBN.sort2",          Mergesort_coq_cbn.sort2        ((<=) : int -> int -> bool));
   ("CBN.sort3",          Mergesort_coq_cbn.sort3        ((<=) : int -> int -> bool));
   ("CBN.sortN",          Mergesort_coq_cbn.sortN        ((<=) : int -> int -> bool));
   ("CBNAcc.sort1",       Mergesort_coq_cbnacc.sort1     ((<=) : int -> int -> bool));
   ("CBNAcc.sort2",       Mergesort_coq_cbnacc.sort2     ((<=) : int -> int -> bool));
   ("CBNAcc.sort3",       Mergesort_coq_cbnacc.sort3     ((<=) : int -> int -> bool));
   ("CBNAcc.sortN",       Mergesort_coq_cbnacc.sortN     ((<=) : int -> int -> bool));
   ("CBN.sort1 (TMC)",    Mergesort_coq_cbn_tmc.sort1    ((<=) : int -> int -> bool));
   ("CBN.sort2 (TMC)",    Mergesort_coq_cbn_tmc.sort2    ((<=) : int -> int -> bool));
   ("CBN.sort3 (TMC)",    Mergesort_coq_cbn_tmc.sort3    ((<=) : int -> int -> bool));
   ("CBN.sortN (TMC)",    Mergesort_coq_cbn_tmc.sortN    ((<=) : int -> int -> bool));
   ("CBNAcc.sort1 (TMC)", Mergesort_coq_cbnacc_tmc.sort1 ((<=) : int -> int -> bool));
   ("CBNAcc.sort2 (TMC)", Mergesort_coq_cbnacc_tmc.sort2 ((<=) : int -> int -> bool));
   ("CBNAcc.sort3 (TMC)", Mergesort_coq_cbnacc_tmc.sort3 ((<=) : int -> int -> bool));
   ("CBNAcc.sortN (TMC)", Mergesort_coq_cbnacc_tmc.sortN ((<=) : int -> int -> bool));
   ("CBV.sort1",          Mergesort_coq_cbv.sort1        ((<=) : int -> int -> bool));
   ("CBV.sort2",          Mergesort_coq_cbv.sort2        ((<=) : int -> int -> bool));
   ("CBV.sort3",          Mergesort_coq_cbv.sort3        ((<=) : int -> int -> bool));
   ("CBV.sortN",          Mergesort_coq_cbv.sortN        ((<=) : int -> int -> bool));
   ("CBVAcc.sort1",       Mergesort_coq_cbvacc.sort1     ((<=) : int -> int -> bool));
   ("CBVAcc.sort2",       Mergesort_coq_cbvacc.sort2     ((<=) : int -> int -> bool));
   ("CBVAcc.sort3",       Mergesort_coq_cbvacc.sort3     ((<=) : int -> int -> bool));
   ("CBVAcc.sortN",       Mergesort_coq_cbvacc.sortN     ((<=) : int -> int -> bool))]
;;

Benchlib.benchmark "ocaml2" (List.init 40 (fun i -> 25000 * (i + 1))) (Benchlib.sort_blocks 50)
  [("List.stable_sort",   List.stable_sort               (compare : int -> int -> int));
   ("CBN.sort1",          Mergesort_coq_cbn.sort1        ((<=) : int -> int -> bool));
   ("CBN.sort2",          Mergesort_coq_cbn.sort2        ((<=) : int -> int -> bool));
   ("CBN.sort3",          Mergesort_coq_cbn.sort3        ((<=) : int -> int -> bool));
   ("CBN.sortN",          Mergesort_coq_cbn.sortN        ((<=) : int -> int -> bool));
   ("CBNAcc.sort1",       Mergesort_coq_cbnacc.sort1     ((<=) : int -> int -> bool));
   ("CBNAcc.sort2",       Mergesort_coq_cbnacc.sort2     ((<=) : int -> int -> bool));
   ("CBNAcc.sort3",       Mergesort_coq_cbnacc.sort3     ((<=) : int -> int -> bool));
   ("CBNAcc.sortN",       Mergesort_coq_cbnacc.sortN     ((<=) : int -> int -> bool));
   ("CBN.sort1 (TMC)",    Mergesort_coq_cbn_tmc.sort1    ((<=) : int -> int -> bool));
   ("CBN.sort2 (TMC)",    Mergesort_coq_cbn_tmc.sort2    ((<=) : int -> int -> bool));
   ("CBN.sort3 (TMC)",    Mergesort_coq_cbn_tmc.sort3    ((<=) : int -> int -> bool));
   ("CBN.sortN (TMC)",    Mergesort_coq_cbn_tmc.sortN    ((<=) : int -> int -> bool));
   ("CBNAcc.sort1 (TMC)", Mergesort_coq_cbnacc_tmc.sort1 ((<=) : int -> int -> bool));
   ("CBNAcc.sort2 (TMC)", Mergesort_coq_cbnacc_tmc.sort2 ((<=) : int -> int -> bool));
   ("CBNAcc.sort3 (TMC)", Mergesort_coq_cbnacc_tmc.sort3 ((<=) : int -> int -> bool));
   ("CBNAcc.sortN (TMC)", Mergesort_coq_cbnacc_tmc.sortN ((<=) : int -> int -> bool));
   ("CBV.sort1",          Mergesort_coq_cbv.sort1        ((<=) : int -> int -> bool));
   ("CBV.sort2",          Mergesort_coq_cbv.sort2        ((<=) : int -> int -> bool));
   ("CBV.sort3",          Mergesort_coq_cbv.sort3        ((<=) : int -> int -> bool));
   ("CBV.sortN",          Mergesort_coq_cbv.sortN        ((<=) : int -> int -> bool));
   ("CBVAcc.sort1",       Mergesort_coq_cbvacc.sort1     ((<=) : int -> int -> bool));
   ("CBVAcc.sort2",       Mergesort_coq_cbvacc.sort2     ((<=) : int -> int -> bool));
   ("CBVAcc.sort3",       Mergesort_coq_cbvacc.sort3     ((<=) : int -> int -> bool));
   ("CBVAcc.sortN",       Mergesort_coq_cbvacc.sortN     ((<=) : int -> int -> bool))]
;;
