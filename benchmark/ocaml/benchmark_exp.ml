open Mergesort_ocaml;;

Random.self_init ();;
Gc.set { (Gc.get()) with Gc.minor_heap_size = 2 * 1024 * 1024 * 1024 };;

Benchlib.benchmark "ocaml-random" (List.init 15 (fun i -> Int.shift_left 128 i)) (fun xs -> xs)
  [("List.stable_sort",   List.stable_sort               (compare : int -> int -> int));
   ("NTRCount.sortN",     NTRCount.sortN                 (compare : int -> int -> int));
   ("NTRCount.sort3N",    NTRCount.sort3N                (compare : int -> int -> int));
   ("NTRStack.sortN",     NTRStack.sortN                 (compare : int -> int -> int));
   ("NTRStack.sort3N",    NTRStack.sort3N                (compare : int -> int -> int));
   ("TRMCCount.sortN",    TRMCCount.sortN                (compare : int -> int -> int));
   ("TRMCCount.sort3N",   TRMCCount.sort3N               (compare : int -> int -> int));
   ("TRMCStack.sortN",    TRMCStack.sortN                (compare : int -> int -> int));
   ("TRMCStack.sort3N",   TRMCStack.sort3N               (compare : int -> int -> int));
   ("TRCount.sortN",      TRCount.sortN                  (compare : int -> int -> int));
   ("TRCount.sort3N",     TRCount.sort3N                 (compare : int -> int -> int));
   ("TRStack.sortN",      TRStack.sortN                  (compare : int -> int -> int));
   ("TRStack.sort3N",     TRStack.sort3N                 (compare : int -> int -> int));
   ("CBNAcc.sort2",       Mergesort_coq_cbnacc.sort2     ((<=) : int -> int -> bool));
   ("CBNAcc.sort3",       Mergesort_coq_cbnacc.sort3     ((<=) : int -> int -> bool));
   ("CBNAcc.sortN",       Mergesort_coq_cbnacc.sortN     ((<=) : int -> int -> bool));
   ("CBNAcc.sort2 (TMC)", Mergesort_coq_cbnacc_tmc.sort2 ((<=) : int -> int -> bool));
   ("CBNAcc.sort3 (TMC)", Mergesort_coq_cbnacc_tmc.sort3 ((<=) : int -> int -> bool));
   ("CBNAcc.sortN (TMC)", Mergesort_coq_cbnacc_tmc.sortN ((<=) : int -> int -> bool));
   ("CBVAcc.sort2",       Mergesort_coq_cbvacc.sort2     ((<=) : int -> int -> bool));
   ("CBVAcc.sort3",       Mergesort_coq_cbvacc.sort3     ((<=) : int -> int -> bool));
   ("CBVAcc.sortN",       Mergesort_coq_cbvacc.sortN     ((<=) : int -> int -> bool))]
;;

Benchlib.benchmark "ocaml-smooth" (List.init 15 (fun i -> Int.shift_left 128 i)) (Benchlib.sort_blocks 50)
  [("List.stable_sort",   List.stable_sort               (compare : int -> int -> int));
   ("NTRCount.sortN",     NTRCount.sortN                 (compare : int -> int -> int));
   ("NTRCount.sort3N",    NTRCount.sort3N                (compare : int -> int -> int));
   ("NTRStack.sortN",     NTRStack.sortN                 (compare : int -> int -> int));
   ("NTRStack.sort3N",    NTRStack.sort3N                (compare : int -> int -> int));
   ("TRMCCount.sortN",    TRMCCount.sortN                (compare : int -> int -> int));
   ("TRMCCount.sort3N",   TRMCCount.sort3N               (compare : int -> int -> int));
   ("TRMCStack.sortN",    TRMCStack.sortN                (compare : int -> int -> int));
   ("TRMCStack.sort3N",   TRMCStack.sort3N               (compare : int -> int -> int));
   ("TRCount.sortN",      TRCount.sortN                  (compare : int -> int -> int));
   ("TRCount.sort3N",     TRCount.sort3N                 (compare : int -> int -> int));
   ("TRStack.sortN",      TRStack.sortN                  (compare : int -> int -> int));
   ("TRStack.sort3N",     TRStack.sort3N                 (compare : int -> int -> int));
   ("CBNAcc.sort2",       Mergesort_coq_cbnacc.sort2     ((<=) : int -> int -> bool));
   ("CBNAcc.sort3",       Mergesort_coq_cbnacc.sort3     ((<=) : int -> int -> bool));
   ("CBNAcc.sortN",       Mergesort_coq_cbnacc.sortN     ((<=) : int -> int -> bool));
   ("CBNAcc.sort2 (TMC)", Mergesort_coq_cbnacc_tmc.sort2 ((<=) : int -> int -> bool));
   ("CBNAcc.sort3 (TMC)", Mergesort_coq_cbnacc_tmc.sort3 ((<=) : int -> int -> bool));
   ("CBNAcc.sortN (TMC)", Mergesort_coq_cbnacc_tmc.sortN ((<=) : int -> int -> bool));
   ("CBVAcc.sort2",       Mergesort_coq_cbvacc.sort2     ((<=) : int -> int -> bool));
   ("CBVAcc.sort3",       Mergesort_coq_cbvacc.sort3     ((<=) : int -> int -> bool));
   ("CBVAcc.sortN",       Mergesort_coq_cbvacc.sortN     ((<=) : int -> int -> bool))]
;;
