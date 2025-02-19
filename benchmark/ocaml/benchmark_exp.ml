Random.self_init ();;
Gc.set { (Gc.get()) with Gc.minor_heap_size = 2 * 1024 * 1024 * 1024 };;

Benchlib.benchmark "ocaml-random" (List.init 15 (fun i -> Int.shift_left 128 i)) (fun xs -> xs)
  [("List.stable_sort",   List.stable_sort               (compare : int -> int -> int));
   ("NTR1.sort3N",        Mergesort_ocaml.NTR1.sort3N    (compare : int -> int -> int));
   ("NTR2.sort3N",        Mergesort_ocaml.NTR2.sort3N    (compare : int -> int -> int));
   ("TRMC1.sort3N",       Mergesort_ocaml.TRMC1.sort3N   (compare : int -> int -> int));
   ("TRMC2.sort3N",       Mergesort_ocaml.TRMC2.sort3N   (compare : int -> int -> int));
   ("TR1.sortN",          Mergesort_ocaml.TR1.sortN      (compare : int -> int -> int));
   ("TR2.sortN",          Mergesort_ocaml.TR2.sortN      (compare : int -> int -> int));
   ("TR1.sort3N",         Mergesort_ocaml.TR1.sort3N     (compare : int -> int -> int));
   ("TR2.sort3N",         Mergesort_ocaml.TR2.sort3N     (compare : int -> int -> int));
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
   ("NTR1.sort3N",        Mergesort_ocaml.NTR1.sort3N    (compare : int -> int -> int));
   ("NTR2.sort3N",        Mergesort_ocaml.NTR2.sort3N    (compare : int -> int -> int));
   ("TRMC1.sort3N",       Mergesort_ocaml.TRMC1.sort3N   (compare : int -> int -> int));
   ("TRMC2.sort3N",       Mergesort_ocaml.TRMC2.sort3N   (compare : int -> int -> int));
   ("TR1.sortN",          Mergesort_ocaml.TR1.sortN      (compare : int -> int -> int));
   ("TR2.sortN",          Mergesort_ocaml.TR2.sortN      (compare : int -> int -> int));
   ("TR1.sort3N",         Mergesort_ocaml.TR1.sort3N     (compare : int -> int -> int));
   ("TR2.sort3N",         Mergesort_ocaml.TR2.sort3N     (compare : int -> int -> int));
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
