open Mergesort_ocaml;;

Random.self_init ();;
Gc.set { (Gc.get()) with Gc.minor_heap_size = 2 * 1024 * 1024 * 1024 };;

Benchlib.benchmark "ocaml-random" (List.init 15 (fun i -> Int.shift_left 128 i)) (fun xs -> xs)
  [("List.stable_sort",   StdlibSort.sort                ((<=) : int -> int -> bool));
   ("NTRStack.sort3",     NTRStack.sort3                 ((<=) : int -> int -> bool));
   ("NTRStack.sortN",     NTRStack.sortN                 ((<=) : int -> int -> bool));
   ("NTRStack.sort3N",    NTRStack.sort3N                ((<=) : int -> int -> bool));
   ("NTRStack_.sort3",    NTRStack_.sort3                ((<=) : int -> int -> bool));
   ("NTRStack_.sortN",    NTRStack_.sortN                ((<=) : int -> int -> bool));
   ("NTRStack_.sort3N",   NTRStack_.sort3N               ((<=) : int -> int -> bool));
   ("TRMCStack.sort3",    TRMCStack.sort3                ((<=) : int -> int -> bool));
   ("TRMCStack.sortN",    TRMCStack.sortN                ((<=) : int -> int -> bool));
   ("TRMCStack.sort3N",   TRMCStack.sort3N               ((<=) : int -> int -> bool));
   ("TRMCStack_.sort3",   TRMCStack_.sort3               ((<=) : int -> int -> bool));
   ("TRMCStack_.sortN",   TRMCStack_.sortN               ((<=) : int -> int -> bool));
   ("TRMCStack_.sort3N",  TRMCStack_.sort3N              ((<=) : int -> int -> bool));
   ("TRStack.sort3",      TRStack.sort3                  ((<=) : int -> int -> bool));
   ("TRStack.sortN",      TRStack.sortN                  ((<=) : int -> int -> bool));
   ("TRStack.sort3N",     TRStack.sort3N                 ((<=) : int -> int -> bool));
   ("TRStack_.sort3",     TRStack_.sort3                 ((<=) : int -> int -> bool));
   ("TRStack_.sortN",     TRStack_.sortN                 ((<=) : int -> int -> bool));
   ("TRStack_.sort3N",    TRStack_.sort3N                ((<=) : int -> int -> bool));
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
  [("List.stable_sort",   StdlibSort.sort                ((<=) : int -> int -> bool));
   ("NTRStack.sort3",     NTRStack.sort3                 ((<=) : int -> int -> bool));
   ("NTRStack.sortN",     NTRStack.sortN                 ((<=) : int -> int -> bool));
   ("NTRStack.sort3N",    NTRStack.sort3N                ((<=) : int -> int -> bool));
   ("NTRStack_.sort3",    NTRStack_.sort3                ((<=) : int -> int -> bool));
   ("NTRStack_.sortN",    NTRStack_.sortN                ((<=) : int -> int -> bool));
   ("NTRStack_.sort3N",   NTRStack_.sort3N               ((<=) : int -> int -> bool));
   ("TRMCStack.sort3",    TRMCStack.sort3                ((<=) : int -> int -> bool));
   ("TRMCStack.sortN",    TRMCStack.sortN                ((<=) : int -> int -> bool));
   ("TRMCStack.sort3N",   TRMCStack.sort3N               ((<=) : int -> int -> bool));
   ("TRMCStack_.sort3",   TRMCStack_.sort3               ((<=) : int -> int -> bool));
   ("TRMCStack_.sortN",   TRMCStack_.sortN               ((<=) : int -> int -> bool));
   ("TRMCStack_.sort3N",  TRMCStack_.sort3N              ((<=) : int -> int -> bool));
   ("TRStack.sort3",      TRStack.sort3                  ((<=) : int -> int -> bool));
   ("TRStack.sortN",      TRStack.sortN                  ((<=) : int -> int -> bool));
   ("TRStack.sort3N",     TRStack.sort3N                 ((<=) : int -> int -> bool));
   ("TRStack_.sort3",     TRStack_.sort3                 ((<=) : int -> int -> bool));
   ("TRStack_.sortN",     TRStack_.sortN                 ((<=) : int -> int -> bool));
   ("TRStack_.sort3N",    TRStack_.sort3N                ((<=) : int -> int -> bool));
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
