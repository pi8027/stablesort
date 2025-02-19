let test_stability sort =
  QCheck.Test.make ~count:2000 ~name:"sort_stability"
    QCheck.(list (pair small_nat small_nat))
    (fun l ->
       let cmp_fst x y = compare (fst x) (fst y) in
       sort cmp_fst l = List.stable_sort cmp_fst l);;

QCheck.Test.check_exn (test_stability Mergesort_ocaml.NTR1.sort3N);;
QCheck.Test.check_exn (test_stability Mergesort_ocaml.NTR2.sort3N);;
QCheck.Test.check_exn (test_stability Mergesort_ocaml.TRMC1.sort3N);;
QCheck.Test.check_exn (test_stability Mergesort_ocaml.TRMC2.sort3N);;
QCheck.Test.check_exn (test_stability Mergesort_ocaml.TR1.sortN);;
QCheck.Test.check_exn (test_stability Mergesort_ocaml.TR2.sortN);;
QCheck.Test.check_exn (test_stability Mergesort_ocaml.TR1.sort3N);;
QCheck.Test.check_exn (test_stability Mergesort_ocaml.TR2.sort3N);;
