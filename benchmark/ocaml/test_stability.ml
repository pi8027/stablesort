open Mergesort_ocaml;;

let test_stability sort =
  QCheck.Test.make ~count:2000 ~name:"sort_stability"
    QCheck.(list (pair small_nat small_nat))
    (fun l ->
       let cmp_fst x y = compare (fst x) (fst y) in
       sort cmp_fst l = List.stable_sort cmp_fst l);;

QCheck.Test.check_exn (test_stability NTRCount.sort3);;
QCheck.Test.check_exn (test_stability NTRCount.sortN);;
QCheck.Test.check_exn (test_stability NTRCount.sort3N);;
QCheck.Test.check_exn (test_stability NTRStack.sort3);;
QCheck.Test.check_exn (test_stability NTRStack.sortN);;
QCheck.Test.check_exn (test_stability NTRStack.sort3N);;
QCheck.Test.check_exn (test_stability TRMCCount.sort3);;
QCheck.Test.check_exn (test_stability TRMCCount.sortN);;
QCheck.Test.check_exn (test_stability TRMCCount.sort3N);;
QCheck.Test.check_exn (test_stability TRMCStack.sort3);;
QCheck.Test.check_exn (test_stability TRMCStack.sortN);;
QCheck.Test.check_exn (test_stability TRMCStack.sort3N);;
QCheck.Test.check_exn (test_stability TRCount.sort3);;
QCheck.Test.check_exn (test_stability TRCount.sortN);;
QCheck.Test.check_exn (test_stability TRCount.sort3N);;
QCheck.Test.check_exn (test_stability TRStack.sort3);;
QCheck.Test.check_exn (test_stability TRStack.sortN);;
QCheck.Test.check_exn (test_stability TRStack.sort3N);;
