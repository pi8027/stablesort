open Mergesort_ocaml;;

let test_stability sort =
  QCheck.Test.make ~count:2000 ~name:"sort_stability"
    QCheck.(list (pair small_nat small_nat))
    (fun l ->
       let le_fst x y = fst x <= fst y in
       let cmp_fst x y = compare (fst x) (fst y) in
       sort le_fst l = List.stable_sort cmp_fst l);;

QCheck.Test.check_exn (test_stability NaiveTopDown.sort);;
QCheck.Test.check_exn (test_stability NaiveBottomUp.sort);;
QCheck.Test.check_exn (test_stability TopDown.sort);;
QCheck.Test.check_exn (test_stability BottomUp.sort);;
QCheck.Test.check_exn (test_stability NTRStack.sort3);;
QCheck.Test.check_exn (test_stability NTRStack.sortN);;
QCheck.Test.check_exn (test_stability NTRStack.sort3N);;
QCheck.Test.check_exn (test_stability NTRStack_.sort3);;
QCheck.Test.check_exn (test_stability NTRStack_.sortN);;
QCheck.Test.check_exn (test_stability NTRStack_.sort3N);;
QCheck.Test.check_exn (test_stability TRMCStack.sort3);;
QCheck.Test.check_exn (test_stability TRMCStack.sortN);;
QCheck.Test.check_exn (test_stability TRMCStack.sort3N);;
QCheck.Test.check_exn (test_stability TRMCStack_.sort3);;
QCheck.Test.check_exn (test_stability TRMCStack_.sortN);;
QCheck.Test.check_exn (test_stability TRMCStack_.sort3N);;
QCheck.Test.check_exn (test_stability TRStack.sort3);;
QCheck.Test.check_exn (test_stability TRStack.sortN);;
QCheck.Test.check_exn (test_stability TRStack.sort3N);;
QCheck.Test.check_exn (test_stability TRStack_.sort3);;
QCheck.Test.check_exn (test_stability TRStack_.sortN);;
QCheck.Test.check_exn (test_stability TRStack_.sort3N);;
QCheck.Test.check_exn (test_stability StdlibSort.sort);;
