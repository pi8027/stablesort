Random.self_init ();;

let with_timer f =
  Gc.compact ();
  let t = Unix.gettimeofday () in
  let v = f () in
  (Unix.gettimeofday () -. t, v)
;;

let median (xs : float list) : float =
  let sorted = List.sort compare xs in
  if List.length sorted mod 2 = 1
    then List.nth sorted (List.length sorted / 2)
    else (List.nth sorted (List.length sorted / 2 - 1) +.
          List.nth sorted (List.length sorted / 2)) /. 2.
;;

let with_timer_median n f =
  let (time1, r) = with_timer f in
  let time_list = ref [time1] in
  for i = 1 to n - 1 do
    let (time, _) = with_timer f in time_list := time :: !time_list
  done;
  median !time_list
;;

let gen_list s elems =
  let rec glrec n acc =
    if n = 0 then
      List.rev acc
    else
      let x = Random.int elems in glrec (n - 1) (x :: acc)
  in
  Random.init s; glrec elems []
;;

let i_max = 100 in
let j_max = 1 in
let seeds = Array.init (i_max * j_max) (fun _ -> Random.bits ()) in
for i_ = 0 to i_max - 1 do
  let i = (i_ + 1) * 1000000 in
  for j = 0 to j_max - 1 do
    let benchmark (test : int -> int list -> int list) =
      let input = gen_list (seeds.(i_ * j_max + j)) i in
      with_timer_median 5 (fun _ -> test i input) in
    let time1 = benchmark (fun n xs -> List.stable_sort compare xs) in
    let time2 = benchmark (fun n xs -> Mergesort_coq.CBV.sort (<=) xs) in
    let time3 = benchmark (fun n xs -> Mergesort_coq.CBVOpt.sort (<=) xs) in
    Printf.printf
      "[%9d, %d] List.stable_sort: %10.6fs, \
                 CBV.sort: %10.6fs (%+06.2f%%), \
                 CBVOpt.sort: %10.6fs (%+06.2f%%)\n%!"
      i j time1
      time2 ((time2 /. time1 -. 1.) *. 100.)
      time3 ((time3 /. time1 -. 1.) *. 100.)
  done
done
;;
