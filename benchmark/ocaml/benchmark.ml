Random.self_init ();;
Gc.set { (Gc.get()) with Gc.minor_heap_size = 512 * 1024 * 1024 };;

let with_timer f =
  Gc.compact ();
  Gc.set { (Gc.get()) with Gc.verbose = 0x01f };
  let s1 = Gc.quick_stat () in
  let t1 = Unix.gettimeofday () in
  let v = f () in
  let t2 = Unix.gettimeofday () in
  let s2 = Gc.quick_stat () in
  Gc.set { (Gc.get()) with Gc.verbose = 0x000 };
  let mem_words =
    (s2.Gc.minor_words +. s2.Gc.major_words -. s2.Gc.promoted_words) -.
    (s1.Gc.minor_words +. s1.Gc.major_words -. s1.Gc.promoted_words)
  in
  (t2 -. t1, mem_words /. (128.0 *. 1024.0), v)
;;

let median (xs : float list) : float =
  let sorted = List.sort compare xs in
  if List.length sorted mod 2 = 1
    then List.nth sorted (List.length sorted / 2)
    else (List.nth sorted (List.length sorted / 2 - 1) +.
          List.nth sorted (List.length sorted / 2)) /. 2.
;;

let with_timer_median n f =
  let time_list = ref [] in
  let mem_list = ref [] in
  for i = 1 to n do
    let (time, mem, _) = with_timer f in
    time_list := time :: !time_list;
    mem_list := mem :: !mem_list
  done;
  (median !time_list, median !mem_list)
;;

let gen_list seed elems =
  Random.init seed; List.init elems (fun _ -> Random.int elems)
;;

let benchmark
    (filename : string) (size : int list) (preproc : int list -> int list)
    (config : (string * (int list -> int list)) list) =
  let times = ref (List.map (fun _ -> []) config) in
  let mems = ref (List.map (fun _ -> []) config) in
  List.iter (fun (seed, size) ->
      let input = preproc (gen_list seed size) in
      let r =
        List.map (fun (name, sort) ->
            let (time, mem) = with_timer_median 5 (fun _ -> sort input) in
            (name, time, mem)) config
      in
      Printf.printf "size: %7d" size;
      List.iter (fun (name, time, mem) ->
          Printf.printf "; %s: %8.6fs, %10.6fMB" name time mem
        ) r;
      Printf.printf "\n%!";
      times := List.map2 (fun (_, t, _) ts -> (size, t) :: ts) r !times;
      mems := List.map2 (fun (_, _, m) ms -> (size, m) :: ms) r !mems
    ) (List.map (fun s -> (Random.bits (), s)) size);
  let outc = open_out (filename ^ ".time.out") in
  Printf.fprintf outc "%% time consumption\n";
  List.iter2 (fun res (name, _) ->
      Printf.fprintf outc "\\addplot coordinates {";
      List.iter (fun (size, time) -> Printf.fprintf outc "(%d, %f) " size time)
        (List.rev res);
      Printf.fprintf outc "}; %% %s\n" name;
    ) !times config;
  close_out outc;
  let outc = open_out (filename ^ ".mem.out") in
  Printf.fprintf outc "%% memory consumption\n";
  List.iter2 (fun res (name, _) ->
      Printf.fprintf outc "\\addplot coordinates {";
      List.iter (fun (size, time) -> Printf.fprintf outc "(%d, %f) " size time)
        (List.rev res);
      Printf.fprintf outc "}; %% %s\n" name;
    ) !mems config;
  close_out outc
;;

let split_n n xs =
  let rec aux i xs acc =
    match i, xs with
      | 0, _ | _, [] -> (List.rev acc, xs)
      | i, x :: xs -> aux (i - 1) xs (x :: acc)
  in aux n xs []
;;

let rec sort_blocks (n : int) = function
  | [] -> []
  | xs ->
    let (xs1, xs2) = split_n n xs in
    List.append (List.sort compare xs1) (sort_blocks n xs2)
;;

benchmark "ocaml1" (List.init 40 (fun i -> 25000 * (i + 1))) (fun xs -> xs)
  [("List.stable.sort",   List.stable_sort               (compare : int -> int -> int));
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

benchmark "ocaml2" (List.init 40 (fun i -> 25000 * (i + 1))) (sort_blocks 50)
  [("List.stable.sort",   List.stable_sort               (compare : int -> int -> int));
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
