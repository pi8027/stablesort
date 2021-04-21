Random.self_init ();;
Gc.set { (Gc.get()) with Gc.minor_heap_size = 128 * 1024 * 1024 };;

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
    (size : int list) (config : (string * (int list -> int list)) list) =
  let times = ref (List.map (fun _ -> []) config) in
  let mems = ref (List.map (fun _ -> []) config) in
  List.iter (fun (seed, size) ->
      let input = gen_list seed size in
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
  Printf.printf "%% time consumption\n";
  List.iter (fun res ->
      Printf.printf "\\addplot coordinates {";
      List.iter (fun (size, time) -> Printf.printf "(%d, %f) " size time)
        (List.rev res);
      Printf.printf "};\n";
    ) !times;
  Printf.printf "%% memory consumption\n";
  List.iter (fun res ->
      Printf.printf "\\addplot coordinates {";
      List.iter (fun (size, time) -> Printf.printf "(%d, %f) " size time)
        (List.rev res);
      Printf.printf "};\n";
    ) !mems
;;

benchmark (List.init 50 (fun i -> 10000 * (i + 1)))
  [("List.stable.sort", List.stable_sort (compare : int -> int -> int));
   ("CBN.sort", Mergesort_coq.CBN.sort ((<=) : int -> int -> bool));
   ("CBNOpt.sort", Mergesort_coq.CBNOpt.sort ((<=) : int -> int -> bool));
   ("CBV.sort", Mergesort_coq.CBV.sort ((<=) : int -> int -> bool));
   ("CBVOpt.sort", Mergesort_coq.CBVOpt.sort ((<=) : int -> int -> bool))]
;;
