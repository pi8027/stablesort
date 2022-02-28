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
  let result = List.map (fun (seed, size) ->
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
      (size, List.map (fun (_, t, _) -> t) r, List.map (fun (_, _, m) -> m) r)
    ) (List.map (fun s -> (Random.bits (), s)) size)
  in
  let outc = open_out (filename ^ ".time.csv") in
  Printf.fprintf outc "Size";
  List.iter (fun (name, _) -> Printf.fprintf outc ", %s" name) config;
  Printf.fprintf outc "\n";
  List.iter (fun (size, times, _) ->
      Printf.fprintf outc "%d" size;
      List.iter (Printf.fprintf outc ", %f") times;
      Printf.fprintf outc "\n") result;
  close_out outc;
  let outc = open_out (filename ^ ".mem.csv") in
  Printf.fprintf outc "Size";
  List.iter (fun (name, _) -> Printf.fprintf outc ", %s" name) config;
  Printf.fprintf outc "\n";
  List.iter (fun (size, _, mems) ->
      Printf.fprintf outc "%d" size;
      List.iter (Printf.fprintf outc ", %f") mems;
      Printf.fprintf outc "\n") result;
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
