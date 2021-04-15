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
  let time_list = ref [] in
  for i = 1 to n do
    let (time, _) = with_timer f in time_list := time :: !time_list
  done;
  median !time_list
;;

let gen_list seed elems =
  Random.init seed; List.init elems (fun _ -> Random.int elems)
;;

let benchmark
    (size : int list) (config : (string * (int list -> int list)) list) =
  let res = ref (List.map (fun _ -> []) config) in
  List.iter (fun (seed, size) ->
      let input = gen_list seed size in
      let r =
        List.map (fun (name, sort) ->
            (name, with_timer_median 5 (fun _ -> sort input))) config
      in
      begin match r with
        | (name1, time1) :: r ->
          Printf.printf "[%9d] %s: %10.6fs" size name1 time1;
          List.iter (fun (name', time') ->
              Printf.printf ", %s: %10.6fs (%+07.2f%%)"
                name' time' ((time' /. time1 -. 1.) *. 100.)
            ) r;
          Printf.printf "\n%!"
        | [] -> raise (Invalid_argument "config should not be empty")
      end;
      res := List.map2 (fun (_, t) ts -> (size, t) :: ts) r !res
    ) (List.map (fun s -> (Random.bits (), s)) size);
  List.iter (fun res ->
      Printf.printf "\\addplot coordinates {";
      List.iter (fun (size, time) -> Printf.printf "(%d, %f) " size time) res;
      Printf.printf "};\n";
    ) !res
;;

benchmark (List.init 100 (fun i -> 10000 * (i + 1)))
  [("List.stable.sort", List.stable_sort (compare : int -> int -> int));
   ("CBN.sort", Mergesort_coq.CBN.sort ((<=) : int -> int -> bool));
   ("CBNOpt.sort", Mergesort_coq.CBNOpt.sort ((<=) : int -> int -> bool));
   ("CBV.sort", Mergesort_coq.CBV.sort ((<=) : int -> int -> bool));
   ("CBVOpt.sort", Mergesort_coq.CBVOpt.sort ((<=) : int -> int -> bool))]
;;
