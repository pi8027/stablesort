open List

let rec split_n s n =
  match s with
  | x :: s when 0 < n ->
    let (s1, s2) = split_n s (n - 1) in (x :: s1, s2)
  | _ -> ([], s)

(* Non-tail-recursive merge *)
module NTRMerge = struct

let rec merge (<=) xs ys =
  match xs, ys with
  | [], ys -> ys
  | xs, [] -> xs
  | x :: xs', y :: ys' ->
    if x <= y then
      x :: merge (<=) xs' ys
    else
      y :: merge (<=) xs ys'

end;;

(* Tail-recursive-modulo-cons merge *)
module TRMCMerge = struct

let[@tail_mod_cons] rec merge (<=) xs ys =
  match xs, ys with
  | [], _ -> ys
  | _, [] -> xs
  | x :: xs', y :: ys' ->
    if x <= y
    then x :: merge (<=) xs' ys
    else y :: merge (<=) xs ys'

end;;

(* Tail-recursive merge *)
module TRMerge = struct

let rec rev_merge (<=) xs ys accu =
  match xs, ys with
  | [], _ -> rev_append ys accu
  | _, [] -> rev_append xs accu
  | x :: xs', y :: ys' ->
    if x <= y
    then rev_merge (<=) xs' ys (x :: accu)
    else rev_merge (<=) xs ys' (y :: accu)

let rec rev_merge_rev (<=) xs ys accu =
  match xs, ys with
  | [], _ -> rev_append ys accu
  | _, [] -> rev_append xs accu
  | x :: xs', y :: ys' ->
    if y <= x
    then rev_merge_rev (<=) xs' ys (x :: accu)
    else rev_merge_rev (<=) xs ys' (y :: accu)

end;;

module NaiveTopDown = struct

open NTRMerge

let rec sort (<=) = function
  | [] -> []
  | [x] -> [x]
  | xs ->
    let k = length xs / 2 in
    let (xs1, xs2) = split_n xs k in
    merge (<=) (sort (<=) xs1) (sort (<=) xs2)

end;;

module NaiveBottomUp = struct

open NTRMerge

let sort (<=) xs =
  let rec merge_pairs = function
    | a :: b :: xs ->
      merge (<=) a b :: merge_pairs xs
    | xs -> xs in
  let rec merge_all = function
    | [] -> []
    | [x] -> x
    | xs -> merge_all (merge_pairs xs)
  in
  merge_all (map (fun x -> [x]) xs)

end;;

module TopDown = struct

open NTRMerge

let rec sort_rec (<=) n xs =
  match n, xs with
  | 1, x :: xs -> ([x], xs)
  | _, _ ->
    let n1 = n / 2 in
    let n2 = n - n1 in
    let s1, xs1 = sort_rec (<=) n1 xs in
    let s2, xs2 = sort_rec (<=) n2 xs1 in
    (merge (<=) s1 s2, xs2)

let sort (<=) = function
  | [] -> []
  | xs -> fst (sort_rec (<=) (length xs) xs)

end;;

module BottomUp = struct

open NTRMerge

let rec push (<=) xs k stack =
  match k mod 2, stack with
  | 0, _ -> xs :: stack
  | 1, ys :: stack -> push (<=) (merge (<=) ys xs) (k / 2) stack

let rec pop (<=) xs = function
  | [] -> xs
  | ys :: stack -> pop (<=) (merge (<=) ys xs) stack

let rec sort_rec (<=) k stack = function
  | x :: s -> sort_rec (<=) (k + 1) (push (<=) [x] k stack) s
  | [] -> pop (<=) [] stack

let sort (<=) s = sort_rec (<=) 0 [] s

end;;

(* Stack-based bottom-up non-tail-recursive mergesorts *)
module NTRStack = struct

open NTRMerge

let rec push (<=) xs k stack =
  match k land 1, stack with
  | 0, _ -> xs :: stack
  | 1, ys :: stack -> push (<=) (merge (<=) ys xs) (k lsr 1) stack

let rec pop (<=) xs = function
  | [] -> xs
  | ys :: stack -> pop (<=) (merge (<=) ys xs) stack

let rec sort3rec (<=) k stack = function
  | x :: y :: z :: s ->
    let xyz =
      if x <= y then
        if y <= z then [x; y; z] else if x <= z then [x; z; y] else [z; x; y]
      else
        if x <= z then [y; x; z] else if y <= z then [y; z; x] else [z; y; x]
    in
    sort3rec (<=) (k + 1) (push (<=) xyz k stack) s
  | [x; y] as s -> pop (<=) (if x <= y then s else [y; x]) stack
  | s -> pop (<=) s stack

let sort3 (<=) s = sort3rec (<=) 0 [] s

let rec sortNrec (<=) k stack s =
  let rec ascending accu x s =
    let accu = x :: accu in
    match s with
    | [] -> pop (<=) (rev accu) stack
    | y :: s when x <= y -> ascending accu y s
    | _ -> sortNrec (<=) (k + 1) (push (<=) (rev accu) k stack) s
  in
  let rec descending accu x s =
    let accu = x :: accu in
    match s with
    | [] -> pop (<=) accu stack
    | y :: s when not (x <= y) -> descending accu y s
    | _ -> sortNrec (<=) (k + 1) (push (<=) accu k stack) s
  in
  match s with
  | x :: y :: s ->
    if x <= y then ascending [x] y s else descending [x] y s
  | _ -> pop (<=) s stack

let sortN (<=) s = sortNrec (<=) 0 [] s

let rec sort3Nrec (<=) k stack s =
  let rec ascending accu x s =
    let accu = x :: accu in
    match s with
    | [] -> pop (<=) (rev accu) stack
    | y :: s when x <= y -> ascending accu y s
    | _ -> sort3Nrec (<=) (k + 1) (push (<=) (rev accu) k stack) s
  in
  let rec descending accu x s =
    let accu = x :: accu in
    match s with
    | [] -> pop (<=) accu stack
    | y :: s when not (x <= y) -> descending accu y s
    | _ -> sort3Nrec (<=) (k + 1) (push (<=) accu k stack) s
  in
  match s with
  | x :: y :: z :: s ->
    begin match x <= y, y <= z with
    | true,  true  -> ascending [y; x] z s
    | false, false -> descending [y; x] z s
    | true,  false ->
      let xyz = if x <= z then [x; z; y] else [z; x; y] in
      sort3Nrec (<=) (k + 1) (push (<=) xyz k stack) s
    | false, true  ->
      let xyz = if x <= z then [y; x; z] else [y; z; x] in
      sort3Nrec (<=) (k + 1) (push (<=) xyz k stack) s
    end
  | [x; y] -> pop (<=) (if x <= y then [x; y] else [y; x]) stack
  | _ -> pop (<=) s stack

let sort3N (<=) s = sort3Nrec (<=) 0 [] s

end;;

(* Stack-based bottom-up non-tail-recursive mergesorts without the counter *)
module NTRStack_ = struct

open NTRMerge

let rec push (<=) xs = function
  | [] :: stack | ([] as stack) -> xs :: stack
  | ys :: stack -> [] :: push (<=) (merge (<=) ys xs) stack

let rec pop (<=) xs = function
  | [] -> xs
  | ys :: stack -> pop (<=) (merge (<=) ys xs) stack

let rec sort3rec (<=) stack = function
  | x :: y :: z :: s ->
    let xyz =
      if x <= y then
        if y <= z then [x; y; z] else if x <= z then [x; z; y] else [z; x; y]
      else
        if x <= z then [y; x; z] else if y <= z then [y; z; x] else [z; y; x]
    in
    sort3rec (<=) (push (<=) xyz stack) s
  | [x; y] as s -> pop (<=) (if x <= y then s else [y; x]) stack
  | s -> pop (<=) s stack

let sort3 (<=) s = sort3rec (<=) [] s

let rec sortNrec (<=) stack s =
  let rec ascending accu x s =
    let accu = x :: accu in
    match s with
    | [] -> pop (<=) (rev accu) stack
    | y :: s when x <= y -> ascending accu y s
    | _ -> sortNrec (<=) (push (<=) (rev accu) stack) s
  in
  let rec descending accu x s =
    let accu = x :: accu in
    match s with
    | [] -> pop (<=) accu stack
    | y :: s when not (x <= y) -> descending accu y s
    | _ -> sortNrec (<=) (push (<=) accu stack) s
  in
  match s with
  | x :: y :: s ->
    if x <= y then ascending [x] y s else descending [x] y s
  | _ -> pop (<=) s stack

let sortN (<=) s = sortNrec (<=) [] s

let rec sort3Nrec (<=) stack s =
  let rec ascending accu x s =
    let accu = x :: accu in
    match s with
    | [] -> pop (<=) (rev accu) stack
    | y :: s when x <= y -> ascending accu y s
    | _ -> sort3Nrec (<=) (push (<=) (rev accu) stack) s
  in
  let rec descending accu x s =
    let accu = x :: accu in
    match s with
    | [] -> pop (<=) accu stack
    | y :: s when not (x <= y) -> descending accu y s
    | _ -> sort3Nrec (<=) (push (<=) accu stack) s
  in
  match s with
  | x :: y :: z :: s ->
    begin match x <= y, y <= z with
    | true,  true  -> ascending [y; x] z s
    | false, false -> descending [y; x] z s
    | true,  false ->
      let xyz = if x <= z then [x; z; y] else [z; x; y] in
      sort3Nrec (<=) (push (<=) xyz stack) s
    | false, true  ->
      let xyz = if x <= z then [y; x; z] else [y; z; x] in
      sort3Nrec (<=) (push (<=) xyz stack) s
    end
  | [x; y] -> pop (<=) (if x <= y then [x; y] else [y; x]) stack
  | _ -> pop (<=) s stack

let sort3N (<=) s = sort3Nrec (<=) [] s

end;;

(* Stack-based bottom-up tail-recursive-modulo-cons mergesorts *)
module TRMCStack = struct

open TRMCMerge

let rec push (<=) xs k stack =
  match k land 1, stack with
  | 0, _ -> xs :: stack
  | 1, ys :: stack -> push (<=) (merge (<=) ys xs) (k lsr 1) stack

let rec pop (<=) xs = function
  | [] -> xs
  | ys :: stack -> pop (<=) (merge (<=) ys xs) stack

let rec sort3rec (<=) k stack = function
  | x :: y :: z :: s ->
    let xyz =
      if x <= y then
        if y <= z then [x; y; z] else if x <= z then [x; z; y] else [z; x; y]
      else
        if x <= z then [y; x; z] else if y <= z then [y; z; x] else [z; y; x]
    in
    sort3rec (<=) (k + 1) (push (<=) xyz k stack) s
  | [x; y] as s -> pop (<=) (if x <= y then s else [y; x]) stack
  | s -> pop (<=) s stack

let sort3 (<=) s = sort3rec (<=) 0 [] s

let rec sortNrec (<=) k stack s =
  let rec ascending accu x s =
    let accu = x :: accu in
    match s with
    | [] -> pop (<=) (rev accu) stack
    | y :: s when x <= y -> ascending accu y s
    | _ -> sortNrec (<=) (k + 1) (push (<=) (rev accu) k stack) s
  in
  let rec descending accu x s =
    let accu = x :: accu in
    match s with
    | [] -> pop (<=) accu stack
    | y :: s when not (x <= y) -> descending accu y s
    | _ -> sortNrec (<=) (k + 1) (push (<=) accu k stack) s
  in
  match s with
  | x :: y :: s ->
    if x <= y then ascending [x] y s else descending [x] y s
  | _ -> pop (<=) s stack

let sortN (<=) s = sortNrec (<=) 0 [] s

let rec sort3Nrec (<=) k stack s =
  let rec ascending accu x s =
    let accu = x :: accu in
    match s with
    | [] -> pop (<=) (rev accu) stack
    | y :: s when x <= y -> ascending accu y s
    | _ -> sort3Nrec (<=) (k + 1) (push (<=) (rev accu) k stack) s
  in
  let rec descending accu x s =
    let accu = x :: accu in
    match s with
    | [] -> pop (<=) accu stack
    | y :: s when not (x <= y) -> descending accu y s
    | _ -> sort3Nrec (<=) (k + 1) (push (<=) accu k stack) s
  in
  match s with
  | x :: y :: z :: s ->
    begin match x <= y, y <= z with
    | true,  true  -> ascending [y; x] z s
    | false, false -> descending [y; x] z s
    | true,  false ->
      let xyz = if x <= z then [x; z; y] else [z; x; y] in
      sort3Nrec (<=) (k + 1) (push (<=) xyz k stack) s
    | false, true  ->
      let xyz = if x <= z then [y; x; z] else [y; z; x] in
      sort3Nrec (<=) (k + 1) (push (<=) xyz k stack) s
    end
  | [x; y] -> pop (<=) (if x <= y then [x; y] else [y; x]) stack
  | _ -> pop (<=) s stack

let sort3N (<=) s = sort3Nrec (<=) 0 [] s

end;;

(* Stack-based bottom-up tail-recursive-modulo-cons mergesorts without the    *)
(* counter                                                                    *)
module TRMCStack_ = struct

open TRMCMerge

let rec push (<=) xs = function
  | [] :: stack | ([] as stack) -> xs :: stack
  | ys :: stack -> [] :: push (<=) (merge (<=) ys xs) stack

let rec pop (<=) xs = function
  | [] -> xs
  | ys :: stack -> pop (<=) (merge (<=) ys xs) stack

let rec sort3rec (<=) stack = function
  | x :: y :: z :: s ->
    let xyz =
      if x <= y then
        if y <= z then [x; y; z] else if x <= z then [x; z; y] else [z; x; y]
      else
        if x <= z then [y; x; z] else if y <= z then [y; z; x] else [z; y; x]
    in
    sort3rec (<=) (push (<=) xyz stack) s
  | [x; y] as s -> pop (<=) (if x <= y then s else [y; x]) stack
  | s -> pop (<=) s stack

let sort3 (<=) s = sort3rec (<=) [] s

let rec sortNrec (<=) stack s =
  let rec ascending accu x s =
    let accu = x :: accu in
    match s with
    | [] -> pop (<=) (rev accu) stack
    | y :: s when x <= y -> ascending accu y s
    | _ -> sortNrec (<=) (push (<=) (rev accu) stack) s
  in
  let rec descending accu x s =
    let accu = x :: accu in
    match s with
    | [] -> pop (<=) accu stack
    | y :: s when not (x <= y) -> descending accu y s
    | _ -> sortNrec (<=) (push (<=) accu stack) s
  in
  match s with
  | x :: y :: s ->
    if x <= y then ascending [x] y s else descending [x] y s
  | _ -> pop (<=) s stack

let sortN (<=) s = sortNrec (<=) [] s

let rec sort3Nrec (<=) stack s =
  let rec ascending accu x s =
    let accu = x :: accu in
    match s with
    | [] -> pop (<=) (rev accu) stack
    | y :: s when x <= y -> ascending accu y s
    | _ -> sort3Nrec (<=) (push (<=) (rev accu) stack) s
  in
  let rec descending accu x s =
    let accu = x :: accu in
    match s with
    | [] -> pop (<=) accu stack
    | y :: s when not (x <= y) -> descending accu y s
    | _ -> sort3Nrec (<=) (push (<=) accu stack) s
  in
  match s with
  | x :: y :: z :: s ->
    begin match x <= y, y <= z with
    | true,  true  -> ascending [y; x] z s
    | false, false -> descending [y; x] z s
    | true,  false ->
      let xyz = if x <= z then [x; z; y] else [z; x; y] in
      sort3Nrec (<=) (push (<=) xyz stack) s
    | false, true  ->
      let xyz = if x <= z then [y; x; z] else [y; z; x] in
      sort3Nrec (<=) (push (<=) xyz stack) s
    end
  | [x; y] -> pop (<=) (if x <= y then [x; y] else [y; x]) stack
  | _ -> pop (<=) s stack

let sort3N (<=) s = sort3Nrec (<=) [] s

end;;

(* Stack-based bottom-up tail-recursive mergesorts *)
module TRStack = struct

open TRMerge

let rec push (<=) xs k stack =
  match k land 3, stack with
  | 0, _ | 2, _ -> xs :: stack
  | 1, ys :: stack -> rev_merge (<=) ys xs [] :: stack
  | 3, ys :: zs :: stack ->
    push (<=) (rev_merge_rev (<=) (rev_merge (<=) ys xs []) zs [])
      (k lsr 2) stack

let rec pop (<=) xs k stack =
  match k land 3, stack with
  | _, [] -> xs
  | 0, _ -> pop (<=) xs (k lsr 2) stack
  | 2, _ -> pop_rev (<=) (rev xs) (k lsr 1) stack
  | 1, ys :: stack | 3, ys :: stack ->
    pop_rev (<=) (rev_merge (<=) ys xs []) (k lsr 1) stack
and pop_rev (<=) xs k stack =
  match k land 3, stack with
  | _, [] -> rev xs
  | 0, _ -> pop_rev (<=) xs (k lsr 2) stack
  | 2, _ -> pop (<=) (rev xs) (k lsr 1) stack
  | 1, ys :: stack | 3, ys :: stack ->
    pop (<=) (rev_merge_rev (<=) xs ys []) (k lsr 1) stack

let rec sort3rec (<=) k stack = function
  | x :: y :: z :: s ->
    let xyz =
      if x <= y then
        if y <= z then [x; y; z] else if x <= z then [x; z; y] else [z; x; y]
      else
        if x <= z then [y; x; z] else if y <= z then [y; z; x] else [z; y; x]
    in
    sort3rec (<=) (k + 1) (push (<=) xyz k stack) s
  | [x; y] as s -> pop (<=) (if x <= y then s else [y; x]) k stack
  | s -> pop (<=) s k stack

let sort3 (<=) s = sort3rec (<=) 0 [] s

let rec sortNrec (<=) k stack s =
  let rec ascending accu x s =
    let accu = x :: accu in
    match s with
    | [] -> pop (<=) (rev accu) k stack
    | y :: s when x <= y -> ascending accu y s
    | _ -> sortNrec (<=) (k + 1) (push (<=) (rev accu) k stack) s
  in
  let rec descending accu x s =
    let accu = x :: accu in
    match s with
    | [] -> pop (<=) accu k stack
    | y :: s when not (x <= y) -> descending accu y s
    | _ -> sortNrec (<=) (k + 1) (push (<=) accu k stack) s
  in
  match s with
  | x :: y :: s ->
    if x <= y then ascending [x] y s else descending [x] y s
  | _ -> pop (<=) s k stack

let sortN (<=) s = sortNrec (<=) 0 [] s

let rec sort3Nrec (<=) k stack s =
  let rec ascending accu x s =
    let accu = x :: accu in
    match s with
    | [] -> pop (<=) (rev accu) k stack
    | y :: s when x <= y -> ascending accu y s
    | _ -> sort3Nrec (<=) (k + 1) (push (<=) (rev accu) k stack) s
  in
  let rec descending accu x s =
    let accu = x :: accu in
    match s with
    | [] -> pop (<=) accu k stack
    | y :: s when not (x <= y) -> descending accu y s
    | _ -> sort3Nrec (<=) (k + 1) (push (<=) accu k stack) s
  in
  match s with
  | x :: y :: z :: s ->
    begin match x <= y, y <= z with
    | true,  true  -> ascending [y; x] z s
    | false, false -> descending [y; x] z s
    | true,  false ->
      let xyz = if x <= z then [x; z; y] else [z; x; y] in
      sort3Nrec (<=) (k + 1) (push (<=) xyz k stack) s
    | false, true ->
      let xyz = if x <= z then [y; x; z] else [y; z; x] in
      sort3Nrec (<=) (k + 1) (push (<=) xyz k stack) s
    end
  | [x; y] -> pop (<=) (if x <= y then [x; y] else [y; x]) k stack
  | _ -> pop (<=) s k stack

let sort3N (<=) s = sort3Nrec (<=) 0 [] s

end;;

(* Stack-based bottom-up tail-recursive mergesorts without the counter *)
module TRStack_ = struct

open TRMerge

let rec push (<=) xs = function
  | [] :: stack | ([] as stack) -> xs :: stack
  | ys :: [] :: stack | ys :: ([] as stack) ->
    [] :: rev_merge (<=) ys xs [] :: stack
  | ys :: zs :: stack ->
    [] :: [] :: push (<=)
      (rev_merge_rev (<=) (rev_merge (<=) ys xs []) zs []) stack

let rec pop (<=) xs = function
  | [] -> xs
  | [] :: [] :: stack -> pop (<=) xs stack
  | [] :: stack -> pop_rev (<=) (rev xs) stack
  | ys :: stack -> pop_rev (<=) (rev_merge (<=) ys xs []) stack
and pop_rev (<=) xs = function
  | [] -> rev xs
  | [] :: [] :: stack -> pop_rev (<=) xs stack
  | [] :: stack -> pop (<=) (rev xs) stack
  | ys :: stack -> pop (<=) (rev_merge_rev (<=) xs ys []) stack

let rec sort3rec (<=) stack = function
  | x :: y :: z :: s ->
    let xyz =
      if x <= y then
        if y <= z then [x; y; z] else if x <= z then [x; z; y] else [z; x; y]
      else
        if x <= z then [y; x; z] else if y <= z then [y; z; x] else [z; y; x]
    in
    sort3rec (<=) (push (<=) xyz stack) s
  | [x; y] as s -> pop (<=) (if x <= y then s else [y; x]) stack
  | s -> pop (<=) s stack

let sort3 (<=) s = sort3rec (<=) [] s

let rec sortNrec (<=) stack s =
  let rec ascending accu x s =
    let accu = x :: accu in
    match s with
    | [] -> pop (<=) (rev accu) stack
    | y :: s when x <= y -> ascending accu y s
    | _ -> sortNrec (<=) (push (<=) (rev accu) stack) s
  in
  let rec descending accu x s =
    let accu = x :: accu in
    match s with
    | [] -> pop (<=) accu stack
    | y :: s when not (x <= y) -> descending accu y s
    | _ -> sortNrec (<=) (push (<=) accu stack) s
  in
  match s with
  | x :: y :: s ->
    if x <= y then ascending [x] y s else descending [x] y s
  | _ -> pop (<=) s stack

let sortN (<=) s = sortNrec (<=) [] s

let rec sort3Nrec (<=) stack s =
  let rec ascending accu x s =
    let accu = x :: accu in
    match s with
    | [] -> pop (<=) (rev accu) stack
    | y :: s when x <= y -> ascending accu y s
    | _ -> sort3Nrec (<=) (push (<=) (rev accu) stack) s
  in
  let rec descending accu x s =
    let accu = x :: accu in
    match s with
    | [] -> pop (<=) accu stack
    | y :: s when not (x <= y) -> descending accu y s
    | _ -> sort3Nrec (<=) (push (<=) accu stack) s
  in
  match s with
  | x :: y :: z :: s ->
    begin match x <= y, y <= z with
    | true,  true  -> ascending [y; x] z s
    | false, false -> descending [y; x] z s
    | true,  false ->
      let xyz = if x <= z then [x; z; y] else [z; x; y] in
      sort3Nrec (<=) (push (<=) xyz stack) s
    | false, true ->
      let xyz = if x <= z then [y; x; z] else [y; z; x] in
      sort3Nrec (<=) (push (<=) xyz stack) s
    end
  | [x; y] -> pop (<=) (if x <= y then [x; y] else [y; x]) stack
  | _ -> pop (<=) s stack

let sort3N (<=) s = sort3Nrec (<=) [] s

end;;

(* A copy of List.stable_sort from the standard library of OCaml, slightly    *)
(* modified to take (<=) of type ['a -> 'a -> bool] instead of [cmp] of type  *)
(* ['a -> 'a -> int]                                                          *)
module StdlibSort = struct

open TRMerge

let sort (<=) l =
  let rec rev_merge l1 l2 accu =
    match l1, l2 with
    | [], l2 -> rev_append l2 accu
    | l1, [] -> rev_append l1 accu
    | h1::t1, h2::t2 ->
        if h1 <= h2
        then rev_merge t1 l2 (h1::accu)
        else rev_merge l1 t2 (h2::accu)
  in
  let rec rev_merge_rev l1 l2 accu =
    match l1, l2 with
    | [], l2 -> rev_append l2 accu
    | l1, [] -> rev_append l1 accu
    | h1::t1, h2::t2 ->
        if h1 <= h2
        then rev_merge_rev l1 t2 (h2::accu)
        else rev_merge_rev t1 l2 (h1::accu)
  in
  let rec sort n l =
    match n, l with
    | 2, x1 :: x2 :: tl ->
      let s = if x1 <= x2 then [x1; x2] else [x2; x1] in
      (s, tl)
    | 3, x1 :: x2 :: x3 :: tl ->
      let s =
        if x1 <= x2 then
          if x2 <= x3 then [x1; x2; x3]
          else if x1 <= x3 then [x1; x3; x2]
          else [x3; x1; x2]
        else if x1 <= x3 then [x2; x1; x3]
        else if x2 <= x3 then [x2; x3; x1]
        else [x3; x2; x1]
      in
      (s, tl)
    | n, l ->
      let n1 = n asr 1 in
      let n2 = n - n1 in
      let s1, l2 = rev_sort n1 l in
      let s2, tl = rev_sort n2 l2 in
      (rev_merge_rev s1 s2 [], tl)
  and rev_sort n l =
    match n, l with
    | 2, x1 :: x2 :: tl ->
      let s = if x1 <= x2 then [x2; x1] else [x1; x2] in
      (s, tl)
    | 3, x1 :: x2 :: x3 :: tl ->
      let s =
        if x1 <= x2 then
          if x1 <= x3 then
            if x2 <= x3 then [x3; x2; x1] else [x2; x3; x1]
          else [x2; x1; x3]
        else
          if x2 <= x3 then
            if x1 <= x3 then [x3; x1; x2] else [x1; x3; x2]
          else [x1; x2; x3]
      in
      (s, tl)
    | n, l ->
      let n1 = n asr 1 in
      let n2 = n - n1 in
      let s1, l2 = sort n1 l in
      let s2, tl = sort n2 l2 in
      (rev_merge s1 s2 [], tl)
  in
  let len = length l in
  if len < 2 then l else fst (sort len l)

end;;
