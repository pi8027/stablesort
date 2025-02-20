(* Counting-based bottom-up non-tail-recursive mergesorts *)
module NTRCount = struct

  let rec merge cmp xs ys =
    match xs, ys with
    | [], _ -> ys
    | _, [] -> xs
    | x :: xs', y :: ys' ->
      if cmp x y <= 0
      then x :: merge cmp xs' ys
      else y :: merge cmp xs ys'

  let rec push cmp xs k stack =
    match k land 1, stack with
    | 0, _ -> xs :: stack
    | 1, ys :: stack -> push cmp (merge cmp ys xs) (k lsr 1) stack

  let rec pop cmp xs = function
    | [] -> xs
    | ys :: stack -> pop cmp (merge cmp ys xs) stack

  let rec sortN_rec cmp k stack s =
    let rec ascending accu x s =
      let accu = x :: accu in
      match s with
      | [] -> pop cmp (List.rev accu) stack
      | y :: s when cmp x y <= 0 -> ascending accu y s
      | _ -> sortN_rec cmp (k + 1) (push cmp (List.rev accu) k stack) s
    in
    let rec descending accu x s =
      let accu = x :: accu in
      match s with
      | [] -> pop cmp accu stack
      | y :: s when cmp x y > 0 -> descending accu y s
      | _ -> sortN_rec cmp (k + 1) (push cmp accu k stack) s
    in
    match s with
    | x :: y :: s ->
      if cmp x y <= 0 then ascending [x] y s else descending [x] y s
    | _ -> pop cmp s stack

  let sortN cmp s = sortN_rec cmp 0 [] s

  let rec sort3N_rec cmp k stack s =
    let rec ascending accu x s =
      let accu = x :: accu in
      match s with
      | [] -> pop cmp (List.rev accu) stack
      | y :: s when cmp x y <= 0 -> ascending accu y s
      | _ -> sort3N_rec cmp (k + 1) (push cmp (List.rev accu) k stack) s
    in
    let rec descending accu x s =
      let accu = x :: accu in
      match s with
      | [] -> pop cmp accu stack
      | y :: s when cmp x y > 0 -> descending accu y s
      | _ -> sort3N_rec cmp (k + 1) (push cmp accu k stack) s
    in
    match s with
    | x :: y :: z :: s ->
      begin match cmp x y <= 0, cmp y z <= 0 with
      | true,  true  -> ascending [y; x] z s
      | false, false -> descending [y; x] z s
      | true,  false ->
        let xyz = if cmp x z <= 0 then [x; z; y] else [z; x; y] in
        sort3N_rec cmp (k + 1) (push cmp xyz k stack) s
      | false, true  ->
        let xyz = if cmp x z <= 0 then [y; x; z] else [y; z; x] in
        sort3N_rec cmp (k + 1) (push cmp xyz k stack) s
      end
    | [x; y] -> pop cmp (if cmp x y <= 0 then [x; y] else [y; x]) stack
    | _ -> pop cmp s stack

  let sort3N cmp s = sort3N_rec cmp 0 [] s

end;;

(* Stack-based bottom-up non-tail-recursive mergesorts *)
module NTRStack = struct

  let rec merge cmp xs ys =
    match xs, ys with
    | [], _ -> ys
    | _, [] -> xs
    | x :: xs', y :: ys' ->
      if cmp x y <= 0
      then x :: merge cmp xs' ys
      else y :: merge cmp xs ys'

  let rec push cmp xs = function
    | [] :: stack | ([] as stack) -> xs :: stack
    | ys :: stack -> [] :: push cmp (merge cmp ys xs) stack

  let rec pop cmp xs = function
    | [] -> xs
    | ys :: stack -> pop cmp (merge cmp ys xs) stack

  let rec sortN_rec cmp stack s =
    let rec ascending accu x s =
      let accu = x :: accu in
      match s with
      | [] -> pop cmp (List.rev accu) stack
      | y :: s when cmp x y <= 0 -> ascending accu y s
      | _ -> sortN_rec cmp (push cmp (List.rev accu) stack) s
    in
    let rec descending accu x s =
      let accu = x :: accu in
      match s with
      | [] -> pop cmp accu stack
      | y :: s when cmp x y > 0 -> descending accu y s
      | _ -> sortN_rec cmp (push cmp accu stack) s
    in
    match s with
    | x :: y :: s ->
      if cmp x y <= 0 then ascending [x] y s else descending [x] y s
    | _ -> pop cmp s stack

  let sortN cmp s = sortN_rec cmp [] s

  let rec sort3N_rec cmp stack s =
    let rec ascending accu x s =
      let accu = x :: accu in
      match s with
      | [] -> pop cmp (List.rev accu) stack
      | y :: s when cmp x y <= 0 -> ascending accu y s
      | _ -> sort3N_rec cmp (push cmp (List.rev accu) stack) s
    in
    let rec descending accu x s =
      let accu = x :: accu in
      match s with
      | [] -> pop cmp accu stack
      | y :: s when cmp x y > 0 -> descending accu y s
      | _ -> sort3N_rec cmp (push cmp accu stack) s
    in
    match s with
    | x :: y :: z :: s ->
      begin match cmp x y <= 0, cmp y z <= 0 with
      | true,  true  -> ascending [y; x] z s
      | false, false -> descending [y; x] z s
      | true,  false ->
        let xyz = if cmp x z <= 0 then [x; z; y] else [z; x; y] in
        sort3N_rec cmp (push cmp xyz stack) s
      | false, true  ->
        let xyz = if cmp x z <= 0 then [y; x; z] else [y; z; x] in
        sort3N_rec cmp (push cmp xyz stack) s
      end
    | [x; y] -> pop cmp (if cmp x y <= 0 then [x; y] else [y; x]) stack
    | _ -> pop cmp s stack

  let sort3N cmp s = sort3N_rec cmp [] s

end;;

(* Counting-based bottom-up tail-recursive-modulo-cons mergesorts *)
module TRMCCount = struct

  let[@tail_mod_cons] rec merge cmp xs ys =
    match xs, ys with
    | [], _ -> ys
    | _, [] -> xs
    | x :: xs', y :: ys' ->
      if cmp x y <= 0
      then x :: (merge[@tailcall]) cmp xs' ys
      else y :: (merge[@tailcall]) cmp xs ys'

  let rec push cmp xs k stack =
    match k land 1, stack with
    | 0, _ -> xs :: stack
    | 1, ys :: stack -> push cmp (merge cmp ys xs) (k lsr 1) stack

  let rec pop cmp xs = function
    | [] -> xs
    | ys :: stack -> pop cmp (merge cmp ys xs) stack

  let rec sortN_rec cmp k stack s =
    let rec ascending accu x s =
      let accu = x :: accu in
      match s with
      | [] -> pop cmp (List.rev accu) stack
      | y :: s when cmp x y <= 0 -> ascending accu y s
      | _ -> sortN_rec cmp (k + 1) (push cmp (List.rev accu) k stack) s
    in
    let rec descending accu x s =
      let accu = x :: accu in
      match s with
      | [] -> pop cmp accu stack
      | y :: s when cmp x y > 0 -> descending accu y s
      | _ -> sortN_rec cmp (k + 1) (push cmp accu k stack) s
    in
    match s with
    | x :: y :: s ->
      if cmp x y <= 0 then ascending [x] y s else descending [x] y s
    | _ -> pop cmp s stack

  let sortN cmp s = sortN_rec cmp 0 [] s

  let rec sort3N_rec cmp k stack s =
    let rec ascending accu x s =
      let accu = x :: accu in
      match s with
      | [] -> pop cmp (List.rev accu) stack
      | y :: s when cmp x y <= 0 -> ascending accu y s
      | _ -> sort3N_rec cmp (k + 1) (push cmp (List.rev accu) k stack) s
    in
    let rec descending accu x s =
      let accu = x :: accu in
      match s with
      | [] -> pop cmp accu stack
      | y :: s when cmp x y > 0 -> descending accu y s
      | _ -> sort3N_rec cmp (k + 1) (push cmp accu k stack) s
    in
    match s with
    | x :: y :: z :: s ->
      begin match cmp x y <= 0, cmp y z <= 0 with
      | true,  true  -> ascending [y; x] z s
      | false, false -> descending [y; x] z s
      | true,  false ->
        let xyz = if cmp x z <= 0 then [x; z; y] else [z; x; y] in
        sort3N_rec cmp (k + 1) (push cmp xyz k stack) s
      | false, true  ->
        let xyz = if cmp x z <= 0 then [y; x; z] else [y; z; x] in
        sort3N_rec cmp (k + 1) (push cmp xyz k stack) s
      end
    | [x; y] -> pop cmp (if cmp x y <= 0 then [x; y] else [y; x]) stack
    | _ -> pop cmp s stack

  let sort3N cmp s = sort3N_rec cmp 0 [] s

end;;

(* Stack-based bottom-up tail-recursive-modulo-cons mergesorts *)
module TRMCStack = struct

  let[@tail_mod_cons] rec merge cmp xs ys =
    match xs, ys with
    | [], _ -> ys
    | _, [] -> xs
    | x :: xs', y :: ys' ->
      if cmp x y <= 0
      then x :: (merge[@tailcall]) cmp xs' ys
      else y :: (merge[@tailcall]) cmp xs ys'

  let rec push cmp xs = function
    | [] :: stack | ([] as stack) -> xs :: stack
    | ys :: stack -> [] :: push cmp (merge cmp ys xs) stack

  let rec pop cmp xs = function
    | [] -> xs
    | ys :: stack -> pop cmp (merge cmp ys xs) stack

  let rec sortN_rec cmp stack s =
    let rec ascending accu x s =
      let accu = x :: accu in
      match s with
      | [] -> pop cmp (List.rev accu) stack
      | y :: s when cmp x y <= 0 -> ascending accu y s
      | _ -> sortN_rec cmp (push cmp (List.rev accu) stack) s
    in
    let rec descending accu x s =
      let accu = x :: accu in
      match s with
      | [] -> pop cmp accu stack
      | y :: s when cmp x y > 0 -> descending accu y s
      | _ -> sortN_rec cmp (push cmp accu stack) s
    in
    match s with
    | x :: y :: s ->
      if cmp x y <= 0 then ascending [x] y s else descending [x] y s
    | _ -> pop cmp s stack

  let sortN cmp s = sortN_rec cmp [] s

  let rec sort3N_rec cmp stack s =
    let rec ascending accu x s =
      let accu = x :: accu in
      match s with
      | [] -> pop cmp (List.rev accu) stack
      | y :: s when cmp x y <= 0 -> ascending accu y s
      | _ -> sort3N_rec cmp (push cmp (List.rev accu) stack) s
    in
    let rec descending accu x s =
      let accu = x :: accu in
      match s with
      | [] -> pop cmp accu stack
      | y :: s when cmp x y > 0 -> descending accu y s
      | _ -> sort3N_rec cmp (push cmp accu stack) s
    in
    match s with
    | x :: y :: z :: s ->
      begin match cmp x y <= 0, cmp y z <= 0 with
      | true,  true  -> ascending [y; x] z s
      | false, false -> descending [y; x] z s
      | true,  false ->
        let xyz = if cmp x z <= 0 then [x; z; y] else [z; x; y] in
        sort3N_rec cmp (push cmp xyz stack) s
      | false, true  ->
        let xyz = if cmp x z <= 0 then [y; x; z] else [y; z; x] in
        sort3N_rec cmp (push cmp xyz stack) s
      end
    | [x; y] -> pop cmp (if cmp x y <= 0 then [x; y] else [y; x]) stack
    | _ -> pop cmp s stack

  let sort3N cmp s = sort3N_rec cmp [] s

end;;

(* Counting-based bottom-up tail-recursive mergesorts *)
module TRCount = struct

  let rec rev_merge cmp xs ys accu =
    match xs, ys with
    | [], _ -> List.rev_append ys accu
    | _, [] -> List.rev_append xs accu
    | x :: xs', y :: ys' ->
      if cmp x y <= 0
      then rev_merge cmp xs' ys (x :: accu)
      else rev_merge cmp xs ys' (y :: accu)

  let rec rev_merge_rev cmp xs ys accu =
    match xs, ys with
    | [], _ -> List.rev_append ys accu
    | _, [] -> List.rev_append xs accu
    | x :: xs', y :: ys' ->
      if cmp y x <= 0
      then rev_merge_rev cmp xs' ys (x :: accu)
      else rev_merge_rev cmp xs ys' (y :: accu)

  let rec push cmp xs k stack =
    match k land 3, stack with
    | 0, _ | 2, _ -> xs :: stack
    | 1, ys :: stack -> rev_merge cmp ys xs [] :: stack
    | 3, ys :: zs :: stack ->
      push cmp (rev_merge_rev cmp (rev_merge cmp ys xs []) zs [])
        (k lsr 2) stack

  let rec pop cmp xs k stack =
    match k land 3, stack with
    | _, [] -> xs
    | 0, _ -> pop cmp xs (k lsr 2) stack
    | 2, _ -> pop_rev cmp (List.rev xs) (k lsr 1) stack
    | 1, ys :: stack | 3, ys :: stack ->
      pop_rev cmp (rev_merge cmp ys xs []) (k lsr 1) stack
  and pop_rev cmp xs k stack =
    match k land 3, stack with
    | _, [] -> List.rev xs
    | 0, _ -> pop_rev cmp xs (k lsr 2) stack
    | 2, _ -> pop cmp (List.rev xs) (k lsr 1) stack
    | 1, ys :: stack | 3, ys :: stack ->
      pop cmp (rev_merge_rev cmp xs ys []) (k lsr 1) stack

  let rec sortN_rec cmp k stack s =
    let rec ascending accu x s =
      let accu = x :: accu in
      match s with
      | [] -> pop cmp (List.rev accu) k stack
      | y :: s when cmp x y <= 0 -> ascending accu y s
      | _ -> sortN_rec cmp (k + 1) (push cmp (List.rev accu) k stack) s
    in
    let rec descending accu x s =
      let accu = x :: accu in
      match s with
      | [] -> pop cmp accu k stack
      | y :: s when cmp x y > 0 -> descending accu y s
      | _ -> sortN_rec cmp (k + 1) (push cmp accu k stack) s
    in
    match s with
    | x :: y :: s ->
      if cmp x y <= 0 then ascending [x] y s else descending [x] y s
    | _ -> pop cmp s k stack

  let sortN cmp s = sortN_rec cmp 0 [] s

  let rec sort3N_rec cmp k stack s =
    let rec ascending accu x s =
      let accu = x :: accu in
      match s with
      | [] -> pop cmp (List.rev accu) k stack
      | y :: s when cmp x y <= 0 -> ascending accu y s
      | _ -> sort3N_rec cmp (k + 1) (push cmp (List.rev accu) k stack) s
    in
    let rec descending accu x s =
      let accu = x :: accu in
      match s with
      | [] -> pop cmp accu k stack
      | y :: s when cmp x y > 0 -> descending accu y s
      | _ -> sort3N_rec cmp (k + 1) (push cmp accu k stack) s
    in
    match s with
    | x :: y :: z :: s ->
      begin match cmp x y <= 0, cmp y z <= 0 with
      | true,  true  -> ascending [y; x] z s
      | false, false -> descending [y; x] z s
      | true,  false ->
        let xyz = if cmp x z <= 0 then [x; z; y] else [z; x; y] in
        sort3N_rec cmp (k + 1) (push cmp xyz k stack) s
      | false, true ->
        let xyz = if cmp x z <= 0 then [y; x; z] else [y; z; x] in
        sort3N_rec cmp (k + 1) (push cmp xyz k stack) s
      end
    | [x; y] -> pop cmp (if cmp x y <= 0 then [x; y] else [y; x]) k stack
    | _ -> pop cmp s k stack

  let sort3N cmp s = sort3N_rec cmp 0 [] s

end;;

(* Stack-based bottom-up tail-recursive mergesorts *)
module TRStack = struct

  let rec rev_merge cmp xs ys accu =
    match xs, ys with
    | [], _ -> List.rev_append ys accu
    | _, [] -> List.rev_append xs accu
    | x :: xs', y :: ys' ->
      if cmp x y <= 0
      then rev_merge cmp xs' ys (x :: accu)
      else rev_merge cmp xs ys' (y :: accu)

  let rec rev_merge_rev cmp xs ys accu =
    match xs, ys with
    | [], _ -> List.rev_append ys accu
    | _, [] -> List.rev_append xs accu
    | x :: xs', y :: ys' ->
      if cmp y x <= 0
      then rev_merge_rev cmp xs' ys (x :: accu)
      else rev_merge_rev cmp xs ys' (y :: accu)

  let rec push cmp xs = function
    | [] :: stack | ([] as stack) -> xs :: stack
    | ys :: [] :: stack | ys :: ([] as stack) ->
      [] :: rev_merge cmp ys xs [] :: stack
    | ys :: zs :: stack ->
      [] :: [] :: push cmp
        (rev_merge_rev cmp (rev_merge cmp ys xs []) zs []) stack

  let rec pop cmp xs = function
    | [] -> xs
    | [] :: [] :: stack -> pop cmp xs stack
    | [] :: stack -> pop_rev cmp (List.rev xs) stack
    | ys :: stack -> pop_rev cmp (rev_merge cmp ys xs []) stack
  and pop_rev cmp xs = function
    | [] -> List.rev xs
    | [] :: [] :: stack -> pop_rev cmp xs stack
    | [] :: stack -> pop cmp (List.rev xs) stack
    | ys :: stack -> pop cmp (rev_merge_rev cmp xs ys []) stack

  let rec sortN_rec cmp stack s =
    let rec ascending accu x s =
      let accu = x :: accu in
      match s with
      | [] -> pop cmp (List.rev accu) stack
      | y :: s when cmp x y <= 0 -> ascending accu y s
      | _ -> sortN_rec cmp (push cmp (List.rev accu) stack) s
    in
    let rec descending accu x s =
      let accu = x :: accu in
      match s with
      | [] -> pop cmp accu stack
      | y :: s when cmp x y > 0 -> descending accu y s
      | _ -> sortN_rec cmp (push cmp accu stack) s
    in
    match s with
    | x :: y :: s ->
      if cmp x y <= 0 then ascending [x] y s else descending [x] y s
    | _ -> pop cmp s stack

  let sortN cmp s = sortN_rec cmp [] s

  let rec sort3N_rec cmp stack s =
    let rec ascending accu x s =
      let accu = x :: accu in
      match s with
      | [] -> pop cmp (List.rev accu) stack
      | y :: s when cmp x y <= 0 -> ascending accu y s
      | _ -> sort3N_rec cmp (push cmp (List.rev accu) stack) s
    in
    let rec descending accu x s =
      let accu = x :: accu in
      match s with
      | [] -> pop cmp accu stack
      | y :: s when cmp x y > 0 -> descending accu y s
      | _ -> sort3N_rec cmp (push cmp accu stack) s
    in
    match s with
    | x :: y :: z :: s ->
      begin match cmp x y <= 0, cmp y z <= 0 with
      | true,  true  -> ascending [y; x] z s
      | false, false -> descending [y; x] z s
      | true,  false ->
        let xyz = if cmp x z <= 0 then [x; z; y] else [z; x; y] in
        sort3N_rec cmp (push cmp xyz stack) s
      | false, true ->
        let xyz = if cmp x z <= 0 then [y; x; z] else [y; z; x] in
        sort3N_rec cmp (push cmp xyz stack) s
      end
    | [x; y] -> pop cmp (if cmp x y <= 0 then [x; y] else [y; x]) stack
    | _ -> pop cmp s stack

  let sort3N cmp s = sort3N_rec cmp [] s

end;;
