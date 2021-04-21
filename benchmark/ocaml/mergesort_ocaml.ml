module CBV = struct

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

  let rec merge_sort_push cmp xs = function
    | [] :: stack | ([] as stack) -> xs :: stack
    | ys :: [] :: stack | ys :: ([] as stack) ->
      [] :: rev_merge cmp ys xs [] :: stack
    | ys :: zs :: stack ->
      [] :: [] :: merge_sort_push cmp
        (rev_merge_rev cmp (rev_merge cmp ys xs []) zs []) stack

  let rec merge_sort_pop cmp mode xs = function
    | [] -> if mode then List.rev xs else xs
    | [] :: [] :: stack -> merge_sort_pop cmp mode xs stack
    | [] :: stack -> merge_sort_pop cmp (not mode) (List.rev xs) stack
    | ys :: stack ->
      if mode
      then merge_sort_pop cmp false (rev_merge_rev cmp xs ys []) stack
      else merge_sort_pop cmp true (rev_merge cmp ys xs []) stack

  let rec merge_sort_rec cmp stack x s =
    let rec inner_rec_asc accu x s =
      let accu = x :: accu in
      match s with
      | [] -> merge_sort_pop cmp false (List.rev accu) stack
      | y :: s ->
        if cmp x y <= 0
        then inner_rec_asc accu y s
        else merge_sort_rec cmp (merge_sort_push cmp (List.rev accu) stack) y s
    in
    let rec inner_rec_desc accu x s =
      let accu = x :: accu in
      match s with
      | [] -> merge_sort_pop cmp false accu stack
      | y :: s ->
        if cmp x y > 0
        then inner_rec_desc accu y s
        else merge_sort_rec cmp (merge_sort_push cmp accu stack) y s
    in
    match s with
    | y :: s ->
      if cmp x y <= 0
      then inner_rec_asc [x] y s
      else inner_rec_desc [x] y s
    | _ -> merge_sort_pop cmp false [x] stack

  let sort cmp = function
    | [] -> []
    | x :: s -> merge_sort_rec cmp [] x s

end;;

module CBV2 = struct

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

  let rec merge_sort_push cmp xs = function
    | [] :: stack | ([] as stack) -> xs :: stack
    | ys :: [] :: stack | ys :: ([] as stack) ->
      [] :: rev_merge cmp ys xs [] :: stack
    | ys :: zs :: stack ->
      [] :: [] :: merge_sort_push cmp
        (rev_merge_rev cmp (rev_merge cmp ys xs []) zs []) stack

  let rec merge_sort_pop cmp mode xs = function
    | [] -> if mode then List.rev xs else xs
    | [] :: [] :: stack -> merge_sort_pop cmp mode xs stack
    | [] :: stack -> merge_sort_pop cmp (not mode) (List.rev xs) stack
    | ys :: stack ->
      if mode
      then merge_sort_pop cmp false (rev_merge_rev cmp xs ys []) stack
      else merge_sort_pop cmp true (rev_merge cmp ys xs []) stack

  let rec merge_sort_rec_ cmp stack x s =
    let rec inner_rec_asc accu x s =
      let accu = x :: accu in
      match s with
      | [] -> merge_sort_pop cmp false (List.rev accu) stack
      | y :: s ->
        if cmp x y <= 0
        then inner_rec_asc accu y s
        else merge_sort_rec_ cmp (merge_sort_push cmp (List.rev accu) stack) y s
    in
    let rec inner_rec_desc accu x s =
      let accu = x :: accu in
      match s with
      | [] -> merge_sort_pop cmp false accu stack
      | y :: s ->
        if cmp x y > 0
        then inner_rec_desc accu y s
        else merge_sort_rec_ cmp (merge_sort_push cmp accu stack) y s
    in
    match s with
    | y :: z :: s ->
      begin match cmp x y <= 0, cmp y z <= 0 with
        | true,  true  -> inner_rec_asc [y; x] z s
        | false, false -> inner_rec_desc [y; x] z s
        | true,  false ->
          let xyz = if cmp x z <= 0 then [x; z; y] else [z; x; y] in
          merge_sort_rec cmp (merge_sort_push cmp xyz stack) s
        | false, true  ->
          let xyz = if cmp x z <= 0 then [y; x; z] else [y; z; x] in
          merge_sort_rec cmp (merge_sort_push cmp xyz stack) s
      end
    | [y] ->
      let xy = if cmp x y <= 0 then [x; y] else [y; x] in
      merge_sort_pop cmp false xy stack
    | [] -> merge_sort_pop cmp false [x] stack
  and merge_sort_rec cmp stack = function
    | [] -> merge_sort_pop cmp false [] stack
    | x :: s -> merge_sort_rec_ cmp stack x s

  let sort cmp s = merge_sort_rec cmp [] s

end;;
