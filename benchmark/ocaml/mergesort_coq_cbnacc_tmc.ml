
type 't pred = 't -> bool

type 't rel = 't -> 't pred

module MergeAcc =
 struct
  (** val merge_rec : 'a1 rel -> 'a1 list -> 'a1 list -> 'a1 list **)

  let[@tail_mod_cons] rec merge_rec leT xs ys =
    match xs with
    | [] -> ys
    | x::xs' ->
      (match ys with
       | [] -> xs
       | y::ys' ->
         if leT x y
         then x::((merge_rec[@tailcall]) leT xs' ys)
         else y::((merge_rec[@tailcall]) leT xs ys'))

  (** val merge : 'a1 rel -> 'a1 list -> 'a1 list -> 'a1 list **)

  let merge =
    merge_rec
 end

(** val merge_sort_push :
    'a1 rel -> 'a1 list -> 'a1 list list -> 'a1 list list **)

let rec merge_sort_push leT s stack = match stack with
| [] -> s::stack
| s'::stack' ->
  (match s' with
   | [] -> s::stack'
   | _::_ -> []::(merge_sort_push leT (MergeAcc.merge leT s' s) stack'))

(** val merge_sort_pop : 'a1 rel -> 'a1 list -> 'a1 list list -> 'a1 list **)

let rec merge_sort_pop leT s1 = function
| [] -> s1
| s2::stack' -> merge_sort_pop leT (MergeAcc.merge leT s2 s1) stack'

(** val sort1rec : 'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 list **)

let rec sort1rec leT stack = function
| [] -> merge_sort_pop leT [] stack
| x::s0 -> sort1rec leT (merge_sort_push leT (x::[]) stack) s0

(** val sort1 : 'a1 rel -> 'a1 list -> 'a1 list **)

let sort1 leT =
  sort1rec leT []

(** val sort2rec : 'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 list **)

let rec sort2rec leT stack s = match s with
| [] -> merge_sort_pop leT s stack
| x1::l ->
  (match l with
   | [] -> merge_sort_pop leT s stack
   | x2::s' ->
     sort2rec leT
       (merge_sort_push leT
         (if leT x1 x2 then x1::(x2::[]) else x2::(x1::[])) stack) s')

(** val sort2 : 'a1 rel -> 'a1 list -> 'a1 list **)

let sort2 leT =
  sort2rec leT []

(** val sort3rec : 'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 list **)

let rec sort3rec leT stack s = match s with
| [] -> merge_sort_pop leT s stack
| x1::l ->
  (match l with
   | [] -> merge_sort_pop leT s stack
   | x2::l0 ->
     (match l0 with
      | [] -> merge_sort_pop leT (if leT x1 x2 then s else x2::(x1::[])) stack
      | x3::s' ->
        sort3rec leT
          (merge_sort_push leT
            (if leT x1 x2
             then if leT x2 x3
                  then x1::(x2::(x3::[]))
                  else if leT x1 x3
                       then x1::(x3::(x2::[]))
                       else x3::(x1::(x2::[]))
             else if leT x1 x3
                  then x2::(x1::(x3::[]))
                  else if leT x2 x3
                       then x2::(x3::(x1::[]))
                       else x3::(x2::(x1::[]))) stack) s'))

(** val sort3 : 'a1 rel -> 'a1 list -> 'a1 list **)

let sort3 leT =
  sort3rec leT []

(** val sortNrec : 'a1 rel -> 'a1 list list -> 'a1 -> 'a1 list -> 'a1 list **)

let sortNrec leT =
  let rec sortNrec0 stack x = function
  | [] -> merge_sort_pop leT (x::[]) stack
  | y::s0 ->
    if leT x y then incr stack y s0 (x::[]) else decr stack y s0 (x::[])
  and incr stack x s accu =
    match s with
    | [] -> merge_sort_pop leT (List.rev_append accu (x::[])) stack
    | y::s0 ->
      if leT x y
      then incr stack y s0 (x::accu)
      else sortNrec0
             (merge_sort_push leT (List.rev_append accu (x::[])) stack) y s0
  and decr stack x s accu =
    match s with
    | [] -> merge_sort_pop leT (x::accu) stack
    | y::s0 ->
      if leT x y
      then sortNrec0 (merge_sort_push leT (x::accu) stack) y s0
      else decr stack y s0 (x::accu)
  in sortNrec0

(** val sortN : 'a1 rel -> 'a1 list -> 'a1 list **)

let sortN leT = function
| [] -> []
| x::s0 -> sortNrec leT [] x s0
