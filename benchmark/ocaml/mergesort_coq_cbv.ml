
type 't pred = 't -> bool

type 't rel = 't -> 't pred

module Revmerge =
 struct
  (** val merge_rec :
      'a1 rel -> 'a1 list -> 'a1 list -> 'a1 list -> 'a1 list **)

  let rec merge_rec leT xs ys accu =
    match xs with
    | [] -> List.rev_append ys accu
    | x::xs' ->
      let rec merge_rec' ys0 accu0 =
        match ys0 with
        | [] -> List.rev_append xs accu0
        | y::ys' ->
          if leT x y
          then merge_rec leT xs' ys0 (x::accu0)
          else merge_rec' ys' (y::accu0)
      in merge_rec' ys accu

  (** val revmerge : 'a1 rel -> 'a1 list -> 'a1 list -> 'a1 list **)

  let revmerge leT xs ys =
    merge_rec leT xs ys []
 end

(** val merge_sort_push :
    'a1 rel -> 'a1 list -> 'a1 list list -> 'a1 list list **)

let rec merge_sort_push leT xs stack = match stack with
| [] -> xs::stack
| ys::stack0 ->
  (match ys with
   | [] -> xs::stack0
   | _::_ ->
     (match stack0 with
      | [] -> []::((Revmerge.revmerge leT ys xs)::stack0)
      | zs::stack1 ->
        (match zs with
         | [] -> []::((Revmerge.revmerge leT ys xs)::stack1)
         | _::_ ->
           []::([]::(merge_sort_push leT
                      (Revmerge.revmerge (fun x y -> leT y x)
                        (Revmerge.revmerge leT ys xs) zs) stack1)))))

(** val merge_sort_pop :
    'a1 rel -> bool -> 'a1 list -> 'a1 list list -> 'a1 list **)

let rec merge_sort_pop leT mode xs = function
| [] -> if mode then List.rev xs else xs
| ys::stack0 ->
  (match ys with
   | [] ->
     (match stack0 with
      | [] -> merge_sort_pop leT (not mode) (List.rev xs) stack0
      | l::stack1 ->
        (match l with
         | [] -> merge_sort_pop leT mode xs stack1
         | _::_ -> merge_sort_pop leT (not mode) (List.rev xs) stack0))
   | _::_ ->
     if mode
     then merge_sort_pop leT false
            (Revmerge.revmerge (fun x y -> leT y x) xs ys) stack0
     else merge_sort_pop leT true (Revmerge.revmerge leT ys xs) stack0)

(** val sort1rec : 'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 list **)

let rec sort1rec leT stack = function
| [] -> merge_sort_pop leT false [] stack
| x::s0 -> sort1rec leT (merge_sort_push leT (x::[]) stack) s0

(** val sort1 : 'a1 rel -> 'a1 list -> 'a1 list **)

let sort1 leT =
  sort1rec leT []

(** val sort2rec : 'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 list **)

let rec sort2rec leT stack s = match s with
| [] -> merge_sort_pop leT false s stack
| x1::l ->
  (match l with
   | [] -> merge_sort_pop leT false s stack
   | x2::s' ->
     sort2rec leT
       (merge_sort_push leT
         (if leT x1 x2 then x1::(x2::[]) else x2::(x1::[])) stack) s')

(** val sort2 : 'a1 rel -> 'a1 list -> 'a1 list **)

let sort2 leT =
  sort2rec leT []

(** val sort3rec : 'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 list **)

let rec sort3rec leT stack s = match s with
| [] -> merge_sort_pop leT false s stack
| x1::l ->
  (match l with
   | [] -> merge_sort_pop leT false s stack
   | x2::l0 ->
     (match l0 with
      | [] ->
        merge_sort_pop leT false (if leT x1 x2 then s else x2::(x1::[])) stack
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
  | [] -> merge_sort_pop leT false (x::[]) stack
  | y::s0 ->
    if leT x y then incr stack y s0 (x::[]) else decr stack y s0 (x::[])
  and incr stack x s accu =
    match s with
    | [] -> merge_sort_pop leT false (List.rev_append accu (x::[])) stack
    | y::s0 ->
      if leT x y
      then incr stack y s0 (x::accu)
      else sortNrec0
             (merge_sort_push leT (List.rev_append accu (x::[])) stack) y s0
  and decr stack x s accu =
    match s with
    | [] -> merge_sort_pop leT false (x::accu) stack
    | y::s0 ->
      if leT x y
      then sortNrec0 (merge_sort_push leT (x::accu) stack) y s0
      else decr stack y s0 (x::accu)
  in sortNrec0

(** val sortN : 'a1 rel -> 'a1 list -> 'a1 list **)

let sortN leT = function
| [] -> []
| x::s0 -> sortNrec leT [] x s0
