
type 't pred = 't -> bool

type 't rel = 't -> 't pred

module MergeAcc :
 sig
  val merge_rec : 'a1 rel -> 'a1 list -> 'a1 list -> 'a1 list

  val merge : 'a1 rel -> 'a1 list -> 'a1 list -> 'a1 list
 end

val merge_sort_push : 'a1 rel -> 'a1 list -> 'a1 list list -> 'a1 list list

val merge_sort_pop : 'a1 rel -> 'a1 list -> 'a1 list list -> 'a1 list

val sort1rec : 'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 list

val sort1 : 'a1 rel -> 'a1 list -> 'a1 list

val sort2rec : 'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 list

val sort2 : 'a1 rel -> 'a1 list -> 'a1 list

val sort3rec : 'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 list

val sort3 : 'a1 rel -> 'a1 list -> 'a1 list

val sortNrec : 'a1 rel -> 'a1 list list -> 'a1 -> 'a1 list -> 'a1 list

val sortN : 'a1 rel -> 'a1 list -> 'a1 list
