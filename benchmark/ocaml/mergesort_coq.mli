
type __ = Obj.t

type 'a sig2 = 'a
  (* singleton inductive, whose constructor was exist2 *)

type reflect =
| ReflectT
| ReflectF

val ssr_have : 'a1 -> ('a1 -> 'a2) -> 'a2

type alt_spec =
| AltTrue
| AltFalse

val altP : bool -> reflect -> alt_spec

val idP : bool -> reflect

val boolP : bool -> alt_spec

type 't pred = 't -> bool

type 't rel = 't -> 't pred

module Equality :
 sig
  type 't axiom = 't -> 't -> reflect

  type 't mixin_of = { op : 't rel; mixin_of__1 : 't axiom }

  val op : 'a1 mixin_of -> 'a1 rel

  type coq_type =
    __ mixin_of
    (* singleton inductive, whose constructor was Pack *)

  type sort = __

  val coq_class : coq_type -> sort mixin_of
 end

val nilP : 'a1 list -> reflect

val cat : 'a1 list -> 'a1 list -> 'a1 list



val merge : 'a1 rel -> 'a1 list -> 'a1 list -> 'a1 list

type bool_R =
| Bool_R_true_R
| Bool_R_false_R

type ('x0, 'x, 'a_R) list_R =
| List_R_nil_R
| List_R_cons_R of 'x0 * 'x * 'a_R * 'x0 list * 'x list
   * ('x0, 'x, 'a_R) list_R

type ('x0, 'x, 't_R) pred_R = 'x0 -> 'x -> 't_R -> bool_R

type ('x0, 'x, 't_R) rel_R = 'x0 -> 'x -> 't_R -> ('x0, 'x, 't_R) pred_R

module StableSort :
 sig
  type 't trace =
  | Coq_branch_trace of bool * 't trace * 't trace
  | Coq_leaf_trace of Equality.sort * 't list

  val empty_trace : 'a1 rel -> 'a1 trace

  val flatten_trace : 'a1 rel -> 'a1 trace -> 'a1 list

  val sort_trace : 'a1 rel -> 'a1 trace -> 'a1 list

  type 't trace_nil_spec =
  | TraceNil
  | TraceNotNil

  val trace_nilP : 'a1 rel -> 'a1 trace -> 'a1 trace_nil_spec

  type sort_ty_R =
    __ -> __ -> __ -> __ rel -> __ rel -> (__, __, __) rel_R -> __ list -> __
    list -> (__, __, __) list_R -> (__, __, __) list_R

  type coq_function = { apply : (__ -> __ rel -> __ list -> __ list);
                        coq_function__1 : sort_ty_R;
                        coq_function__2 : (__ -> __ rel -> __ list -> __
                                          trace sig2) }
 end

module type MergeSig =
 sig
  val merge : 'a1 rel -> 'a1 list -> 'a1 list -> 'a1 list

  val merge_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) list_R
    -> ('a1, 'a2, 'a3) list_R
 end

module type RevmergeSig =
 sig
  val revmerge : 'a1 rel -> 'a1 list -> 'a1 list -> 'a1 list

  val revmerge_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) list_R
    -> ('a1, 'a2, 'a3) list_R
 end

module Merge :
 sig
  val merge : 'a1 rel -> 'a1 list -> 'a1 list -> 'a1 list

  val merge_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) list_R
    -> ('a1, 'a2, 'a3) list_R
 end

module MergeAcc :
 sig
  val merge_rec : 'a1 rel -> 'a1 list -> 'a1 list -> 'a1 list

  val merge : 'a1 rel -> 'a1 list -> 'a1 list -> 'a1 list

  val merge_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) list_R
    -> ('a1, 'a2, 'a3) list_R
 end

module Revmerge :
 sig
  val merge_rec : 'a1 rel -> 'a1 list -> 'a1 list -> 'a1 list -> 'a1 list

  val revmerge : 'a1 rel -> 'a1 list -> 'a1 list -> 'a1 list

  val revmerge_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) list_R
    -> ('a1, 'a2, 'a3) list_R
 end

module RevmergeAcc :
 sig
  val merge_rec : 'a1 rel -> 'a1 list -> 'a1 list -> 'a1 list -> 'a1 list

  val revmerge : 'a1 rel -> 'a1 list -> 'a1 list -> 'a1 list

  val revmerge_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) list_R
    -> ('a1, 'a2, 'a3) list_R
 end

module CBN_ :
 functor (M:MergeSig) ->
 sig
  val merge_sort_push : 'a1 rel -> 'a1 list -> 'a1 list list -> 'a1 list list

  val merge_sort_pop : 'a1 rel -> 'a1 list -> 'a1 list list -> 'a1 list

  val sort1rec : 'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 list

  val sort1 : 'a1 rel -> 'a1 list -> 'a1 list

  val sort2rec : 'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 list

  val sort2 : 'a1 rel -> 'a1 list -> 'a1 list

  val sort3rec : 'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 list

  val sort3 : 'a1 rel -> 'a1 list -> 'a1 list

  val sortNrec : 'a1 rel -> 'a1 list list -> 'a1 -> 'a1 list -> 'a1 list

  val incr :
    'a1 rel -> 'a1 list list -> 'a1 -> 'a1 list -> 'a1 list -> 'a1 list

  val decr :
    'a1 rel -> 'a1 list list -> 'a1 -> 'a1 list -> 'a1 list -> 'a1 list

  val sortN : 'a1 rel -> 'a1 list -> 'a1 list

  val merge_sort_pushP :
    'a1 rel -> 'a1 StableSort.trace -> 'a1 StableSort.trace list -> 'a1
    StableSort.trace list sig2

  val merge_sort_popP :
    'a1 rel -> 'a1 StableSort.trace -> 'a1 StableSort.trace list -> 'a1
    StableSort.trace sig2

  val sort1P : 'a1 rel -> 'a1 list -> 'a1 StableSort.trace sig2

  val sort2P : 'a1 rel -> 'a1 list -> 'a1 StableSort.trace sig2

  val sort3P : 'a1 rel -> 'a1 list -> 'a1 StableSort.trace sig2

  val sortNP : 'a1 rel -> 'a1 list -> 'a1 StableSort.trace sig2

  val merge_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) list_R
    -> ('a1, 'a2, 'a3) list_R

  val merge_sort_push_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> 'a1 list list -> 'a2 list list -> ('a1 list,
    'a2 list, ('a1, 'a2, 'a3) list_R) list_R -> ('a1 list, 'a2 list, ('a1,
    'a2, 'a3) list_R) list_R

  val merge_sort_pop_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> 'a1 list list -> 'a2 list list -> ('a1 list,
    'a2 list, ('a1, 'a2, 'a3) list_R) list_R -> ('a1, 'a2, 'a3) list_R

  val sort1_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> ('a1, 'a2, 'a3) list_R

  val sort2_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> ('a1, 'a2, 'a3) list_R

  val sort3_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> ('a1, 'a2, 'a3) list_R

  val sortN_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> ('a1, 'a2, 'a3) list_R

  val sort1_stable : StableSort.coq_function

  val sort2_stable : StableSort.coq_function

  val sort3_stable : StableSort.coq_function

  val sortN_stable : StableSort.coq_function
 end

module CBN :
 sig
  val merge_sort_push : 'a1 rel -> 'a1 list -> 'a1 list list -> 'a1 list list

  val merge_sort_pop : 'a1 rel -> 'a1 list -> 'a1 list list -> 'a1 list

  val sort1rec : 'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 list

  val sort1 : 'a1 rel -> 'a1 list -> 'a1 list

  val sort2rec : 'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 list

  val sort2 : 'a1 rel -> 'a1 list -> 'a1 list

  val sort3rec : 'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 list

  val sort3 : 'a1 rel -> 'a1 list -> 'a1 list

  val sortNrec : 'a1 rel -> 'a1 list list -> 'a1 -> 'a1 list -> 'a1 list

  val incr :
    'a1 rel -> 'a1 list list -> 'a1 -> 'a1 list -> 'a1 list -> 'a1 list

  val decr :
    'a1 rel -> 'a1 list list -> 'a1 -> 'a1 list -> 'a1 list -> 'a1 list

  val sortN : 'a1 rel -> 'a1 list -> 'a1 list

  val merge_sort_pushP :
    'a1 rel -> 'a1 StableSort.trace -> 'a1 StableSort.trace list -> 'a1
    StableSort.trace list sig2

  val merge_sort_popP :
    'a1 rel -> 'a1 StableSort.trace -> 'a1 StableSort.trace list -> 'a1
    StableSort.trace sig2

  val sort1P : 'a1 rel -> 'a1 list -> 'a1 StableSort.trace sig2

  val sort2P : 'a1 rel -> 'a1 list -> 'a1 StableSort.trace sig2

  val sort3P : 'a1 rel -> 'a1 list -> 'a1 StableSort.trace sig2

  val sortNP : 'a1 rel -> 'a1 list -> 'a1 StableSort.trace sig2

  val merge_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) list_R
    -> ('a1, 'a2, 'a3) list_R

  val merge_sort_push_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> 'a1 list list -> 'a2 list list -> ('a1 list,
    'a2 list, ('a1, 'a2, 'a3) list_R) list_R -> ('a1 list, 'a2 list, ('a1,
    'a2, 'a3) list_R) list_R

  val merge_sort_pop_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> 'a1 list list -> 'a2 list list -> ('a1 list,
    'a2 list, ('a1, 'a2, 'a3) list_R) list_R -> ('a1, 'a2, 'a3) list_R

  val sort1_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> ('a1, 'a2, 'a3) list_R

  val sort2_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> ('a1, 'a2, 'a3) list_R

  val sort3_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> ('a1, 'a2, 'a3) list_R

  val sortN_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> ('a1, 'a2, 'a3) list_R

  val sort1_stable : StableSort.coq_function

  val sort2_stable : StableSort.coq_function

  val sort3_stable : StableSort.coq_function

  val sortN_stable : StableSort.coq_function
 end

module CBNAcc :
 sig
  val merge_sort_push : 'a1 rel -> 'a1 list -> 'a1 list list -> 'a1 list list

  val merge_sort_pop : 'a1 rel -> 'a1 list -> 'a1 list list -> 'a1 list

  val sort1rec : 'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 list

  val sort1 : 'a1 rel -> 'a1 list -> 'a1 list

  val sort2rec : 'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 list

  val sort2 : 'a1 rel -> 'a1 list -> 'a1 list

  val sort3rec : 'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 list

  val sort3 : 'a1 rel -> 'a1 list -> 'a1 list

  val sortNrec : 'a1 rel -> 'a1 list list -> 'a1 -> 'a1 list -> 'a1 list

  val incr :
    'a1 rel -> 'a1 list list -> 'a1 -> 'a1 list -> 'a1 list -> 'a1 list

  val decr :
    'a1 rel -> 'a1 list list -> 'a1 -> 'a1 list -> 'a1 list -> 'a1 list

  val sortN : 'a1 rel -> 'a1 list -> 'a1 list

  val merge_sort_pushP :
    'a1 rel -> 'a1 StableSort.trace -> 'a1 StableSort.trace list -> 'a1
    StableSort.trace list sig2

  val merge_sort_popP :
    'a1 rel -> 'a1 StableSort.trace -> 'a1 StableSort.trace list -> 'a1
    StableSort.trace sig2

  val sort1P : 'a1 rel -> 'a1 list -> 'a1 StableSort.trace sig2

  val sort2P : 'a1 rel -> 'a1 list -> 'a1 StableSort.trace sig2

  val sort3P : 'a1 rel -> 'a1 list -> 'a1 StableSort.trace sig2

  val sortNP : 'a1 rel -> 'a1 list -> 'a1 StableSort.trace sig2

  val merge_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) list_R
    -> ('a1, 'a2, 'a3) list_R

  val merge_sort_push_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> 'a1 list list -> 'a2 list list -> ('a1 list,
    'a2 list, ('a1, 'a2, 'a3) list_R) list_R -> ('a1 list, 'a2 list, ('a1,
    'a2, 'a3) list_R) list_R

  val merge_sort_pop_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> 'a1 list list -> 'a2 list list -> ('a1 list,
    'a2 list, ('a1, 'a2, 'a3) list_R) list_R -> ('a1, 'a2, 'a3) list_R

  val sort1_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> ('a1, 'a2, 'a3) list_R

  val sort2_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> ('a1, 'a2, 'a3) list_R

  val sort3_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> ('a1, 'a2, 'a3) list_R

  val sortN_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> ('a1, 'a2, 'a3) list_R

  val sort1_stable : StableSort.coq_function

  val sort2_stable : StableSort.coq_function

  val sort3_stable : StableSort.coq_function

  val sortN_stable : StableSort.coq_function
 end

module CBV_ :
 functor (M:RevmergeSig) ->
 sig
  val merge_sort_push : 'a1 rel -> 'a1 list -> 'a1 list list -> 'a1 list list

  val merge_sort_pop :
    'a1 rel -> bool -> 'a1 list -> 'a1 list list -> 'a1 list

  val sort1rec : 'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 list

  val sort1 : 'a1 rel -> 'a1 list -> 'a1 list

  val sort2rec : 'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 list

  val sort2 : 'a1 rel -> 'a1 list -> 'a1 list

  val sort3rec : 'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 list

  val sort3 : 'a1 rel -> 'a1 list -> 'a1 list

  val sortNrec : 'a1 rel -> 'a1 list list -> 'a1 -> 'a1 list -> 'a1 list

  val incr :
    'a1 rel -> 'a1 list list -> 'a1 -> 'a1 list -> 'a1 list -> 'a1 list

  val decr :
    'a1 rel -> 'a1 list list -> 'a1 -> 'a1 list -> 'a1 list -> 'a1 list

  val sortN : 'a1 rel -> 'a1 list -> 'a1 list

  val merge_sort_pushP :
    'a1 rel -> 'a1 StableSort.trace -> 'a1 StableSort.trace list -> 'a1
    StableSort.trace list sig2

  val merge_sort_popP :
    'a1 rel -> bool -> 'a1 StableSort.trace -> 'a1 StableSort.trace list ->
    'a1 StableSort.trace sig2

  val sort1P : 'a1 rel -> 'a1 list -> 'a1 StableSort.trace sig2

  val sort2P : 'a1 rel -> 'a1 list -> 'a1 StableSort.trace sig2

  val sort3P : 'a1 rel -> 'a1 list -> 'a1 StableSort.trace sig2

  val sortNP : 'a1 rel -> 'a1 list -> 'a1 StableSort.trace sig2

  val revmerge_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) list_R
    -> ('a1, 'a2, 'a3) list_R

  val merge_sort_push_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> 'a1 list list -> 'a2 list list -> ('a1 list,
    'a2 list, ('a1, 'a2, 'a3) list_R) list_R -> ('a1 list, 'a2 list, ('a1,
    'a2, 'a3) list_R) list_R

  val merge_sort_pop_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> bool -> bool -> bool_R ->
    'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) list_R -> 'a1 list list -> 'a2
    list list -> ('a1 list, 'a2 list, ('a1, 'a2, 'a3) list_R) list_R -> ('a1,
    'a2, 'a3) list_R

  val sort1_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> ('a1, 'a2, 'a3) list_R

  val sort2_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> ('a1, 'a2, 'a3) list_R

  val sort3_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> ('a1, 'a2, 'a3) list_R

  val sortN_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> ('a1, 'a2, 'a3) list_R

  val sort1_stable : StableSort.coq_function

  val sort2_stable : StableSort.coq_function

  val sort3_stable : StableSort.coq_function

  val sortN_stable : StableSort.coq_function
 end

module CBV :
 sig
  val merge_sort_push : 'a1 rel -> 'a1 list -> 'a1 list list -> 'a1 list list

  val merge_sort_pop :
    'a1 rel -> bool -> 'a1 list -> 'a1 list list -> 'a1 list

  val sort1rec : 'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 list

  val sort1 : 'a1 rel -> 'a1 list -> 'a1 list

  val sort2rec : 'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 list

  val sort2 : 'a1 rel -> 'a1 list -> 'a1 list

  val sort3rec : 'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 list

  val sort3 : 'a1 rel -> 'a1 list -> 'a1 list

  val sortNrec : 'a1 rel -> 'a1 list list -> 'a1 -> 'a1 list -> 'a1 list

  val incr :
    'a1 rel -> 'a1 list list -> 'a1 -> 'a1 list -> 'a1 list -> 'a1 list

  val decr :
    'a1 rel -> 'a1 list list -> 'a1 -> 'a1 list -> 'a1 list -> 'a1 list

  val sortN : 'a1 rel -> 'a1 list -> 'a1 list

  val merge_sort_pushP :
    'a1 rel -> 'a1 StableSort.trace -> 'a1 StableSort.trace list -> 'a1
    StableSort.trace list sig2

  val merge_sort_popP :
    'a1 rel -> bool -> 'a1 StableSort.trace -> 'a1 StableSort.trace list ->
    'a1 StableSort.trace sig2

  val sort1P : 'a1 rel -> 'a1 list -> 'a1 StableSort.trace sig2

  val sort2P : 'a1 rel -> 'a1 list -> 'a1 StableSort.trace sig2

  val sort3P : 'a1 rel -> 'a1 list -> 'a1 StableSort.trace sig2

  val sortNP : 'a1 rel -> 'a1 list -> 'a1 StableSort.trace sig2

  val revmerge_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) list_R
    -> ('a1, 'a2, 'a3) list_R

  val merge_sort_push_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> 'a1 list list -> 'a2 list list -> ('a1 list,
    'a2 list, ('a1, 'a2, 'a3) list_R) list_R -> ('a1 list, 'a2 list, ('a1,
    'a2, 'a3) list_R) list_R

  val merge_sort_pop_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> bool -> bool -> bool_R ->
    'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) list_R -> 'a1 list list -> 'a2
    list list -> ('a1 list, 'a2 list, ('a1, 'a2, 'a3) list_R) list_R -> ('a1,
    'a2, 'a3) list_R

  val sort1_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> ('a1, 'a2, 'a3) list_R

  val sort2_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> ('a1, 'a2, 'a3) list_R

  val sort3_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> ('a1, 'a2, 'a3) list_R

  val sortN_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> ('a1, 'a2, 'a3) list_R

  val sort1_stable : StableSort.coq_function

  val sort2_stable : StableSort.coq_function

  val sort3_stable : StableSort.coq_function

  val sortN_stable : StableSort.coq_function
 end

module CBVAcc :
 sig
  val merge_sort_push : 'a1 rel -> 'a1 list -> 'a1 list list -> 'a1 list list

  val merge_sort_pop :
    'a1 rel -> bool -> 'a1 list -> 'a1 list list -> 'a1 list

  val sort1rec : 'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 list

  val sort1 : 'a1 rel -> 'a1 list -> 'a1 list

  val sort2rec : 'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 list

  val sort2 : 'a1 rel -> 'a1 list -> 'a1 list

  val sort3rec : 'a1 rel -> 'a1 list list -> 'a1 list -> 'a1 list

  val sort3 : 'a1 rel -> 'a1 list -> 'a1 list

  val sortNrec : 'a1 rel -> 'a1 list list -> 'a1 -> 'a1 list -> 'a1 list

  val incr :
    'a1 rel -> 'a1 list list -> 'a1 -> 'a1 list -> 'a1 list -> 'a1 list

  val decr :
    'a1 rel -> 'a1 list list -> 'a1 -> 'a1 list -> 'a1 list -> 'a1 list

  val sortN : 'a1 rel -> 'a1 list -> 'a1 list

  val merge_sort_pushP :
    'a1 rel -> 'a1 StableSort.trace -> 'a1 StableSort.trace list -> 'a1
    StableSort.trace list sig2

  val merge_sort_popP :
    'a1 rel -> bool -> 'a1 StableSort.trace -> 'a1 StableSort.trace list ->
    'a1 StableSort.trace sig2

  val sort1P : 'a1 rel -> 'a1 list -> 'a1 StableSort.trace sig2

  val sort2P : 'a1 rel -> 'a1 list -> 'a1 StableSort.trace sig2

  val sort3P : 'a1 rel -> 'a1 list -> 'a1 StableSort.trace sig2

  val sortNP : 'a1 rel -> 'a1 list -> 'a1 StableSort.trace sig2

  val revmerge_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> 'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) list_R
    -> ('a1, 'a2, 'a3) list_R

  val merge_sort_push_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> 'a1 list list -> 'a2 list list -> ('a1 list,
    'a2 list, ('a1, 'a2, 'a3) list_R) list_R -> ('a1 list, 'a2 list, ('a1,
    'a2, 'a3) list_R) list_R

  val merge_sort_pop_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> bool -> bool -> bool_R ->
    'a1 list -> 'a2 list -> ('a1, 'a2, 'a3) list_R -> 'a1 list list -> 'a2
    list list -> ('a1 list, 'a2 list, ('a1, 'a2, 'a3) list_R) list_R -> ('a1,
    'a2, 'a3) list_R

  val sort1_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> ('a1, 'a2, 'a3) list_R

  val sort2_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> ('a1, 'a2, 'a3) list_R

  val sort3_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> ('a1, 'a2, 'a3) list_R

  val sortN_R :
    'a1 rel -> 'a2 rel -> ('a1, 'a2, 'a3) rel_R -> 'a1 list -> 'a2 list ->
    ('a1, 'a2, 'a3) list_R -> ('a1, 'a2, 'a3) list_R

  val sort1_stable : StableSort.coq_function

  val sort2_stable : StableSort.coq_function

  val sort3_stable : StableSort.coq_function

  val sortN_stable : StableSort.coq_function
 end
