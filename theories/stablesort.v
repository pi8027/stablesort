From stablesort Require Import mathcomp_ext.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From stablesort Require Import param.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(* The abstract interface for stable (merge)sort algorithms                   *)
(******************************************************************************)

Module StableSort.

Section Trees.

Variables (T : Type) (P : {pred T}) (leT : rel T).

(* One easy way to prove the correctness of highly optimized stable sort      *)
(* algorithms is to prove the equivalence between it and a simpler (but       *)
(* unoptimized) algorithm, e.g., insertion sort. However, such equivalence    *)
(* proof requires the comparison function [leT : rel T] to be total and       *)
(* transitive so that [merge] is associative. These requirements are          *)
(* undesirable since some correctness properties hold without them.           *)
(* Therefore, we present a type of binary trees [tree] representing the       *)
(* divide-and-conquer structure of sort. These trees can also be seen as      *)
(* "traces" of sorting algorithms, and have to be balanced in the case of     *)
(* O(n log n) mergesort. Nevertheless, these trees can also represent rather  *)
(* naive algorithms such as insertion sort, since there is no such formal     *)
(* "balanced" restriction.                                                    *)
Inductive tree :=
  | branch_tree   : bool -> tree -> tree -> tree
  | leaf_tree b s : sorted (fun x y => leT x y == b) s -> tree.

Definition empty_tree := @leaf_tree false [::] erefl.

(* By flattening a tree, the input list can be obtained.                      *)
Fixpoint flatten_tree (t : tree) : seq T :=
  match t with
    | branch_tree _ l r => flatten_tree l ++ flatten_tree r
    | leaf_tree _ s _ => s
  end.

(* By sorting a tree, the output list can be obtained.                        *)
Fixpoint sort_tree (t : tree) : seq T :=
  match t with
    | branch_tree true  l r => merge leT (sort_tree l) (sort_tree r)
    | branch_tree false l r =>
      rev (merge (fun x y => leT y x) (rev (sort_tree r)) (rev (sort_tree l)))
    | leaf_tree true  s _ => s
    | leaf_tree false s _ => rev s
  end.

Lemma all_tree (t : tree) : all P (sort_tree t) = all P (flatten_tree t).
Proof.
elim: t => [b l IHl r IHr|[] s] /=; rewrite ?all_rev //.
by case: b; rewrite ?(all_rev, all_merge) all_cat IHl IHr // andbC.
Qed.

Lemma size_tree (t : tree) : size (sort_tree t) = size (flatten_tree t).
Proof.
elim: t => [b l IHl r IHr|[] s] /=; rewrite ?size_rev //.
by case: b; rewrite ?(size_rev, size_merge, size_cat) IHl IHr // addnC.
Qed.

Lemma tree_nilp (t : tree) : nilp (sort_tree t) = nilp (flatten_tree t).
Proof. by move: (sort_tree t) (flatten_tree t) (size_tree t) => [|? ?] []. Qed.

Variant tree_nil_spec (t : tree) : seq T -> seq T -> bool -> bool -> Type :=
  | TreeNil    : flatten_tree t = [::] -> sort_tree t = [::] ->
                 tree_nil_spec t [::] [::] true true
  | TreeNotNil : flatten_tree t <> [::] -> sort_tree t <> [::] ->
                 tree_nil_spec t (flatten_tree t) (sort_tree t) false false.

Lemma tree_nilP (t : tree) :
  tree_nil_spec t (flatten_tree t) (sort_tree t)
                (nilp (flatten_tree t)) (nilp (sort_tree t)).
Proof.
case: nilP (tree_nilp t); case: nilP => //; last by constructor.
by move=> /[dup] ? -> /[dup] ? ->; constructor.
Qed.

End Trees.

Lemma perm_tree (T : eqType) (leT : rel T) (t : tree leT) :
  perm_eql (sort_tree t) (flatten_tree t).
Proof.
apply/permPl; elim: t => [b l IHl r IHr|[] s _] //=; rewrite ?perm_rev //.
by case: b; rewrite /= ?perm_rev perm_merge -?rev_cat ?perm_rev perm_cat.
Qed.

Definition sort_ty := forall T : Type, rel T -> seq T -> seq T.

Parametricity Recursive sort_ty.

Structure interface := Interface {
  sort_fun : forall T : Type, rel T -> seq T -> seq T;
  (* Binary parametricity *)
  (* _ : forall T1 T2 (T_R : T1 -> T2 -> Type) *)
  (*            (leT1 : rel T1) (leT2 : rel T2), *)
  (*     (forall (x1 : T1) (y1 : T2), T_R x1 y1 -> *)
  (*      forall (x2 : T1) (y2 : T2), T_R x2 y2 -> *)
  (*        bool_R (leT1 x1 x2) (leT2 y1 y2)) -> *)
  (*     forall (xs : seq T1) (ys : seq T2), *)
  (*       list_R T_R xs ys -> *)
  (*       list_R T_R (sort_fun leT1 xs) (sort_fun leT2 ys); *)
  _ : sort_ty_R sort_fun sort_fun;
  (* Characterization by binary trees *)
  _ : forall (T : Type) (leT : rel T) (s : seq T),
        {t : tree leT | s = flatten_tree t & sort_fun leT s = sort_tree t } }.

Module Exports.
Arguments leaf_tree {T leT} b s _.
Arguments empty_tree {T leT}.
Arguments flatten_tree {T leT} t.
Arguments sort_tree {T leT} t.
Arguments Interface sort_fun _ _ : clear implicits.
Notation stableSort := interface.
Notation StableSort := Interface.
Coercion sort_fun : interface >-> Funclass.
End Exports.

End StableSort.
Export StableSort.Exports.

(******************************************************************************)
(* Insertion sort                                                             *)
(******************************************************************************)

Module Insertion.
Section Insertion.

Variables (T : Type) (leT : rel T).

Definition sort := foldr (fun x => merge leT [:: x]) [::].

Import StableSort.

Lemma sortP (s : seq T) :
  {t : tree leT | s = flatten_tree t & sort s = sort_tree t}.
Proof.
elim: s => [|x _ [t -> /= ->]]; first by exists empty_tree.
by exists (branch_tree true (leaf_tree true [:: x] erefl) t).
Qed.

End Insertion.

Parametricity Recursive sort.

Definition sort_stable := StableSort.Interface sort sort_R sortP.

End Insertion.

Canonical Insertion.sort_stable.

(******************************************************************************)
(* [path.sort] of MathComp                                                    *)
(******************************************************************************)

Module NaiveMergesort.
Section NaiveMergesort.

Variable (T : Type) (leT : rel T).

Import StableSort.

Let flatten_stack := foldr (fun x => cat^~ (@flatten_tree _ leT x)) nil.

Lemma merge_sort_pushP (t : tree leT) (stack : seq (tree leT)) :
  {stack' : seq (tree leT) |
    flatten_stack (t :: stack) = flatten_stack stack' &
    merge_sort_push leT (sort_tree t) (map sort_tree stack) =
    map sort_tree stack'}.
Proof.
elim: stack t => [|t' stack IHstack] t /=; first by exists [:: t].
rewrite ifnilE -catA; case: tree_nilP => _ _.
  by exists (t :: stack); rewrite //= cats0.
case: (IHstack (branch_tree true t' t)) => /= {IHstack}stack -> ->.
by exists (empty_tree :: stack); rewrite //= cats0.
Qed.

Lemma merge_sort_popP (t : tree leT) (stack : seq (tree leT)) :
  {t' : tree leT |
    flatten_stack (t :: stack) = flatten_tree t' &
    merge_sort_pop leT (sort_tree t) (map sort_tree stack) = sort_tree t'}.
Proof.
elim: stack t => [|t' stack IHstack] t; first by exists t; rewrite //= cats0.
case: (IHstack (branch_tree true t' t)) => t''.
by rewrite /= catA => -> ->; exists t''.
Qed.

Lemma sortP (s : seq T) :
  {t : tree leT | s = flatten_tree t & sort leT s = sort_tree t}.
Proof.
rewrite sortE.
have {1}->: s = flatten_stack [::] ++ s by [].
have ->: [::] = map (@sort_tree _ leT) [::] by [].
elim: s [::] => [|x s IHs] stack /=; first exact: merge_sort_popP empty_tree _.
case: (merge_sort_pushP (leaf_tree true [:: x] erefl) stack).
by rewrite (catA _ [:: _]) => {}stack /= -> ->; exact: IHs.
Qed.

End NaiveMergesort.

Parametricity Recursive sort.

Definition sort_stable := StableSort.Interface sort sort_R sortP.

End NaiveMergesort.

Canonical NaiveMergesort.sort_stable.

(******************************************************************************)
(* [CBN.sort] is a variant of mergesort optimized for the call-by-need        *)
(* evaluation, which is:                                                      *)
(* - bottom up,                                                               *)
(* - structurally recursive (as in [path.sort] of MathComp),                  *)
(* - reusing sorted slices (as in [Data.List.sort] of GHC), and               *)
(* - not tail recursive.                                                      *)
(* This algorithm is basically the same as [path.sort] of MathComp except     *)
(* that it reuses sorted slices. In the call-by-need evaluation, this         *)
(* algorithm should allow us to take the first few elements of the output     *)
(* without computing the rest of the output, so that it is O(n) time          *)
(* complexity. However, non-tail-recursive merge linearly consumes the stack  *)
(* in the call-by-value evaluation.                                           *)
(******************************************************************************)

Module CBN.
Section CBN.

Variables (T : Type) (leT : rel T).

Let condrev (r : bool) (s : seq T) : seq T := if r then rev s else s.

(*
Fixpoint merge_sort_push s stack :=
  match stack with
  | [::] :: stack' | [::] as stack' => s :: stack'
  | s' :: stack' => [::] :: merge_sort_push (merge leT s' s) stack'
  end.

Fixpoint merge_sort_pop s1 stack :=
  if stack is s2 :: stack' then merge_sort_pop (merge leT s2 s1) stack' else s1.
*)

Fixpoint merge_sort_rec (stack : seq (seq T)) x s :=
  let inner_rec := fix inner_rec mode acc x s :=
    if s is y :: s then
      if eqb (leT x y) mode then
        inner_rec mode (x :: acc) y s
      else
        let stack := merge_sort_push leT (condrev mode (x :: acc)) stack in
        merge_sort_rec stack y s
    else
      merge_sort_pop leT (condrev mode (x :: acc)) stack
  in
  if s is y :: s then
    inner_rec (leT x y) [:: x] y s else merge_sort_pop leT [:: x] stack.

Definition sort s := if s is x :: s then merge_sort_rec [::] x s else [::].

(* Proofs *)

Import StableSort.

Let flatten_stack := foldr (fun x => cat^~ (@flatten_tree _ leT x)) nil.

Let merge_sort_pushP := @NaiveMergesort.merge_sort_pushP T leT.
Let merge_sort_popP := @NaiveMergesort.merge_sort_popP T leT.

Lemma sortP (s : seq T) :
  {t : tree leT | s = flatten_tree t & sort s = sort_tree t}.
Proof.
case: s => /= [|x s]; first by exists empty_tree.
have {1}->: x :: s = flatten_stack [::] ++ x :: s by [].
have ->: [::] = map (@sort_tree _ leT) [::] by [].
move: [::] x s; fix IHs 3 => stack x [|y s] /=.
  exact: merge_sort_popP (leaf_tree true [:: x] erefl) _.
set lexy := leT x y.
have: path (fun y x => leT x y == lexy) y [:: x] by rewrite /= eqxx.
have ->: [:: x, y & s] = rev [:: y; x] ++ s by [].
elim: s (lexy) (y) [:: x] => {lexy x y} => [|y s IHs'] ord x acc.
  rewrite -/(sorted _ (_ :: _)) -rev_sorted cats0 => sorted_acc.
  case: (merge_sort_popP (leaf_tree ord _ sorted_acc) stack) => /= t ->.
  by rewrite /= revK => ->; exists t.
rewrite -[eqb _ _]/(_ == _); case: eqVneq => lexy.
  move=> path_acc.
  have: path (fun y x => leT x y == ord) y (x :: acc)  by rewrite /= lexy eqxx.
  by case/IHs' => {path_acc} t; rewrite -cat_rcons -rev_cons => -> ->; exists t.
rewrite -/(sorted _ (_ :: _)) -rev_sorted => sorted_acc.
case: (merge_sort_pushP (leaf_tree ord _ sorted_acc) stack) => stack'.
by rewrite /= catA revK => -> ->; apply: IHs.
Qed.

End CBN.

Parametricity Recursive sort.

Definition sort_stable := StableSort.Interface sort sort_R sortP.

End CBN.

Canonical CBN.sort_stable.

(******************************************************************************)
(* [CBV.sort] is a variant of mergesort optimized for the call-by-value       *)
(* evaluation, which is:                                                      *)
(* - bottom up,                                                               *)
(* - structurally recursive (as in [path.sort] of MathComp),                  *)
(* - reusing sorted slices (as in [Data.List.sort] of GHC), and               *)
(* - tail recursive (as in List.stable_sort of OCaml).                        *)
(* This algorithm is similar to above [CBN.sort] except that the merging      *)
(* function [revmerge] is tail-recursive and puts its result in the reverse   *)
(* order. Merging with the converse relation of [leT] allows us to merge two  *)
(* lists of the reverse order without taking their reversals (see, e.g., the  *)
(* last case of [merge_sort_push]). Also, the push/pop trick of [path.sort]   *)
(* allows us to implement a bottom-up mergesort algorithm with only O(log n)  *)
(* stack consumption. However, this algorithm forces us to compute the output *)
(* almost entirely, which may be undesirable in the call-by-need evaluation.  *)
(******************************************************************************)

Module CBV.
Section CBV.

Fixpoint revmerge T (leT : rel T) (xs : seq T) : seq T -> seq T -> seq T :=
  if xs is x :: xs'
  then fix revmerge' (ys acc : seq T) :=
         if ys is y :: ys'
         then if leT x y then
                revmerge leT xs' ys (x :: acc)
              else
                revmerge' ys' (y :: acc)
         else catrev xs acc
  else catrev.

Lemma revmergeE (T : Type) (leT : rel T) (s1 s2 : seq T) :
  revmerge leT s1 s2 [::] = rev (merge leT s1 s2).
Proof.
rewrite -[RHS]cats0.
elim: s1 s2 [::] => [|x s1 IHs1]; elim=> [|y s2 IHs2] s3 //=;
  try by rewrite catrevE rev_cons cat_rcons.
by case: ifP => //= _; rewrite ?(IHs1, IHs2) rev_cons cat_rcons.
Qed.

Variables (T : Type) (leT : rel T).

Let condrev (r : bool) (s : seq T) : seq T := if r then rev s else s.

Fixpoint merge_sort_push (xs : seq T) (stack : seq (seq T)) : seq (seq T) :=
  match stack with
    | [::] :: stack' | [::] as stack' => xs :: stack'
    | ys :: [::] :: stack | ys :: ([::] as stack) =>
      [::] :: revmerge leT ys xs [::] :: stack
    | ys :: zs :: stack =>
      [::] :: [::] ::
           merge_sort_push
           (revmerge (fun x y => leT y x) (revmerge leT ys xs [::]) zs [::])
           stack
  end.

Fixpoint merge_sort_pop
         (mode : bool) (xs : seq T) (stack : seq (seq T)) : seq T :=
  match stack, mode with
    | [::], true => rev xs
    | [::], false => xs
    | [::] :: [::] :: stack, _ => merge_sort_pop mode xs stack
    | [::] :: stack, _ => merge_sort_pop (~~ mode) (rev xs) stack
    | ys :: stack, true =>
      merge_sort_pop false (revmerge (fun x y => leT y x) xs ys [::]) stack
    | ys :: stack, false =>
      merge_sort_pop true (revmerge leT ys xs [::]) stack
  end.

Fixpoint merge_sort_rec (stack : seq (seq T)) (x : T) (s : seq T) : seq T :=
  let inner_rec := fix inner_rec mode acc x s :=
    if s is y :: s then
      if eqb (leT x y) mode then
        inner_rec mode (x :: acc) y s
      else
        let stack := merge_sort_push (condrev mode (x :: acc)) stack in
        merge_sort_rec stack y s
    else
      merge_sort_pop false (condrev mode (x :: acc)) stack
  in
  if s is y :: s then
    inner_rec (leT x y) [:: x] y s else merge_sort_pop false [:: x] stack.

Definition sort s : seq T :=
  if s is x :: s then merge_sort_rec [::] x s else [::].

(* Proofs *)

Import StableSort.

Let flatten_stack := foldr (fun x => cat^~ (@flatten_tree _ leT x)) nil.

Let Fixpoint sort_stack (mode : bool) (stack : seq (tree leT)) : seq (seq T) :=
  if stack isn't t :: stack then [::] else
    condrev mode (sort_tree t) :: sort_stack (~~ mode) stack.

Let merge_sort_pushP (t : tree leT) (stack : seq (tree leT)) :
  {stack' : seq (tree leT) |
    flatten_stack (t :: stack) = flatten_stack stack' &
    merge_sort_push (sort_tree t) (sort_stack false stack)
    = sort_stack false stack'}.
Proof.
move: t stack; fix IHstack 2; move=> t [|t' [|t'' stack]] /=.
- by exists [:: t].
- rewrite !revmergeE ifnilE tree_nilp; have [->|_] := nilP.
    by exists [:: t].
  by exists [:: empty_tree; branch_tree true t' t]; rewrite //= cats0.
- rewrite !revmergeE !ifnilE nilp_rev !tree_nilp; have [->|_] := nilP.
    by exists [:: t, t'' & stack]; rewrite ?cats0.
  rewrite -!catA; have [->|_] := nilP.
    by exists [:: empty_tree, branch_tree true t' t & stack]; rewrite /= ?cats0.
  have [/= {}stack -> ->] :=
    IHstack (branch_tree false t'' (branch_tree true t' t)) stack.
  by exists [:: empty_tree, empty_tree & stack]; rewrite /= ?cats0.
Qed.

Lemma nilp_condrev (r : bool) (s : seq T) : nilp (condrev r s) = nilp s.
Proof. by case: r; rewrite ?nilp_rev. Qed.

Let merge_sort_popP (mode : bool) (t : tree leT) (stack : seq (tree leT)) :
  {t' : tree leT |
    flatten_stack stack ++ flatten_tree t = flatten_tree t' &
    merge_sort_pop mode (condrev mode (sort_tree t)) (sort_stack mode stack)
    = sort_tree t'}.
Proof.
move: mode t stack; fix IHstack 3; move=> mode t [|t' stack] /=.
  by exists t => //; case: mode; rewrite ?revK.
rewrite -catA !revmergeE ifnilE nilp_condrev.
case: tree_nilP => _ _; last first.
  by case: mode (IHstack (~~ mode) (branch_tree (~~ mode) t' t) stack).
case: stack => [|t'' stack] /=.
  by exists t => //; case: mode; rewrite ?revK.
rewrite !revmergeE !ifnilE !nilp_condrev !negbK revK.
case: tree_nilP => _ _; first by rewrite cats0; apply: IHstack.
rewrite -catA.
by case: mode (IHstack mode (branch_tree mode t'' t) stack); rewrite //= revK.
Qed.

Lemma sortP (s : seq T) :
  {t : tree leT | s = flatten_tree t & sort s = sort_tree t}.
Proof.
case: s => /= [|x s]; first by exists empty_tree.
have {1}->: x :: s = flatten_stack [::] ++ x :: s by [].
have ->: [::] = sort_stack false [::] by [].
move: [::] x s; fix IHs 3 => stack x [|y s] /=.
  exact: merge_sort_popP (leaf_tree true [:: x] erefl) _.
set lexy := leT x y.
have: path (fun y x => leT x y == lexy) y [:: x] by rewrite /= eqxx.
have ->: [:: x, y & s] = rev [:: y; x] ++ s by [].
elim: s (lexy) (y) [:: x] => {lexy x y} => [|y s IHs'] ord x acc.
  rewrite -/(sorted _ (_ :: _)) -rev_sorted cats0 => sorted_acc.
  case: (merge_sort_popP false (leaf_tree ord _ sorted_acc) stack) => t ->.
  by rewrite /= revK => ->; exists t.
rewrite -[eqb _ _]/(_ == _); case: eqVneq => lexy.
  move=> path_acc.
  have: path (fun y x => leT x y == ord) y (x :: acc) by rewrite /= lexy eqxx.
  by case/IHs' => {path_acc} t; rewrite -cat_rcons -rev_cons => -> ->; exists t.
rewrite -/(sorted _ (_ :: _)) -rev_sorted => sorted_acc.
case: (merge_sort_pushP (leaf_tree ord _ sorted_acc) stack) => stack'.
by rewrite /= catA revK => -> ->; apply: IHs.
Qed.

End CBV.

Parametricity Recursive sort.

Definition sort_stable := StableSort.Interface sort sort_R sortP.

End CBV.

Canonical CBV.sort_stable.

(******************************************************************************)
(* Theory of stable sort functions                                            *)
(******************************************************************************)

Section StableSortTheory.

Variable (sort : stableSort).

Local Lemma param_sort : StableSort.sort_ty_R sort sort.
Proof. by case: sort => ? param ?; exact: param. Qed.

Lemma map_sort (T T' : Type) (f : T' -> T) (leT' : rel T') (leT : rel T) :
  {mono f : x y / leT' x y >-> leT x y} ->
  {morph map f : s1 / sort _ leT' s1 >-> sort _ leT s1}.
Proof.
move=> leT_mono xs; apply/esym/rel_map_map/param_sort/map_rel_map.
by move=> ? ? <- ? ? <-; apply/bool_R_refl/esym/leT_mono.
Qed.

Lemma sort_map (T T' : Type) (f : T' -> T) (leT : rel T) (s : seq T') :
  sort _ leT (map f s) = map f (sort _ (relpre f leT) s).
Proof. exact/esym/map_sort. Qed.

Section SortSeq.

Variable (T : Type) (P : {pred T}) (leT : rel T).

Variant sort_spec : seq T -> seq T -> Type :=
  SortSpec (t : StableSort.tree leT) :
    sort_spec (StableSort.flatten_tree t) (StableSort.sort_tree t).

Local Lemma sortP (s : seq T) : sort_spec s (sort _ leT s).
Proof.
by case: sort => ? ? sortP; case: (sortP _ leT s) => t -> /= ->; constructor.
Qed.

Lemma all_sort (s : seq T) : all P (sort _ leT s) = all P s.
Proof. by case: sortP; exact: StableSort.all_tree. Qed.

Lemma size_sort (s : seq T) : size (sort _ leT s) = size s.
Proof. case: sortP; exact: StableSort.size_tree. Qed.

Lemma sort_nil : sort _ leT [::] = [::].
Proof. by case: (sort _) (size_sort [::]). Qed.

Lemma pairwise_sort (s : seq T) : pairwise leT s -> sort _ leT s = s.
Proof.
case: {s}sortP; elim=> [b l IHl r IHr|[] s] //=; last first.
  by case: s => [|x[|y s]] //=; case: leT.
rewrite pairwise_cat => /and3P[hlr /IHl -> /IHr ->].
rewrite !allrel_merge ?rev_cat ?revK //; first by case: b.
by rewrite /allrel all_rev [all _ _]allrelC /allrel all_rev.
Qed.

Lemma sorted_sort :
  transitive leT -> forall s : seq T, sorted leT s -> sort _ leT s = s.
Proof. by move=> leT_tr s; rewrite sorted_pairwise //; apply/pairwise_sort. Qed.

End SortSeq.

Lemma sorted_sort_in (T : Type) (P : {pred T}) (leT : rel T) :
  {in P & &, transitive leT} ->
  forall s : seq T, all P s -> sorted leT s -> sort _ leT s = s.
Proof.
move=> /in3_sig ? s /all_sigP[? ->].
by rewrite sort_map sorted_map => /sorted_sort->.
Qed.

Section EqSortSeq.

Variables (T : eqType) (leT : rel T).

Lemma perm_sort (s : seq T) : perm_eql (sort _ leT s) s.
Proof. by case: sortP; exact: StableSort.perm_tree. Qed.

Lemma mem_sort (s : seq T) : sort _ leT s =i s.
Proof. exact/perm_mem/permPl/perm_sort. Qed.

Lemma sort_uniq (s : seq T) : uniq (sort _ leT s) = uniq s.
Proof. exact/perm_uniq/permPl/perm_sort. Qed.

End EqSortSeq.

Lemma sort_pairwise_stable (T : Type) (leT leT' : rel T) :
  total leT -> forall s : seq T, pairwise leT' s ->
  sorted [rel x y | leT x y && (leT y x ==> leT' x y)] (sort _ leT s).
Proof.
move=> leT_total s; case: {s}sortP; elim=> [b l IHl r IHr|b s] /=.
  rewrite ?pairwise_cat => /and3P[hlr /IHl ? /IHr ?].
  case: b; rewrite ?(rev_sorted, merge_stable_sorted) //=;
    do 2 rewrite /allrel ?all_rev StableSort.all_tree [all _ _]allrelC //.
  by rewrite allrelC.
move=> sorted_s1 /pairwise_sorted /(conj sorted_s1) /andP.
case: (b); rewrite sorted_relI ?rev_sorted;
  apply: sub_sorted => x y /= /andP[/eqP xy xy']; rewrite ?xy ?xy' ?implybT //.
by case: (leT _ _) xy (leT_total x y) => //= _ ->.
Qed.

Lemma sort_pairwise_stable_in (T : Type) (P : {pred T}) (leT leT' : rel T) :
  {in P &, total leT} -> forall s : seq T, all P s -> pairwise leT' s ->
  sorted [rel x y | leT x y && (leT y x ==> leT' x y)] (sort _ leT s).
Proof.
move=> /in2_sig leT_total _ /all_sigP[s ->].
by rewrite sort_map pairwise_map sorted_map; apply: sort_pairwise_stable.
Qed.

Lemma sort_stable (T : Type) (leT leT' : rel T) :
  total leT -> transitive leT' -> forall s : seq T, sorted leT' s ->
  sorted [rel x y | leT x y && (leT y x ==> leT' x y)] (sort _ leT s).
Proof.
move=> leT_total leT'_tr s; rewrite sorted_pairwise //.
exact: sort_pairwise_stable.
Qed.

Lemma sort_stable_in (T : Type) (P : {pred T}) (leT leT' : rel T) :
  {in P &, total leT} -> {in P & &, transitive leT'} ->
  forall s : seq T, all P s -> sorted leT' s ->
  sorted [rel x y | leT x y && (leT y x ==> leT' x y)] (sort _ leT s).
Proof.
move=> /in2_sig leT_total /in3_sig leT_tr _ /all_sigP[s ->].
by rewrite sort_map !sorted_map; apply: sort_stable.
Qed.

Lemma sort_sorted (T : Type) (leT : rel T) :
  total leT -> forall s : seq T, sorted leT (sort _ leT s).
Proof.
move=> leT_total s; apply/sub_sorted/sort_stable => //= [? ? /andP[] //|].
by case: s => // x s; elim: s x => /=.
Qed.

Lemma sort_sorted_in (T : Type) (P : {pred T}) (leT : rel T) :
  {in P &, total leT} -> forall s : seq T, all P s -> sorted leT (sort _ leT s).
Proof.
by move=> /in2_sig ? s /all_sigP[? ->]; rewrite sort_map sorted_map sort_sorted.
Qed.

Lemma filter_sort (T : Type) (leT : rel T) :
  total leT -> transitive leT ->
  forall (p : pred T) (s : seq T),
    filter p (sort _ leT s) = sort _ leT (filter p s).
Proof.
move=> leT_total leT_tr p s; case Ds: s => [|x s1]; first by rewrite sort_nil.
pose leN := relpre (nth x s) leT.
pose lt_lex := [rel n m | leN n m && (leN m n ==> (n < m))].
have lt_lex_tr: transitive lt_lex.
  rewrite /lt_lex /leN => ? ? ? /= /andP [xy xy'] /andP [yz yz'].
  rewrite (leT_tr _ _ _ xy yz); apply/implyP => zx; move: xy' yz'.
  by rewrite (leT_tr _ _ _ yz zx) (leT_tr _ _ _ zx xy); apply: ltn_trans.
rewrite -{s1}Ds -(mkseq_nth x s) !(filter_map, sort_map); congr map.
apply/(@irr_sorted_eq _ lt_lex); rewrite /lt_lex /leN //=.
- by move=> ?; rewrite /= ltnn implybF andbN.
- exact/sorted_filter/sort_stable/iota_ltn_sorted/ltn_trans.
- exact/sort_stable/sorted_filter/iota_ltn_sorted/ltn_trans/ltn_trans.
- by move=> ?; rewrite !(mem_filter, mem_sort).
Qed.

Lemma filter_sort_in (T : Type) (P : {pred T}) (leT : rel T) :
  {in P &, total leT} -> {in P & &, transitive leT} ->
  forall (p : pred T) (s : seq T),
    all P s -> filter p (sort _ leT s) = sort _ leT (filter p s).
Proof.
move=> /in2_sig leT_total /in3_sig leT_tr p _ /all_sigP[s ->].
by rewrite !(sort_map, filter_map) filter_sort.
Qed.

Lemma perm_sortP (T : eqType) (leT : rel T) :
  total leT -> transitive leT -> antisymmetric leT ->
  forall s1 s2, reflect (sort _ leT s1 = sort _ leT s2) (perm_eq s1 s2).
Proof.
move=> leT_total leT_tr leT_asym s1 s2.
apply: (iffP idP) => eq12; last by rewrite -(perm_sort leT) eq12 perm_sort.
apply: (sorted_eq leT_tr leT_asym); rewrite ?sort_sorted //.
by rewrite perm_sort (permPl eq12) -(perm_sort leT).
Qed.

Lemma perm_sort_inP (T : eqType) (leT : rel T) (s1 s2 : seq T) :
  {in s1 &, total leT} -> {in s1 & &, transitive leT} ->
  {in s1 &, antisymmetric leT} ->
  reflect (sort _ leT s1 = sort _ leT s2) (perm_eq s1 s2).
Proof.
move=> /in2_sig leT_total /in3_sig leT_tr /in2_sig/(_ _ _ _)/val_inj leT_asym.
apply: (iffP idP) => s1s2; last by rewrite -(perm_sort leT) s1s2 perm_sort.
move: (s1s2); have /all_sigP[s1' ->] := allss s1.
have /all_sigP[{s1s2}s2 ->] : all (mem s1) s2 by rewrite -(perm_all _ s1s2).
by rewrite !sort_map => /(perm_map_inj val_inj) /(perm_sortP leT_total)->.
Qed.

End StableSortTheory.

Arguments map_sort                sort {T T' f leT' leT} _ _.
Arguments sort_map                sort {T T' f leT} s.
Arguments all_sort                sort {T} P leT s.
Arguments size_sort               sort {T} leT s.
Arguments sort_nil                sort {T} leT.
Arguments pairwise_sort           sort {T leT s} _.
Arguments sorted_sort             sort {T leT} leT_tr {s} _.
Arguments sorted_sort_in          sort {T P leT} leT_tr {s} _ _.
Arguments perm_sort               sort {T} leT s _.
Arguments mem_sort                sort {T} leT s _.
Arguments sort_uniq               sort {T} leT s.
Arguments sort_pairwise_stable    sort {T leT leT'} leT_total {s} _.
Arguments sort_pairwise_stable_in sort {T P leT leT'} leT_total {s} _ _.
Arguments sort_stable             sort {T leT leT'} leT_total leT'_tr {s} _.
Arguments sort_stable_in          sort {T P leT leT'} leT_total leT'_tr {s} _ _.
Arguments sort_sorted             sort {T leT} leT_total s.
Arguments sort_sorted_in          sort {T P leT} leT_total {s} _.
Arguments filter_sort             sort {T leT} leT_total leT_tr p s.
Arguments filter_sort_in          sort {T P leT} leT_total leT_tr p {s} _.
Arguments perm_sortP              sort {T leT} leT_total leT_tr leT_asym s1 s2.
Arguments perm_sort_inP           sort {T leT s1 s2} leT_total leT_tr leT_asym.

Section StableSortTheory.

Lemma eq_sort (sort1 sort2 : stableSort) (T : Type) (leT : rel T) :
  total leT -> transitive leT -> sort1 _ leT =1 sort2 _ leT.
Proof.
move=> leT_total leT_tr s; case Ds: s => [|x s1]; first by rewrite !sort_nil.
pose leN := relpre (nth x s) leT.
pose lt_lex := [rel n m | leN n m && (leN m n ==> (n < m))].
have lt_lex_tr: transitive lt_lex.
  rewrite /lt_lex /leN => ? ? ? /= /andP [xy xy'] /andP [yz yz'].
  rewrite (leT_tr _ _ _ xy yz); apply/implyP => zx; move: xy' yz'.
  by rewrite (leT_tr _ _ _ yz zx) (leT_tr _ _ _ zx xy); apply: ltn_trans.
rewrite -{s1}Ds -(mkseq_nth x s) !(filter_map, sort_map); congr map.
apply/(@irr_sorted_eq _ lt_lex); rewrite /lt_lex /leN //=.
- by move=> ?; rewrite /= ltnn implybF andbN.
- exact/sort_stable/iota_ltn_sorted/ltn_trans.
- exact/sort_stable/iota_ltn_sorted/ltn_trans.
- by move=> ?; rewrite !mem_sort.
Qed.

Lemma eq_in_sort
      (sort1 sort2 : stableSort) (T : Type) (P : {pred T}) (leT : rel T) :
  {in P &, total leT} -> {in P & &, transitive leT} ->
  forall s, all P s -> sort1 _ leT s = sort2 _ leT s.
Proof.
move=> /in2_sig ? /in3_sig ? s /all_sigP[{}s ->].
by rewrite !sort_map; congr map; exact: eq_sort.
Qed.

Variable (sort : stableSort).

Section Stability.

Variables (T : Type) (leT : rel T).
Variables (leT_total : total leT) (leT_tr : transitive leT).

Lemma eq_sort_insert : sort _ leT =1 Insertion.sort leT.
Proof. exact: eq_sort. Qed.

Lemma sort_cat (s1 s2 : seq T) :
  sort _ leT (s1 ++ s2) = merge leT (sort _ leT s1) (sort _ leT s2).
Proof. by rewrite !eq_sort_insert; elim: s1 => //= x s1 ->; rewrite mergeA. Qed.

Lemma mask_sort (s : seq T) (m : bitseq) :
  {m_s : bitseq | mask m_s (sort _ leT s) = sort _ leT (mask m s)}.
Proof.
case Ds: {-}s => [|x s1]; first by exists [::]; rewrite Ds mask0 sort_nil.
rewrite -(mkseq_nth x s) -map_mask !sort_map.
exists [seq i \in mask m (iota 0 (size s)) |
            i <- sort _ (xrelpre (nth x s) leT) (iota 0 (size s))].
rewrite -map_mask -filter_mask [in RHS]mask_filter ?iota_uniq ?filter_sort //.
by move=> ? ? ?; exact: leT_tr.
Qed.

Lemma sorted_mask_sort (s : seq T) (m : bitseq) :
  sorted leT (mask m s) -> {m_s : bitseq | mask m_s (sort _ leT s) = mask m s}.
Proof. by move/(sorted_sort sort leT_tr) <-; exact: mask_sort. Qed.

End Stability.

Section Stability_in.

Variables (T : Type) (P : {pred T}) (leT : rel T).
Hypothesis leT_total : {in P &, total leT}.
Hypothesis leT_tr : {in P & &, transitive leT}.

Let le_sT := relpre (val : sig P -> _) leT.
Let le_sT_total : total le_sT := in2_sig leT_total.
Let le_sT_tr : transitive le_sT := in3_sig leT_tr.

Lemma eq_in_sort_insert (s : seq T) :
  all P s -> sort _ leT s = Insertion.sort leT s.
Proof. exact: eq_in_sort. Qed.

Lemma sort_cat_in (s1 s2 : seq T) : all P s1 -> all P s2 ->
  sort _ leT (s1 ++ s2) = merge leT (sort _ leT s1) (sort _ leT s2).
Proof.
move=> /all_sigP [{}s1 ->] /all_sigP [{}s2 ->].
by rewrite -map_cat !sort_map merge_map; congr map; apply: sort_cat.
Qed.

Lemma mask_sort_in (s : seq T) (m : bitseq) :
  all P s -> {m_s : bitseq | mask m_s (sort _ leT s) = sort _ leT (mask m s)}.
Proof.
move=> /all_sigP [{}s ->]; case: (mask_sort (leT := le_sT) _ _ s m) => //.
by move=> m' m'E; exists m'; rewrite -map_mask !sort_map -map_mask m'E.
Qed.

Lemma sorted_mask_sort_in (s : seq T) (m : bitseq) :
  all P s -> sorted leT (mask m s) ->
  {m_s : bitseq | mask m_s (sort _ leT s) = mask m s}.
Proof.
move=> ? /(sorted_sort_in sort leT_tr _) <-; last exact: all_mask.
exact: mask_sort_in.
Qed.

End Stability_in.

Section Stability_subseq.

Variables (T : eqType) (leT : rel T).
Variables (leT_total : total leT) (leT_tr : transitive leT).

Lemma subseq_sort : {homo sort _ leT : t s / subseq t s}.
Proof.
move=> _ s /subseqP [m _ ->].
have [m' <-] := mask_sort leT_total leT_tr s m; exact: mask_subseq.
Qed.

Lemma sorted_subseq_sort (t s : seq T) :
  subseq t s -> sorted leT t -> subseq t (sort _ leT s).
Proof.
by move=> subseq_ts /(sorted_sort sort leT_tr) <-; exact: subseq_sort.
Qed.

Lemma mem2_sort (s : seq T) (x y : T) :
    leT x y -> mem2 s x y -> mem2 (sort _ leT s) x y.
Proof.
move=> lexy; rewrite !mem2E => /subseq_sort; rewrite !eq_sort_insert //.
by case: (_ == _); rewrite //= lexy.
Qed.

End Stability_subseq.

Section Stability_subseq_in.

Variables (T : eqType) (leT : rel T).

Lemma subseq_sort_in (t s : seq T) :
  {in s &, total leT} -> {in s & &, transitive leT} ->
  subseq t s -> subseq (sort _ leT t) (sort _ leT s).
Proof.
move=> leT_total leT_tr /subseqP [m _ ->].
have [m' <-] := mask_sort_in leT_total leT_tr m (allss _); exact: mask_subseq.
Qed.

Lemma sorted_subseq_sort_in (t s : seq T) :
  {in s &, total leT} -> {in s & &, transitive leT} ->
  subseq t s -> sorted leT t -> subseq t (sort _ leT s).
Proof.
move=> ? leT_tr ? /(sorted_sort_in sort leT_tr) <-; last exact/allP/mem_subseq.
exact: subseq_sort_in.
Qed.

Lemma mem2_sort_in (s : seq T) :
  {in s &, total leT} -> {in s & &, transitive leT} ->
  forall x y, leT x y -> mem2 s x y -> mem2 (sort _ leT s) x y.
Proof.
move=> leT_total leT_tr x y lexy; rewrite !mem2E.
move=> /[dup] /mem_subseq /allP ? /subseq_sort_in.
rewrite !(eq_in_sort_insert leT_total leT_tr) //.
by case: (_ == _); rewrite /= ?lexy; apply.
Qed.

End Stability_subseq_in.

End StableSortTheory.

Arguments eq_sort                 sort1 sort2 {T leT} leT_total leT_tr _.
Arguments eq_in_sort              sort1 sort2 {T P leT} leT_total leT_tr {s} _.
Arguments eq_sort_insert          sort {T leT} leT_total leT_tr _.
Arguments sort_cat                sort {T leT} leT_total leT_tr s1 s2.
Arguments mask_sort               sort {T leT} leT_total leT_tr s m.
Arguments sorted_mask_sort        sort {T leT} leT_total leT_tr {s m} _.
Arguments eq_in_sort_insert       sort {T P leT} leT_total leT_tr {s} _.
Arguments sort_cat_in             sort {T P leT} leT_total leT_tr {s1 s2} _ _.
Arguments mask_sort_in            sort {T P leT} leT_total leT_tr {s} m _.
Arguments sorted_mask_sort_in     sort {T P leT} leT_total leT_tr {s m} _ _.
Arguments subseq_sort             sort {T leT} leT_total leT_tr {x y} _.
Arguments sorted_subseq_sort      sort {T leT} leT_total leT_tr {t s} _ _.
Arguments mem2_sort               sort {T leT} leT_total leT_tr {s x y} _ _.
Arguments subseq_sort_in          sort {T leT t s} leT_total leT_tr _.
Arguments sorted_subseq_sort_in   sort {T leT t s} leT_total leT_tr _ _.
Arguments mem2_sort_in            sort {T leT s} leT_total leT_tr x y _ _.
