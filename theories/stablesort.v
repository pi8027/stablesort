From stablesort Require Import mathcomp_ext.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From stablesort Require Import param.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* COMPATIBILITY HACK: [mathcomp_ext] has to be imported *before* MathComp    *)
(* libraries since [pairwise] has to be imported from MathComp if available.  *)
(* However, [eq_sorted] has to be imported from [mathcomp_ext] to override a  *)
(* deprecation alias in MathComp; hence, we declare the following notation.   *)
Local Notation eq_sorted := mathcomp_ext.eq_sorted (only parsing).

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

Parametricity sort_ty.

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
(* Merge functions                                                            *)
(******************************************************************************)

Module MergeR.
Definition merge_ty := forall (T : Type) (leT : rel T), seq T -> seq T -> seq T.
Parametricity merge_ty.
End MergeR.

Module Type MergeSig.
Import MergeR.
Parameter merge : forall (T : Type) (leT : rel T), seq T -> seq T -> seq T.
Parameter mergeE : forall (T : Type) (leT : rel T), merge leT =2 path.merge leT.
Parameter merge_R : merge_ty_R merge merge.
End MergeSig.

Module Type RevmergeSig.
Import MergeR.
Parameter revmerge : forall (T : Type) (leT : rel T), seq T -> seq T -> seq T.
Parameter revmergeE : forall (T : Type) (leT : rel T) (xs ys : seq T),
    revmerge leT xs ys = rev (path.merge leT xs ys).
Parameter revmerge_R : merge_ty_R revmerge revmerge.
End RevmergeSig.

Module Merge <: MergeSig.

Fixpoint merge (T : Type) (leT : rel T) (xs ys : seq T) :=
  if xs is x :: xs' then
    (fix merge' ys :=
       if ys is y :: ys' then
         if leT x y then x :: merge leT xs' ys else y :: merge' ys'
       else xs) ys
  else ys.

Lemma mergeE (T : Type) (leT : rel T) : merge leT =2 path.merge leT.
Proof. by elim=> // x xs IHxs; elim=> //= y ys IHys; rewrite IHxs IHys. Qed.

Parametricity merge.

End Merge.

Module MergeAcc <: MergeSig.

Definition mergeord {T : Type} (p1 p2 : seq T * seq T) : Prop :=
  if p2 is (x :: xs, y :: ys) then
    (xs, y :: ys) = p1 \/ (x :: xs, ys) = p1 else False.

Fixpoint wf_mergeord (T : Type) (xs ys : seq T) : Acc mergeord (xs, ys) :=
  if xs is x :: xs' then
    (fix wf_mergeord' (ys : seq T) : Acc mergeord (x :: xs', ys) :=
       if ys is y :: ys' then
         Acc_intro
           (x :: xs', y :: ys')
           (fun _ H =>
              match H with
                | or_introl H0 =>
                  let: erefl in (_ = y1) := H0 return Acc mergeord y1 in
                  wf_mergeord xs' (y :: ys')
                | or_intror H0 =>
                  let: erefl in (_ = y1) := H0 return Acc mergeord y1 in
                  wf_mergeord' ys'
              end)
       else
         Acc_intro (x :: xs', [::]) (fun _ => False_ind _)) ys
  else
    Acc_intro ([::], ys) (fun _ => False_ind _).

Fixpoint merge_rec (T : Type) (leT : rel T)
                    (xs ys : seq T) (fuel : Acc mergeord (xs, ys)) :=
  match fuel, xs, ys return xs = _ -> ys = _ -> _ with
    | _, [::], ys => fun _ _ => ys
    | _, xs, [::] => fun _ _ => xs
    | Acc_intro fuel, x :: xs', y :: ys' =>
      fun (xsE : x :: xs' = xs) (ysE : y :: ys' = ys) =>
      if leT x y then
        x :: @merge_rec T leT xs' ys
          (fuel _ match xsE in _ = xs0, ysE in _ = ys0
                        return mergeord (xs', ys0) (xs0, ys0) with
                    erefl, erefl => or_introl erefl
                  end)
      else
        y :: @merge_rec T leT xs ys'
          (fuel _ match xsE in _ = xs0, ysE in _ = ys0
                        return mergeord (xs0, ys') (xs0, ys0) with
                    erefl, erefl => or_intror erefl
                  end)
  end erefl erefl.

Definition merge (T : Type) (leT : rel T) (xs ys : seq T) :=
  @merge_rec T leT xs ys (wf_mergeord xs ys).

Lemma mergeE (T : Type) (leT : rel T) : merge leT =2 path.merge leT.
Proof.
rewrite /merge => xs ys; move: xs ys (wf_mergeord xs ys).
by elim=> [|x xs IHxs]; elim=> [|y ys IHys] [acc] //=; rewrite IHxs IHys.
Qed.

Parametricity mergeord.
Parametricity wf_mergeord.
Parametricity merge.

End MergeAcc.

Module Revmerge <: RevmergeSig.

Fixpoint merge_rec (T : Type) (leT : rel T) (xs ys accu : seq T) : seq T :=
  if xs is x :: xs' then
    (fix merge_rec' (ys accu : seq T) :=
       if ys is y :: ys' then
         if leT x y then
           merge_rec leT xs' ys (x :: accu) else merge_rec' ys' (y :: accu)
       else
         catrev xs accu) ys accu
  else catrev ys accu.

Definition revmerge (T : Type) (leT : rel T) (xs ys : seq T) : seq T :=
  merge_rec leT xs ys [::].

Lemma revmergeE (T : Type) (leT : rel T) (xs ys : seq T) :
  revmerge leT xs ys = rev (path.merge leT xs ys).
Proof.
rewrite /revmerge -[RHS]cats0.
elim: xs ys [::] => [|x xs IHxs]; elim=> [|y ys IHys] accu //=;
  try by rewrite catrevE rev_cons cat_rcons.
by case: ifP => _; rewrite rev_cons cat_rcons.
Qed.

Parametricity revmerge.

End Revmerge.

Module RevmergeAcc <: RevmergeSig.

Import MergeAcc.

Fixpoint merge_rec (T : Type) (leT : rel T) (xs ys accu : seq T)
                   (fuel : Acc mergeord (xs, ys)) :=
  match fuel, xs, ys return xs = _ -> ys = _ -> _ with
    | _, [::], ys => fun _ _ => catrev ys accu
    | _, xs, [::] => fun _ _ => catrev xs accu
    | Acc_intro fuel, x :: xs', y :: ys' =>
      fun (xsE : x :: xs' = xs) (ysE : y :: ys' = ys) =>
      if leT x y then
        @merge_rec T leT xs' ys (x :: accu)
          (fuel _ match xsE in _ = xs0, ysE in _ = ys0
                        return mergeord (xs', ys0) (xs0, ys0) with
                    erefl, erefl => or_introl erefl
                  end)
      else
        @merge_rec T leT xs ys' (y :: accu)
          (fuel _ match xsE in _ = xs0, ysE in _ = ys0
                        return mergeord (xs0, ys') (xs0, ys0) with
                    erefl, erefl => or_intror erefl
                  end)
  end erefl erefl.

Definition revmerge (T : Type) (leT : rel T) (xs ys : seq T) :=
  @merge_rec T leT xs ys [::] (wf_mergeord xs ys).

Lemma revmergeE (T : Type) (leT : rel T) (xs ys : seq T) :
  revmerge leT xs ys = rev (path.merge leT xs ys).
Proof.
rewrite /revmerge -[RHS]cats0; move: xs ys [::] (wf_mergeord xs ys).
elim=> [|x xs IHxs]; elim=> [|y ys IHys] accu [acc] //=;
  try by rewrite catrevE rev_cons cat_rcons.
by case: ifP => _; rewrite rev_cons cat_rcons.
Qed.

Parametricity revmerge.

End RevmergeAcc.

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

Parametricity sort.

Definition sort_stable := StableSort.Interface sort sort_R sortP.

End Insertion.

Canonical Insertion.sort_stable.

(******************************************************************************)
(* The [CBN_] functor module takes a module [M] of type [MergeSig] and        *)
(* provides a family of mergesort functions [sort1], [sort2], [sort3], and    *)
(* [sortN]. These functions are bottom-up and structurally recursive and use  *)
(* [M.merge] internally for merging sorted lists.                             *)
(* The numbers [1], [2], and [3] in their names stand for the fact that they  *)
(* repeat to take a fixed-size prefix from the input, put it into the given   *)
(* order, and push it to a stack that manages the sorting process. Among      *)
(* those, [sort2] is exactly the same as [path.sort] of MathComp except that  *)
(* it is parameterized by the merge function. On the other hand, [sortN]      *)
(* takes the longest sorted prefix (in ascending or descending order) instead *)
(* of a fixed-size prefix, as in GHC's [Data.List.sort].                      *)
(* Since [M.merge] is expected to be a non-tail-recursive merge function,     *)
(* these algorithms should allow us to take the first few elements of the     *)
(* output without computing the rest of the output in the call-by-need        *)
(* evaluation, so that it is O(n) time complexity. However, the               *)
(* non-tail-recursive merge function linearly consumes the stack in the       *)
(* call-by-value evaluation, which may trigger a stack overflow.              *)
(******************************************************************************)

Module CBN_ (M : MergeSig).

Section CBN.

Variable (T : Type) (leT : rel T).

Let condrev (r : bool) (s : seq T) : seq T := if r then rev s else s.

Fixpoint merge_sort_push (s : seq T) (stack : seq (seq T)) : seq (seq T) :=
  match stack with
  | [::] :: stack' | [::] as stack' => s :: stack'
  | s' :: stack' => [::] :: merge_sort_push (M.merge leT s' s) stack'
  end.

Fixpoint merge_sort_pop (s1 : seq T) (stack : seq (seq T)) : seq T :=
  if stack is s2 :: stack' then
    merge_sort_pop (M.merge leT s2 s1) stack' else s1.

Fixpoint sort1rec (stack : seq (seq T)) (s : seq T) :=
  if s is x :: s then sort1rec (merge_sort_push [:: x] stack) s else
  merge_sort_pop [::] stack.

Definition sort1 : seq T -> seq T := sort1rec [::].

Fixpoint sort2rec (stack : seq (seq T)) (s : seq T) :=
  if s is [:: x1, x2 & s'] then
    let s1 := if leT x1 x2 then [:: x1; x2] else [:: x2; x1] in
    sort2rec (merge_sort_push s1 stack) s'
  else merge_sort_pop s stack.

Definition sort2 : seq T -> seq T := sort2rec [::].

Fixpoint sort3rec (stack : seq (seq T)) (s : seq T) :=
  match s with
    | [:: x1, x2, x3 & s'] =>
      let s1 :=
          if leT x1 x2 then
            if leT x2 x3 then [:: x1; x2; x3]
            else if leT x1 x3 then [:: x1; x3; x2] else [:: x3; x1; x2]
          else
            if leT x1 x3 then [:: x2; x1; x3]
            else if leT x2 x3 then [:: x2; x3; x1] else [:: x3; x2; x1]
      in
      sort3rec (merge_sort_push s1 stack) s'
    | [:: x1; x2] =>
      merge_sort_pop (if leT x1 x2 then s else [:: x2; x1]) stack
    | _ => merge_sort_pop s stack
  end.

Definition sort3 : seq T -> seq T := sort3rec [::].

Fixpoint sortNrec (stack : seq (seq T)) (x : T) (s : seq T) :=
  if s is y :: s then
    if leT x y then ascending stack [:: x] y s else descending stack [:: x] y s
  else
    merge_sort_pop [:: x] stack
with ascending stack acc x s :=
    if s is y :: s then
      if leT x y then
        ascending stack (x :: acc) y s
      else
        sortNrec (merge_sort_push (catrev acc [:: x]) stack) y s
    else
      merge_sort_pop (catrev acc [:: x]) stack
with descending stack acc x s :=
    if s is y :: s then
      if leT x y then
        sortNrec (merge_sort_push (x :: acc) stack) y s
      else
        descending stack (x :: acc) y s
    else
      merge_sort_pop (x :: acc) stack.

Definition sortN (s : seq T) : seq T :=
  if s is x :: s then sortNrec [::] x s else [::].

(* Proofs *)

Import StableSort.

Let flatten_stack := foldr (fun x => cat^~ (@flatten_tree _ leT x)) nil.

Lemma merge_sort_pushP (t : tree leT) (stack : seq (tree leT)) :
  {stack' : seq (tree leT) |
    flatten_stack (t :: stack) = flatten_stack stack' &
    merge_sort_push (sort_tree t) (map sort_tree stack) =
    map sort_tree stack'}.
Proof.
elim: stack t => [|t' stack IHstack] t /=; first by exists [:: t].
rewrite M.mergeE ifnilE -catA; case: tree_nilP => _ _.
  by exists (t :: stack); rewrite //= cats0.
have [/= {IHstack}stack -> ->] := IHstack (branch_tree true t' t).
by exists (empty_tree :: stack); rewrite //= cats0.
Qed.

Lemma merge_sort_popP (t : tree leT) (stack : seq (tree leT)) :
  {t' : tree leT |
    flatten_stack (t :: stack) = flatten_tree t' &
    merge_sort_pop (sort_tree t) (map sort_tree stack) = sort_tree t'}.
Proof.
elim: stack t => [|t' stack IHstack] t; first by exists t; rewrite //= cats0.
rewrite /= M.mergeE -catA.
by have [/= t'' -> ->] := IHstack (branch_tree true t' t); exists t''.
Qed.

Lemma sort1P (s : seq T) :
  {t : tree leT | s = flatten_tree t & sort1 s = sort_tree t}.
Proof.
rewrite /sort1.
have {1}->: s = flatten_stack [::] ++ s by [].
have ->: [::] = map (@sort_tree _ leT) [::] by [].
elim: s [::] => [|x s IHs] stack /=; first exact: merge_sort_popP empty_tree _.
case: (merge_sort_pushP (leaf_tree true [:: x] erefl) stack).
by rewrite (catA _ [:: _]) => {}stack /= -> ->; exact: IHs.
Qed.

Lemma sort2P (s : seq T) :
  {t : tree leT | s = flatten_tree t & sort2 s = sort_tree t}.
Proof.
rewrite /sort2.
have {1}->: s = flatten_stack [::] ++ s by [].
have ->: [::] = map (@sort_tree _ leT) [::] by [].
move: [::] s; fix IHs 2 => stack [|x [|y s]].
- exact: merge_sort_popP (leaf_tree true [::] erefl) _.
- exact: merge_sort_popP (leaf_tree true [:: x] erefl) _.
case: (merge_sort_pushP (leaf_tree (leT x y) [:: x; y] _) stack).
  by rewrite /= eqxx.
by rewrite (catA _ [:: _; _]) => /= _ {}stack -> ->; apply: IHs.
Qed.

Lemma sort3P (s : seq T) :
  {t : tree leT | s = flatten_tree t & sort3 s = sort_tree t}.
Proof.
rewrite /sort3.
have sorted2 x y : sorted (fun x' y' => leT x' y' == leT x y) [:: x; y].
  by rewrite /= eqxx.
have {1}->: s = flatten_stack [::] ++ s by [].
have ->: [::] = map (@sort_tree _ leT) [::] by [].
move: [::] s; fix IHs 2 => stack [|x [|y [|z s]]].
- exact: merge_sort_popP (leaf_tree true [::] erefl) _.
- exact: merge_sort_popP (leaf_tree true [:: x] erefl) _.
- exact: merge_sort_popP (leaf_tree (leT x y) [:: x; y] (sorted2 _ _)) _.
rewrite (catA _ [:: _; _; _]).
pose xyz : tree leT := branch_tree false
  (leaf_tree (leT x y) [:: x; y] (sorted2 _ _)) (leaf_tree true [:: z] erefl).
case: (merge_sort_pushP xyz stack) => /= stack' ->.
set push1 := merge_sort_push _ _; set push2 := merge_sort_push _ _.
have ->: push1 = push2 by congr merge_sort_push; do 3 case: ifP => //=.
by move=> ->; apply: IHs.
Qed.

Lemma sortNP (s : seq T) :
  {t : tree leT | s = flatten_tree t & sortN s = sort_tree t}.
Proof.
case: s => /= [|x s]; first by exists empty_tree.
have {1}->: x :: s = flatten_stack [::] ++ x :: s by [].
have ->: [::] = map (@sort_tree _ leT) [::] by [].
move: [::] x s; fix IHs 3 => stack x [|y s] /=.
  exact: merge_sort_popP (leaf_tree true [:: x] erefl) _.
set lexy := leT x y.
have: path (fun y x => leT x y == lexy) y [:: x] by rewrite /= eqxx.
have ->: [:: x, y & s] = rev [:: y; x] ++ s by [].
elim: s (lexy) (y) [:: x] => {lexy x y} => [|y s IHs' /=] ord x acc.
  rewrite -/(sorted _ (_ :: _)) -rev_sorted cats0 => sorted_acc.
  case: (merge_sort_popP (leaf_tree ord _ sorted_acc) stack) => /= t ->.
  by rewrite revK; case: ord {sorted_acc} => ->; exists t.
case: ord (boolP (leT x y)) => [] [] lexy.
- move=> path_acc.
  have: path (fun y x => leT x y == true) y (x :: acc) by rewrite /= lexy eqxx.
  by case/IHs' => {path_acc} t; rewrite -cat_rcons -rev_cons => -> ->; exists t.
- rewrite -/(sorted _ (_ :: _)) -rev_sorted => sorted_acc.
  case: (merge_sort_pushP (leaf_tree true _ sorted_acc) stack) => stack'.
  by rewrite /= catA => -> ->; apply: IHs.
- rewrite -/(sorted _ (_ :: _)) -rev_sorted => sorted_acc.
  case: (merge_sort_pushP (leaf_tree false _ sorted_acc) stack) => stack'.
  by rewrite /= catA revK => -> ->; apply: IHs.
- move=> path_acc.
  have: path (fun y x => leT x y == false) y (x :: acc).
    by rewrite /= eqbF_neg lexy.
  by case/IHs' => {path_acc} t; rewrite -cat_rcons -rev_cons => -> ->; exists t.
Qed.

End CBN.

Realizer M.merge as merge_R arity 2 := M.merge_R.

Parametricity merge_sort_push.
Parametricity merge_sort_pop.
Parametricity sort1.
Parametricity sort2.
Parametricity sort3.
Parametricity sortN.

Definition sort1_stable := StableSort.Interface sort1 sort1_R sort1P.
Definition sort2_stable := StableSort.Interface sort2 sort2_R sort2P.
Definition sort3_stable := StableSort.Interface sort3 sort3_R sort3P.
Definition sortN_stable := StableSort.Interface sortN sortN_R sortNP.

End CBN_.

Module CBN := CBN_(Merge).
Module CBNAcc := CBN_(MergeAcc).

Canonical CBN.sort1_stable.
Canonical CBN.sort2_stable.
Canonical CBN.sort3_stable.
Canonical CBN.sortN_stable.
Canonical CBNAcc.sort1_stable.
Canonical CBNAcc.sort2_stable.
Canonical CBNAcc.sort3_stable.
Canonical CBNAcc.sortN_stable.

(******************************************************************************)
(* The [CBV_] functor module takes a module [M] of type [RevmergeSig] and     *)
(* provides a family of mergesort functions [sort1], [sort2], [sort3], and    *)
(* [sortN]. These functions are bottom-up and structurally recursive and use  *)
(* [M.revmerge] internally for merging sorted lists. Their naming convention  *)
(* is the same as in the above [CBN_] functor module.                         *)
(* As opposed to the [M.merge] function of a [M : MergeSig], the [M.revmerge] *)
(* function puts its result in the reverse order, and is expected to be a     *)
(* tail-recursive merge function, so that it does not consume the stack       *)
(* linearly in the call-by-value evaluation. Merging with the converse        *)
(* relation of the given order [leT] allows us to merge two lists sorted in   *)
(* the reverse order without taking their reversals (see, e.g., the last case *)
(* of [merge_sort_push]). Also, the push/pop trick of [path.sort] allows us   *)
(* to implement a bottom-up mergesort algorithm with only O(log n) stack      *)
(* consumption. However, this algorithm forces us to compute the output       *)
(* almost entirely, which may be undesirable in the call-by-need evaluation.  *)
(******************************************************************************)

Module CBV_ (M : RevmergeSig).
Section CBV.

Variables (T : Type) (leT : rel T).

Let condrev (r : bool) (s : seq T) : seq T := if r then rev s else s.

Fixpoint merge_sort_push (xs : seq T) (stack : seq (seq T)) : seq (seq T) :=
  match stack with
    | [::] :: stack' | [::] as stack' => xs :: stack'
    | ys :: [::] :: stack | ys :: ([::] as stack) =>
      [::] :: M.revmerge leT ys xs :: stack
    | ys :: zs :: stack =>
      [::] :: [::] ::
           merge_sort_push
           (M.revmerge (fun x y => leT y x) (M.revmerge leT ys xs) zs) stack
  end.

Fixpoint merge_sort_pop
         (mode : bool) (xs : seq T) (stack : seq (seq T)) : seq T :=
  match stack, mode with
    | [::], true => rev xs
    | [::], false => xs
    | [::] :: [::] :: stack, _ => merge_sort_pop mode xs stack
    | [::] :: stack, _ => merge_sort_pop (~~ mode) (rev xs) stack
    | ys :: stack, true =>
      merge_sort_pop false (M.revmerge (fun x y => leT y x) xs ys) stack
    | ys :: stack, false =>
      merge_sort_pop true (M.revmerge leT ys xs) stack
  end.

Fixpoint sort1rec (stack : seq (seq T)) (s : seq T) :=
  if s is x :: s then sort1rec (merge_sort_push [:: x] stack) s else
  merge_sort_pop false [::] stack.

Definition sort1 : seq T -> seq T := sort1rec [::].

Fixpoint sort2rec ss s :=
  if s is [:: x1, x2 & s'] then
    let s1 := if leT x1 x2 then [:: x1; x2] else [:: x2; x1] in
    sort2rec (merge_sort_push s1 ss) s'
  else merge_sort_pop false s ss.

Definition sort2 : seq T -> seq T := sort2rec [::].

Fixpoint sort3rec (stack : seq (seq T)) (s : seq T) :=
  match s with
    | [:: x1, x2, x3 & s'] =>
      let s1 :=
          if leT x1 x2 then
            if leT x2 x3 then [:: x1; x2; x3]
            else if leT x1 x3 then [:: x1; x3; x2] else [:: x3; x1; x2]
          else
            if leT x1 x3 then [:: x2; x1; x3]
            else if leT x2 x3 then [:: x2; x3; x1] else [:: x3; x2; x1]
      in
      sort3rec (merge_sort_push s1 stack) s'
    | [:: x1; x2] =>
      merge_sort_pop false (if leT x1 x2 then s else [:: x2; x1]) stack
    | _ => merge_sort_pop false s stack
  end.

Definition sort3 : seq T -> seq T := sort3rec [::].

Fixpoint sortNrec (stack : seq (seq T)) (x : T) (s : seq T) : seq T :=
  if s is y :: s then
    if leT x y then ascending stack [:: x] y s else descending stack [:: x] y s
  else
    merge_sort_pop false [:: x] stack
with ascending stack acc x s :=
    if s is y :: s then
      if leT x y then
        ascending stack (x :: acc) y s
      else
        sortNrec (merge_sort_push (catrev acc [:: x]) stack) y s
    else
      merge_sort_pop false (catrev acc [:: x]) stack
with descending stack acc x s :=
    if s is y :: s then
      if leT x y then
        sortNrec (merge_sort_push (x :: acc) stack) y s
      else
        descending stack (x :: acc) y s
    else
      merge_sort_pop false (x :: acc) stack.

Definition sortN (s : seq T) : seq T :=
  if s is x :: s then sortNrec [::] x s else [::].

(* Proofs *)

Import StableSort.

Let flatten_stack := foldr (fun x => cat^~ (@flatten_tree _ leT x)) nil.

Let Fixpoint sort_stack (mode : bool) (stack : seq (tree leT)) : seq (seq T) :=
  if stack isn't t :: stack then [::] else
    condrev mode (sort_tree t) :: sort_stack (~~ mode) stack.

Lemma merge_sort_pushP (t : tree leT) (stack : seq (tree leT)) :
  {stack' : seq (tree leT) |
    flatten_stack (t :: stack) = flatten_stack stack' &
    merge_sort_push (sort_tree t) (sort_stack false stack)
    = sort_stack false stack'}.
Proof.
move: t stack; fix IHstack 2; move=> t [|t' [|t'' stack]] /=.
- by exists [:: t].
- rewrite !M.revmergeE ifnilE tree_nilp; have [->|_] := nilP.
    by exists [:: t].
  by exists [:: empty_tree; branch_tree true t' t]; rewrite //= cats0.
- rewrite !M.revmergeE !ifnilE nilp_rev !tree_nilp; have [->|_] := nilP.
    by exists [:: t, t'' & stack]; rewrite ?cats0.
  rewrite -!catA; have [->|_] := nilP.
    by exists [:: empty_tree, branch_tree true t' t & stack]; rewrite /= ?cats0.
  have [/= {}stack -> ->] :=
    IHstack (branch_tree false t'' (branch_tree true t' t)) stack.
  by exists [:: empty_tree, empty_tree & stack]; rewrite /= ?cats0.
Qed.

Let nilp_condrev (r : bool) (s : seq T) : nilp (condrev r s) = nilp s.
Proof. by case: r; rewrite ?nilp_rev. Qed.

Lemma merge_sort_popP (mode : bool) (t : tree leT) (stack : seq (tree leT)) :
  {t' : tree leT |
    flatten_stack (t :: stack) = flatten_tree t' &
    merge_sort_pop mode (condrev mode (sort_tree t)) (sort_stack mode stack)
    = sort_tree t'}.
Proof.
move: mode t stack; fix IHstack 3; move=> mode t [|t' stack] /=.
  by exists t => //; case: mode; rewrite ?revK.
rewrite -catA !M.revmergeE ifnilE nilp_condrev.
case: tree_nilP => _ _; last first.
  by case: mode (IHstack (~~ mode) (branch_tree (~~ mode) t' t) stack).
case: stack => [|t'' stack] /=.
  by exists t => //; case: mode; rewrite ?revK.
rewrite !M.revmergeE !ifnilE !nilp_condrev !negbK revK.
case: tree_nilP => _ _; first by rewrite cats0; apply: IHstack.
rewrite -catA.
by case: mode (IHstack mode (branch_tree mode t'' t) stack); rewrite //= revK.
Qed.

Lemma sort1P (s : seq T) :
  {t : tree leT | s = flatten_tree t & sort1 s = sort_tree t}.
Proof.
rewrite /sort1.
have {1}->: s = flatten_stack [::] ++ s by [].
have ->: [::] = sort_stack false [::] by [].
elim: s [::] => [|x s IHs] stack /=.
  exact: merge_sort_popP empty_tree stack.
case: (merge_sort_pushP (leaf_tree true [:: x] erefl) stack).
by rewrite (catA _ [:: _]) => {}stack /= -> ->; exact: IHs.
Qed.

Lemma sort2P (s : seq T) :
  {t : tree leT | s = flatten_tree t & sort2 s = sort_tree t}.
Proof.
rewrite /sort2.
have {1}->: s = flatten_stack [::] ++ s by [].
have ->: [::] = sort_stack false [::] by [].
move: [::] s; fix IHs 2 => stack [|x [|y s]] /=.
- exact: merge_sort_popP (leaf_tree true [::] erefl) _.
- exact: merge_sort_popP (leaf_tree true [:: x] erefl) _.
case: (merge_sort_pushP (leaf_tree (leT x y) [:: x; y] _) stack).
  by rewrite /= eqxx.
by rewrite (catA _ [:: _; _]) => /= _ {}stack -> ->; apply: IHs.
Qed.

Lemma sort3P (s : seq T) :
  {t : tree leT | s = flatten_tree t & sort3 s = sort_tree t}.
Proof.
rewrite /sort3.
have sorted2 x y : sorted (fun x' y' => leT x' y' == leT x y) [:: x; y].
  by rewrite /= eqxx.
have {1}->: s = flatten_stack [::] ++ s by [].
have ->: [::] = sort_stack false [::] by [].
move: [::] s; fix IHs 2 => stack [|x [|y [|z s]]] /=.
- exact: merge_sort_popP (leaf_tree true [::] erefl) _.
- exact: merge_sort_popP (leaf_tree true [:: x] erefl) _.
- exact: merge_sort_popP (leaf_tree (leT x y) [:: x; y] (sorted2 _ _)) _.
rewrite (catA _ [:: _; _; _]).
pose xyz : tree leT := branch_tree false
  (leaf_tree (leT x y) [:: x; y] (sorted2 _ _)) (leaf_tree true [:: z] erefl).
case: (merge_sort_pushP xyz stack) => /= stack' ->.
set push1 := merge_sort_push _ _; set push2 := merge_sort_push _ _.
have ->: push1 = push2 by congr merge_sort_push; do 3 case: ifP => //=.
by move=> ->; apply: IHs.
Qed.

Lemma sortNP (s : seq T) :
  {t : tree leT | s = flatten_tree t & sortN s = sort_tree t}.
Proof.
case: s => /= [|x s]; first by exists empty_tree.
have {1}->: x :: s = flatten_stack [::] ++ x :: s by [].
have ->: [::] = sort_stack false [::] by [].
move: [::] x s; fix IHs 3 => stack x [|y s] /=.
  exact: merge_sort_popP (leaf_tree true [:: x] erefl) _.
set lexy := leT x y.
have: path (fun y x => leT x y == lexy) y [:: x] by rewrite /= eqxx.
have ->: [:: x, y & s] = rev [:: y; x] ++ s by [].
elim: s (lexy) (y) [:: x] => {lexy x y} => [|y s IHs' /=] ord x acc.
  rewrite -/(sorted _ (_ :: _)) -rev_sorted cats0 => sorted_acc.
  case: (merge_sort_popP false (leaf_tree ord _ sorted_acc) stack) => /= t ->.
  by rewrite revK; case: ord {sorted_acc} => ->; exists t.
case: ord (boolP (leT x y)) => [] [] lexy.
- move=> path_acc.
  have: path (fun y x => leT x y == true) y (x :: acc) by rewrite /= lexy eqxx.
  by case/IHs' => {path_acc} t; rewrite -cat_rcons -rev_cons => -> ->; exists t.
- rewrite -/(sorted _ (_ :: _)) -rev_sorted => sorted_acc.
  case: (merge_sort_pushP (leaf_tree true _ sorted_acc) stack) => stack'.
  by rewrite /= catA => -> ->; apply: IHs.
- rewrite -/(sorted _ (_ :: _)) -rev_sorted => sorted_acc.
  case: (merge_sort_pushP (leaf_tree false _ sorted_acc) stack) => stack'.
  by rewrite /= catA revK => -> ->; apply: IHs.
- move=> path_acc.
  have: path (fun y x => leT x y == false) y (x :: acc).
    by rewrite /= eqbF_neg lexy.
  by case/IHs' => {path_acc} t; rewrite -cat_rcons -rev_cons => -> ->; exists t.
Qed.

End CBV.

Realizer M.revmerge as revmerge_R arity 2 := M.revmerge_R.

Parametricity merge_sort_push.
Parametricity merge_sort_pop.
Parametricity sort1.
Parametricity sort2.
Parametricity sort3.
Parametricity sortN.

Definition sort1_stable := StableSort.Interface sort1 sort1_R sort1P.
Definition sort2_stable := StableSort.Interface sort2 sort2_R sort2P.
Definition sort3_stable := StableSort.Interface sort3 sort3_R sort3P.
Definition sortN_stable := StableSort.Interface sortN sortN_R sortNP.

End CBV_.

Module CBV := CBV_(Revmerge).
Module CBVAcc := CBV_(RevmergeAcc).

Canonical CBV.sort1_stable.
Canonical CBV.sort2_stable.
Canonical CBV.sort3_stable.
Canonical CBV.sortN_stable.
Canonical CBVAcc.sort1_stable.
Canonical CBVAcc.sort2_stable.
Canonical CBVAcc.sort3_stable.
Canonical CBVAcc.sortN_stable.

(******************************************************************************)
(* Theory of stable sort functions                                            *)
(******************************************************************************)

Section StableSortTheory.

Let lexord (T : Type) (leT leT' : rel T) :=
  [rel x y | leT x y && (leT y x ==> leT' x y)].

Let lexord_total (T : Type) (leT leT' : rel T) :
  total leT -> total leT' -> total (lexord leT leT').
Proof.
move=> leT_total leT'_total x y /=.
by move: (leT_total x y) (leT'_total x y) => /orP[->|->] /orP[->|->];
  rewrite /= ?implybE ?orbT ?andbT //= (orbAC, orbA) (orNb, orbN).
Qed.

Let lexord_trans (T : Type) (leT leT' : rel T) :
  transitive leT -> transitive leT' -> transitive (lexord leT leT').
Proof.
move=> leT_tr leT'_tr y x z /= /andP[lexy leyx] /andP[leyz lezy].
rewrite (leT_tr _ _ _ lexy leyz); apply/implyP => lezx; move: leyx lezy.
by rewrite (leT_tr _ _ _ leyz lezx) (leT_tr _ _ _ lezx lexy); exact: leT'_tr.
Qed.

Let lexordA (T : Type) (leT leT' leT'' : rel T) :
  lexord leT (lexord leT' leT'') =2 lexord (lexord leT leT') leT''.
Proof. by move=> x y /=; case: (leT x y) (leT y x) => [] []. Qed.

Section StableSortTheory_Part1.

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
by case: sort => ? ? sortP; have [/= t -> ->] := sortP _ leT s; constructor.
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
move=> /in3_sig ? _ /all_sigP[s ->].
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
  sorted (lexord leT leT') (sort _ leT s).
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
  sorted (lexord leT leT') (sort _ leT s).
Proof.
move=> /in2_sig leT_total _ /all_sigP[s ->].
by rewrite sort_map pairwise_map sorted_map; apply: sort_pairwise_stable.
Qed.

Lemma sort_stable (T : Type) (leT leT' : rel T) :
  total leT -> transitive leT' -> forall s : seq T, sorted leT' s ->
  sorted (lexord leT leT') (sort _ leT s).
Proof.
move=> leT_total leT'_tr s; rewrite sorted_pairwise //.
exact: sort_pairwise_stable.
Qed.

Lemma sort_stable_in (T : Type) (P : {pred T}) (leT leT' : rel T) :
  {in P &, total leT} -> {in P & &, transitive leT'} ->
  forall s : seq T, all P s -> sorted leT' s ->
  sorted (lexord leT leT') (sort _ leT s).
Proof.
move=> /in2_sig leT_total /in3_sig leT_tr _ /all_sigP[s ->].
by rewrite sort_map !sorted_map; apply: sort_stable.
Qed.

Lemma filter_sort (T : Type) (leT : rel T) :
  total leT -> transitive leT ->
  forall (p : pred T) (s : seq T),
    filter p (sort _ leT s) = sort _ leT (filter p s).
Proof.
move=> leT_total leT_tr p s; case Ds: s => [|x s1]; first by rewrite sort_nil.
pose lt_lex := lexord (relpre (nth x s) leT) ltn.
have lt_lex_tr: transitive lt_lex.
  by apply/lexord_trans/ltn_trans => ? ? ?; apply/leT_tr.
rewrite -{s1}Ds -(mkseq_nth x s) !(filter_map, sort_map); congr map.
apply/(@irr_sorted_eq _ lt_lex); rewrite /lt_lex /lexord //=.
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

Lemma sort_sort (T : Type) (leT leT' : rel T) :
  total leT -> transitive leT -> total leT' -> transitive leT' ->
  forall s : seq T, sort _ leT (sort _ leT' s) = sort _ (lexord leT leT') s.
Proof.
move=> leT_total leT_tr leT'_total leT'_tr s.
case Ds: s => [|x s1]; first by rewrite !sort_nil.
pose lt_lex' := lexord (relpre (nth x s) leT') ltn.
pose lt_lex := lexord (relpre (nth x s) leT) lt_lex'.
have lt_lex'_tr: transitive lt_lex'.
  by apply/lexord_trans/ltn_trans => ? ? ?; apply: leT'_tr.
have lt_lex_tr : transitive lt_lex.
  by apply/lexord_trans/lt_lex'_tr => ? ? ?; apply: leT_tr.
rewrite -{s1}Ds -(mkseq_nth x s) !(filter_map, sort_map); congr map.
apply/(@irr_sorted_eq _ lt_lex); rewrite /lt_lex /lexord //=.
- by move=> ?; rewrite /= ltnn !(implybF, andbN).
- exact/sort_stable/sort_stable/iota_ltn_sorted/ltn_trans.
- under eq_sorted => ? ? do rewrite lexordA.
  exact/sort_stable/iota_ltn_sorted/ltn_trans/lexord_total.
- by move=> ?; rewrite !mem_sort.
Qed.

Lemma sort_sort_in (T : Type) (P : {pred T}) (leT leT' : rel T) :
  {in P &, total leT} -> {in P & &, transitive leT} ->
  {in P &, total leT'} -> {in P & &, transitive leT'} ->
  forall s : seq T,
    all P s -> sort _ leT (sort _ leT' s) = sort _ (lexord leT leT') s.
Proof.
move=> /in2_sig leT_total /in3_sig leT_tr /in2_sig leT'_total /in3_sig leT'_tr.
by move=> _ /all_sigP[s ->]; rewrite !sort_map sort_sort.
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
by move=> /in2_sig ? _ /all_sigP[s ->]; rewrite sort_map sorted_map sort_sorted.
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

End StableSortTheory_Part1.

Lemma eq_sort (sort1 sort2 : stableSort) (T : Type) (leT : rel T) :
  total leT -> transitive leT -> sort1 _ leT =1 sort2 _ leT.
Proof.
move=> leT_total leT_tr s; case Ds: s => [|x s1]; first by rewrite !sort_nil.
pose lt_lex := lexord (relpre (nth x s) leT) ltn.
have lt_lex_tr: transitive lt_lex.
  by apply/lexord_trans/ltn_trans => ? ? ?; apply/leT_tr.
rewrite -{s1}Ds -(mkseq_nth x s) !(filter_map, sort_map); congr map.
apply/(@irr_sorted_eq _ lt_lex); rewrite /lt_lex /lexord //=.
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
move=> /in2_sig ? /in3_sig ? _ /all_sigP[s ->].
by rewrite !sort_map; congr map; exact: eq_sort.
Qed.

Section StableSortTheory_Part2.

Variable (sort : stableSort).

Section Stability.

Variables (T : Type) (leT : rel T).
Variables (leT_total : total leT) (leT_tr : transitive leT).

Lemma eq_sort_insert : sort _ leT =1 Insertion.sort leT.
Proof. exact: eq_sort. Qed.

Lemma sort_cat (s1 s2 : seq T) :
  sort _ leT (s1 ++ s2) = path.merge leT (sort _ leT s1) (sort _ leT s2).
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

End StableSortTheory_Part2.

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
Arguments filter_sort             sort {T leT} leT_total leT_tr p s.
Arguments filter_sort_in          sort {T P leT} leT_total leT_tr p {s} _.
Arguments sort_sort               sort {T leT leT'}
                                  leT_total leT_tr leT'_total leT'_tr s.
Arguments sort_sort_in            sort {T P leT leT'}
                                  leT_total leT_tr leT'_total leT'_tr {s} _.
Arguments sort_sorted             sort {T leT} leT_total s.
Arguments sort_sorted_in          sort {T P leT} leT_total {s} _.
Arguments perm_sortP              sort {T leT} leT_total leT_tr leT_asym s1 s2.
Arguments perm_sort_inP           sort {T leT s1 s2} leT_total leT_tr leT_asym.
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
