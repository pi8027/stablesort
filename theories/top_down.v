Require Export PArith.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From stablesort Require Import param stablesort.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module CBN_ (M : MergeSig).

Section CBN.

Variable (T : Type) (leT : rel T).

Fixpoint sort2_rec (c : bool) (n : positive) (s : seq T) : seq T * seq T :=
  let rec c1 c2 n s :=
    let (s1, s') := sort2_rec c1 n s in
    let (s2, s'') := sort2_rec c2 n s' in (M.merge leT s1 s2, s'')
  in
  match n, c, s with
    | 1%positive, _, [::] | 2%positive, _, [::] => ([::], s)
    | 1%positive, false, x :: s
    | 1%positive, true, x :: [::] as s
    | 2%positive, _, x :: [::] as s => ([:: x], s)
    | 1%positive, true, x :: y :: s | 2%positive, false, x :: y :: s =>
      ((if leT x y then [:: x; y] else [:: y; x]), s)
    | xO n, _, s => rec false c n s
    | xI n, _, s => rec c true n s
  end.

Definition sort2 (s : seq T) :=
  if bin_of_nat (size s) is Npos n then (sort2_rec false n s).1 else [::].

Import StableSort.

Lemma sort2_recP (c : bool) (n : positive) (s : seq T) :
  let n' := c + nat_of_pos n in
  {t : trace leT |
    take n' s = flatten_trace t & sort2_rec c n s = (sort_trace t, drop n' s) }.
Proof.
elim: n c s => /= [n IHn c s|[n|n|] IHn c s|].
- case: sort2_rec (IHn c s) => [_ s'] [t1 Ht1 [-> s'E]].
  case: sort2_rec (IHn true s') => [_ s''] [t2 Ht2 [-> s''E]].
  rewrite NatTrec.doubleE; exists (branch_trace true t1 t2).
  + rewrite /= -Ht1 -Ht2 s'E take_drop addnACA addnn addSnnS.
    rewrite -[LHS](cat_take_drop (c + nat_of_pos n)) take_take //.
    by rewrite leq_add2l leqW // -addnn leq_addr.
  + by rewrite s''E s'E drop_drop addnACA addnn add1n addSnnS M.mergeE.
- case: sort2_rec (IHn false s) => [_ s'] [t1 Ht1 [-> s'E]].
  case: sort2_rec (IHn c s') => [_ s''] [t2 Ht2 [-> s''E]].
  rewrite NatTrec.doubleE; exists (branch_trace true t1 t2).
  + rewrite /= -Ht1 -Ht2 s'E take_drop addnACA addnn add0n addn0.
    rewrite -[LHS](cat_take_drop (nat_of_pos (xI n))) take_take //.
    by rewrite -addnn addnA leq_addl.
  + by rewrite s''E s'E drop_drop addnACA addnn addn0 M.mergeE.
- case: sort2_rec (IHn false s) => [_ s'] [t1 Ht1 [-> s'E]].
  case: sort2_rec (IHn c s') => [_ s''] [t2 Ht2 [-> s''E]].
  rewrite NatTrec.doubleE; exists (branch_trace true t1 t2).
  + rewrite /= -Ht1 -Ht2 s'E take_drop addnACA addnn add0n addn0.
    rewrite -[LHS](cat_take_drop (nat_of_pos (xO n))) take_take //.
    by rewrite -addnn addnA leq_addl.
  + by rewrite s''E s'E drop_drop addnACA addnn addn0 M.mergeE.
- case: c s => [] [|x [|y s]].
  + by exists (leaf_trace true [::] isT).
  + by exists (leaf_trace true [:: x] isT).
  + case: sort2_rec (IHn false [:: x, y & s]) => [_ s'] [t1 Ht1 [-> s'E]].
    case: sort2_rec (IHn true s') => [_ s''] [t2 Ht2 [-> s''E]].
    rewrite NatTrec.doubleE; exists (branch_trace true t1 t2).
    * by rewrite /= -Ht1 -Ht2 s'E.
    * by rewrite s''E s'E M.mergeE.
  + by exists (leaf_trace true [::] isT).
  + by exists (leaf_trace true [:: x] isT).
  + have sorted_xy: sorted (fun x0 y0 => leT x0 y0 == leT x y) [:: x; y].
      by rewrite /= eqxx.
    exists (leaf_trace (leT x y) [:: x; y] sorted_xy).
      by rewrite /= take0.
    by rewrite /= drop0.
- case=> [[|x [|y s]] | [|x s]] //=.
  + by exists (leaf_trace true [::] isT).
  + by exists (leaf_trace true [:: x] isT).
  + have sorted_xy: sorted (fun x0 y0 => leT x0 y0 == leT x y) [:: x; y].
      by rewrite /= eqxx.
    exists (leaf_trace (leT x y) [:: x; y] sorted_xy).
      by rewrite take0.
    by rewrite drop0.
  + by exists (leaf_trace true [::] isT).
  + exists (leaf_trace true [:: x] isT).
      by rewrite take0.
    by rewrite drop0.
Qed.

Lemma sort2P (s : seq T) :
  {t : trace leT | s = flatten_trace t & sort2 s = sort_trace t}.
Proof.
rewrite /sort2.
case: (bin_of_nat _) (bin_of_natK (size s)) => [|n] //=.
- by move=> /esym /size0nil ->; exists (leaf_trace true [::] isT).
- move=> nE; case: (sort2_recP false n s) => t /=.
  by rewrite add0n nE take_oversize // drop_oversize // => -> -> /=; exists t.
Qed.

End CBN.

Realizer M.merge as merge_R arity 2 := M.merge_R.

Parametricity sort2.

Definition sort2_stable := StableSort.Pack sort2 sort2_R sort2P.

End CBN_.

Module CBN := CBN_(Merge).
Module CBNAcc := CBN_(MergeAcc).

Canonical CBN.sort2_stable.
Canonical CBNAcc.sort2_stable.
