(* A verified version of top-down tail-recursive mergesort, presented in      *)
(* Sections 4.1 and 4.4.1 of the paper                                        *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import zify.
From stablesort Require Import param stablesort.
From Equations Require Import Equations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma if_nilp (T S : Type) (s : seq T) (x y : S) :
  (if nilp s then x else y) = if s is [::] then x else y.
Proof. by case: s. Qed.

Section Revmerge.

Context (T : Type) (leT : rel T).

Fixpoint merge_rec (xs ys accu : seq T) : seq T :=
  if xs is x :: xs' then
    (fix merge_rec' (ys accu : seq T) :=
       if ys is y :: ys' then
         if leT x y then
           merge_rec xs' ys (x :: accu) else merge_rec' ys' (y :: accu)
       else
         catrev xs accu) ys accu
  else catrev ys accu.

Definition revmerge (xs ys : seq T) : seq T := merge_rec xs ys [::].

Lemma revmergeE (xs ys : seq T) : revmerge xs ys = rev (merge leT xs ys).
Proof.
rewrite /revmerge /rev; move: xs ys [::].
by elim=> [|x xs IHxs]; elim=> [|y ys IHys] accu //=; case: ifP => /=.
Qed.

End Revmerge.

Module Abstract.
Section Abstract.

Context (T R : Type) (leT : rel T).
Context (merge merge' : R -> R -> R) (singleton : T -> R) (empty : R).

(* The abstract top-down tail-recursive mergesort (Section 4.4.1) *)
Equations sort_rec (xs : seq T) (b : bool) (n fuel : nat) :
    R * seq T by struct fuel :=
  (* The following three cases ar absurd because [0 < n <= size xs] and       *)
  (* [n <= fuel] should hold. Nevertheless, we add them to make [sort_rec]    *)
  (* total and to make its correctness proof easier.                          *)
  sort_rec xs _ _ 0 => (empty, xs);
  sort_rec xs _ 0 _ => (empty, xs);
  sort_rec [::] _ _ _ => (empty, [::]);
  (* end absurd cases *)
  sort_rec (x :: xs) _ 1 _ => (singleton x, xs);
  sort_rec xs b n fuel.+1 =>
    let n1 := n./2 in
    let (s1, xs') := sort_rec xs (~~ b) n1 fuel in
    let (s2, xs'') := sort_rec xs' (~~ b) (n - n1) fuel in
    ((if b then merge' s1 s2 else merge s1 s2), xs'').

#[using="All"]
Definition sort (xs : seq T) : R :=
  if xs is [::] then empty else let n := size xs in (sort_rec xs true n n).1.

End Abstract.

Parametricity sort.

End Abstract.

Section Concrete.

Context (T : Type) (leT : rel T).
Let geT x y := leT y x.

(* The concrete top-down tail-recursive mergesort (Section 4.1) *)
Equations sort_rec (xs : seq T) (b : bool) (n fuel : nat) :
    seq T * seq T by struct fuel :=
  (* begin absurd cases (cf. Abstract.sort_rec) *)
  sort_rec xs _ _ 0 => ([::], xs);
  sort_rec xs _ 0 _ => ([::], xs);
  sort_rec [::] _ _ _ => ([::], [::]);
  (* end absurd cases *)
  sort_rec (x :: xs) _ 1 _ => ([:: x], xs);
  sort_rec xs b n fuel.+1 =>
    let n1 := n./2 in
    let (s1, xs') := sort_rec xs (~~ b) n1 fuel in
    let (s2, xs'') := sort_rec xs' (~~ b) (n - n1) fuel in
    (if b then revmerge geT s2 s1 else revmerge leT s1 s2, xs'').

Definition sort (xs : seq T) : seq T :=
  if xs is [::] then [::] else let n := size xs in (sort_rec xs true n n).1.

Notation merge := (path.merge leT) (only parsing).
Notation merge' :=
  (fun xs ys => rev (path.merge geT (rev ys) (rev xs))) (only parsing).

(* The proof of Equation (5) *)
Lemma asort_mergeE :
  Abstract.sort leT merge merge' (fun x => [:: x]) [::] =1 sort.
Proof.
rewrite /Abstract.sort /sort => xs; rewrite -!if_nilp.
congr (if _ then _ else _.1).
pose condrev b (p : seq T * seq T) := ((if b then p.1 else rev p.1), p.2).
set rhs := RHS; have ->: rhs = condrev true rhs by case: rhs.
rewrite {}/rhs; move: {2 4}(size xs) => fuel.
apply_funelim (sort_rec xs true (size xs) fuel);
  try by move=> *; case: (b in condrev b).
move=> x {}xs b n {}fuel IHl IHr.
rewrite Abstract.sort_rec_equation_5 /= {}IHl /= {IHr}(IHr [::]) /=.
case: (sort_rec (x :: xs)) => s1 xs' /=; case: sort_rec => s2 xs'' /=.
by rewrite !revmergeE /condrev; case: b; rewrite /= !revK.
Qed.

(* The proof of Equation (6) *)
Lemma asort_catE : Abstract.sort leT cat cat (fun x => [:: x]) [::] =1 id.
Proof.
rewrite /Abstract.sort => xs.
rewrite (_ : Abstract.sort_rec _ _ _ _ _ _ _ _ =
               (take (size xs) xs, drop (size xs) xs)).
  by rewrite take_size; case: xs.
move: {2 4}(size xs) (leqnn (size xs)) => fuel.
apply_funelim
  (Abstract.sort_rec cat cat (fun x => [:: x]) [::] xs true (size xs) fuel).
- by move=> {}xs _ [] //; rewrite take0 drop0.
- by move=> {}xs; rewrite take0 drop0.
- by [].
- by move=> x {}xs; rewrite /= take0 drop0.
move=> x {}xs b n {}fuel IHl IHr; rewrite ltnS => n_lt_fuel.
rewrite [LHS]/= {}IHl 1?{}(IHr [::]) 1?if_same; try lia.
rewrite -takeD drop_drop; congr (take _ _, drop _ _); lia.
Qed.

End Concrete.

Canonical sort_stable :=
  StableSort sort Abstract.sort Abstract.sort_R asort_mergeE asort_catE.
