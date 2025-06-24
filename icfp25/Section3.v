(******************************************************************************)
(* Section 3: Non-tail-recursive mergesorts                                   *)
(* This file is the Rocq formalization of Section 3, that provides:           *)
(* - the simpler version of the characteristic property that work only for    *)
(*   non-tail-recursive mergesorts (Section 3.2),                             *)
(* - the proofs that the insertion sort (Definition 3.1), top-down mergesort  *)
(*   (Figure 2a), and bottom-up mergesort (Figure 2b) satisfy the             *)
(*   characteristic property (Section 3.3), and                               *)
(* - generic correctness proofs (Section 3.4), including all the lemmas       *)
(*   listed in Appendix B.                                                    *)
(* We refer the readers to `AppendixC.v` for the Rocq counterpart of Section  *)
(* 3.4.3.                                                                     *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From mathcomp Require Import zify.
From Param Require Export Param.
From Equations Require Import Equations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Global Ltac destruct_reflexivity :=
  intros; repeat match goal with
  | [ x : _ |- _ = _ ] => destruct x; reflexivity; fail
  end.

Global Parametricity Tactic := destruct_reflexivity.

Parametricity bool.
Parametricity nat.
Parametricity list.
Parametricity merge.

Local Lemma bool_R_refl b1 b2 : b1 = b2 -> bool_R b1 b2.
Proof. by case: b1 => <-; constructor. Qed.

Local Lemma map_rel_map A B (f : A -> B) (l : seq A) :
  list_R (fun x y => f x = y) l (map f l).
Proof. by elim: l; constructor. Qed.

Local Lemma rel_map_map A B (f : A -> B) (l : seq A) (fl : seq B) :
  list_R (fun x y => f x = y) l fl -> fl = map f l.
Proof. by elim/list_R_ind: l fl / => //= ? ? <- ? ? _ ->. Qed.

(******************************************************************************)
(* Section 3.2: Characterization of stable non-tail-recursive mergesort       *)
(* functions                                                                  *)
(* Here we formally define the simplified version of the characterization of  *)
(* mergesort that works only for non-tail-recursive mergesorts (Section 3.2). *)
(* The characteristic properties are bundled as a record type stableSort      *)
(* (:= StableSort.function) in the same way as Section 5.2.1.                 *)
(******************************************************************************)

Module StableSort.

(* the type of polymorphic sort functions                                     *)
Definition sort_ty :=
  forall T : Type,                      (* the type of elements               *)
    rel T ->                            (* the comparison function `leT`      *)
    seq T ->                            (* input                              *)
    seq T.                              (* output                             *)

(* the type of sort functions abstracted over the type of sorted lists and    *)
(* some operations on them, e.g., merge                                       *)
Definition asort_ty :=
  forall T : Type,                      (* the type of elements               *)
  forall R : Type,                      (* the type of sorted lists           *)
    (R -> R -> R) ->                    (* merge by `leT`                     *)
    (T -> R) ->                         (* singleton sorted list              *)
    R ->                                (* empty sorted list                  *)
    seq T ->                            (* input                              *)
    R.                                  (* output                             *)

Parametricity sort_ty.
Parametricity asort_ty.

Structure function := Pack {
  (* the sort function                                                        *)
  apply : forall T : Type, rel T -> seq T -> seq T;
  (* the *abstract* sort function                                             *)
  asort : asort_ty;
  (* Binary parametricity of `asort`                                          *)
  (* _ : forall (T1 T2 : Type) (T_R : T1 -> T2 -> Type)                       *)
  (*            (R1 R2 : Type) (R_R : R1 -> R2 -> Type)                       *)
  (*            (merge1 : R1 -> R1 -> R1) (merge2 : R2 -> R2 -> R2),          *)
  (*       (forall (xs1 : R1) (xs2 : R2), R_R xs1 xs2 ->                      *)
  (*        forall (ys1 : R1) (ys2 : R2), R_R ys1 ys2 ->                      *)
  (*          R_R (merge1 xs1 ys1) (merge2 xs2 ys2)) ->                       *)
  (*     forall (singleton1 : T1 -> R1) (singleton2 : T2 -> R2),              *)
  (*       (forall (x1 : T1) (x2 : T2), T_R x1 x2 ->                          *)
  (*          R_R (singleton1 x1) (singleton2 x2)) ->                         *)
  (*     forall (empty1 : R1) (empty2 : R2), R_R empty1 empty2 ->             *)
  (*     forall (xs1 : seq T1) (xs2 : seq T2), list_R T_R xs1 xs2 ->          *)
  (*       R_R (asort merge1 singleton1 empty1 xs1)                           *)
  (*           (asort merge2 singleton2 empty2 xs2);                          *)
  _ : asort_ty_R asort asort;
  (* Equation (1): the abstract sort function `asort` instantiated with merge *)
  (* is extensionally equal to the sort function `apply`                      *)
  _ : forall (T : Type) (leT : rel T),
    asort (merge leT) (fun x => [:: x]) [::] =1 apply leT;
  (* Equation (2): the abstract sort function `asort` instantiated with       *)
  (* concatenation is the identity function                                   *)
  _ : forall T : Type, asort cat (fun x : T => [:: x]) [::] =1 id;
}.

Module Exports.
Arguments Pack apply _ _ : clear implicits.
Notation stableSort := function.
Notation StableSort := Pack.
Coercion apply : function >-> Funclass.
End Exports.

End StableSort.
Export StableSort.Exports.

(******************************************************************************)
(* Section 3.3: Proofs of the characteristic property                         *)
(* Here we define the insertion sort (Definition 3.1), top-down mergesort     *)
(* (Figure 2a), and bottom-up mergesort (Figure 2b), and prove that they      *)
(* satisfy the characteristic property.                                       *)
(******************************************************************************)

(* Insection sort *)
Module Insertion.

Module Abstract.

(* The abstract insertion sort (in the proof of Lemma 3.2) *)
Definition sort T R (merge : R -> R -> R) (singleton : T -> R) (empty : R) :=
  foldr (fun x => merge (singleton x)) empty.

(* Its parametricity *)
Parametricity sort.

End Abstract.

(* The concrete insertion sort (Definition 3.1) *)
Definition sort (T : Type) (leT : rel T) : seq T -> seq T :=
  foldr (fun x => merge leT [:: x]) [::].

(* Equation (1) holds by definition *)
Lemma asort_mergeE (T : Type) (leT : rel T) :
  Abstract.sort (merge leT) (fun x : T => [:: x]) [::] =1 sort leT.
Proof. by move=> ?; reflexivity. Qed.

(* The proof of Equation (2) in Lemma 3.2 *)
Lemma asort_catE (T : Type) :
  Abstract.sort cat (fun x : T => [:: x]) [::] =1 id.
Proof. by elim=> //= x xs ->. Qed.

Definition sort_stable :=
  StableSort sort Abstract.sort Abstract.sort_R asort_mergeE asort_catE.

End Insertion.

Canonical Insertion.sort_stable.

(* Top-down mergesort (Figure 2a) *)
Module TopDown.

(* The abstract top-down mergesort (Figure 4a) *)
Module Abstract.
Section Abstract.

Context (T R : Type) (merge : R -> R -> R) (singleton : T -> R) (empty : R).

Equations sort_rec (xs : seq T) (fuel : nat) : R by struct fuel :=
  sort_rec _ 0        => empty;
  sort_rec [::] _     => empty;
  sort_rec [:: x] _   => singleton x;
  sort_rec xs fuel.+1 =>
    let k := size xs in
    merge (sort_rec (take k./2 xs) fuel) (sort_rec (drop k./2 xs) fuel).

Definition sort (xs : seq T) : R := sort_rec xs (size xs).

End Abstract.

(* Its parametricity *)
Parametricity sort.

End Abstract.

Section TopDown.

Context (T : Type) (leT : rel T).

(* The concrete top-down mergesort (Figure 2a) *)
Equations sort_rec (xs : seq T) (fuel : nat) : seq T by struct fuel :=
  sort_rec _ 0        => [::];
  sort_rec [::] _     => [::];
  sort_rec [:: x] _   => [:: x];
  sort_rec xs fuel.+1 =>
    let n := size xs in
    merge leT (sort_rec (take n./2 xs) fuel) (sort_rec (drop n./2 xs) fuel).

Definition sort (xs : seq T) : seq T := sort_rec xs (size xs).

(* Equation (1) holds by definition. *)
Lemma asort_mergeE : Abstract.sort (merge leT) (fun x => [:: x]) [::] =1 sort.
Proof. by []. Qed.

(* The proof of Equation (2) in Lemma 3.3 *)
Lemma asort_catE : Abstract.sort cat (fun x : T => [:: x]) [::] =1 id.
Proof.
rewrite /Abstract.sort => xs; move: {-1}(size xs) (leqnn (size xs)) => n.
elim: n xs => [|n IHn] [|x [|y xs]] //= Hxs; simp sort_rec; cbn zeta.
rewrite !IHn ?cat_take_drop //= (size_drop, size_take) /=; last case: ifP; lia.
Qed.

End TopDown.

Definition sort_stable :=
  StableSort sort Abstract.sort Abstract.sort_R asort_mergeE asort_catE.

End TopDown.

Canonical TopDown.sort_stable.

(* Bottom-up mergesort (Figure 2b) *)
Module BottomUp.

(* The abstract bottom-up mergesort (Figure 4b) *)
Module Abstract.
Section Abstract.

Context (T R : Type) (merge : R -> R -> R) (singleton : T -> R) (empty : R).

Equations merge_pairs (xs : seq R) : seq R by struct xs :=
  merge_pairs (a :: b :: xs) => merge a b :: merge_pairs xs;
  merge_pairs xs             => xs.

Equations merge_all (xs : seq R) (fuel : nat) : R by struct fuel :=
  merge_all _ 0        => empty;
  merge_all [::] _     => empty;
  merge_all [:: x] _   => x;
  merge_all xs fuel.+1 => merge_all (merge_pairs xs) fuel.

Definition sort (xs : seq T) : R := merge_all (map singleton xs) (size xs).

Lemma size_merge_pairs xs : size (merge_pairs xs) = uphalf (size xs).
Proof. by apply_funelim (merge_pairs xs) => //= ? ? ? ->. Qed.

End Abstract.

(* Its parametricity *)
Parametricity sort.

End Abstract.

Section BottomUp.

Context (T : Type) (leT : rel T).

(* The concrete bottom-up mergesort (Figure 2b) *)
Equations merge_pairs (xs : seq (seq T)) : seq (seq T) by struct xs :=
  merge_pairs (a :: b :: xs) => merge leT a b :: merge_pairs xs;
  merge_pairs xs             => xs.

Equations merge_all (xs : seq (seq T)) (fuel : nat) : seq T by struct fuel :=
  merge_all _ 0        => [::];
  merge_all [::] _     => [::];
  merge_all [:: x] _   => x;
  merge_all xs fuel.+1 => merge_all (merge_pairs xs) fuel.

Definition sort (xs : seq T) : seq T :=
  merge_all (map (fun x => [:: x]) xs) (size xs).

(* Equation (1) holds by definition. *)
Lemma asort_mergeE : Abstract.sort (merge leT) (fun x => [:: x]) [::] =1 sort.
Proof. by []. Qed.

Lemma flatten_merge_pairs (xs : seq (seq T)) :
  flatten (Abstract.merge_pairs cat xs) = flatten xs.
Proof.
by apply_funelim (Abstract.merge_pairs cat xs) => //= ? ? ? ->; rewrite catA.
Qed.

(* The proof of Equation (2) in Lemma 3.4 *)
Lemma asort_catE : Abstract.sort cat (fun x : T => [:: x]) [::] =1 id.
Proof.
move=> xs; rewrite /Abstract.sort -[RHS]flatten_seq1 -(size_map (cons^~ [::])).
move: (map _ _) => {}xs; move: {-1}(size xs) (leqnn (size xs)) => n.
elim: n xs => [|n IHn] [|x [|y xs]] //= Hxs; first by rewrite cats0.
simp merge_all; rewrite IHn ?flatten_merge_pairs ?Abstract.size_merge_pairs //=.
lia.
Qed.

End BottomUp.

Definition sort_stable :=
  StableSort sort Abstract.sort Abstract.sort_R asort_mergeE asort_catE.

End BottomUp.

Canonical BottomUp.sort_stable.

(******************************************************************************)
(* Section 3.4: Correctness proofs                                            *)
(******************************************************************************)

Section StableSortTheory.

Let lexord (T : Type) (leT leT' : rel T) :=
  [rel x y | leT x y && (leT y x ==> leT' x y)].

Local Lemma lexord_total (T : Type) (leT leT' : rel T) :
  total leT -> total leT' -> total (lexord leT leT').
Proof.
move=> leT_total leT'_total x y /=.
by move: (leT_total x y) (leT'_total x y) => /orP[->|->] /orP[->|->];
  rewrite /= ?implybE ?orbT ?andbT //= (orbAC, orbA) (orNb, orbN).
Qed.

Local Lemma lexord_trans (T : Type) (leT leT' : rel T) :
  transitive leT -> transitive leT' -> transitive (lexord leT leT').
Proof.
move=> leT_tr leT'_tr y x z /= /andP[lexy leyx] /andP[leyz lezy].
rewrite (leT_tr _ _ _ lexy leyz); apply/implyP => lezx; move: leyx lezy.
by rewrite (leT_tr _ _ _ leyz lezx) (leT_tr _ _ _ lezx lexy); exact: leT'_tr.
Qed.

Local Lemma lexord_irr (T : Type) (leT leT' : rel T) :
  irreflexive leT' -> irreflexive (lexord leT leT').
Proof. by move=> irr x /=; rewrite irr implybF andbN. Qed.

Local Lemma lexordA (T : Type) (leT leT' leT'' : rel T) :
  lexord leT (lexord leT' leT'') =2 lexord (lexord leT leT') leT''.
Proof. by move=> x y /=; case: (leT x y) (leT y x) => [] []. Qed.

Section StableSortTheory_Part1.

Context (sort : stableSort).

Local Lemma param_asort :
  StableSort.asort_ty_R (StableSort.asort sort) (StableSort.asort sort).
Proof. by case: sort. Qed.

Section SortSeq.

Context (T : Type) (leT leT' : rel T).

Local Lemma asort_mergeE :
  StableSort.asort sort (merge leT) (fun x => [:: x]) [::] =1 sort _ leT.
Proof. by case: sort. Qed.

Local Lemma asort_catE :
  StableSort.asort sort cat (fun x : T => [:: x]) [::] =1 id.
Proof. by case: sort. Qed.

(* Lemma 3.5 *)
Lemma sort_ind (R : seq T -> seq T -> Prop) :
  (forall xs xs', R xs xs' -> forall ys ys', R ys ys' ->
     R (cat xs ys) (merge leT xs' ys')) ->
  (forall x, R [:: x] [:: x]) -> R [::] [::] ->
  forall s, R s (sort _ leT s).
Proof.
move=> ? Hsingleton ? s; rewrite -[s in R s _]asort_catE -asort_mergeE.
apply: (@param_asort _ _ eq _ _ R) => //; last by elim: s; constructor.
by move=> ? ? ->; apply: Hsingleton.
Qed.

(* Lemma 3.10 (B.3) *)
Lemma pairwise_sort (s : seq T) : pairwise leT s -> sort _ leT s = s.
Proof.
elim/sort_ind: (sort _ leT s) => // xs xs' IHxs ys ys' IHys.
by rewrite pairwise_cat => /and3P[/allrel_merge <- /IHxs -> /IHys ->].
Qed.

Lemma sorted_sort : transitive leT ->
  forall s : seq T, sorted leT s -> sort _ leT s = s.
Proof. by move=> leT_tr s; rewrite sorted_pairwise //; apply/pairwise_sort. Qed.

(* Theorem 3.11 (B.5) *)
Lemma sort_pairwise_stable : total leT ->
  forall s : seq T, pairwise leT' s -> sorted (lexord leT leT') (sort _ leT s).
Proof.
move=> leT_total s.
suff: (forall P, all P s -> all P (sort T leT s)) /\
        (pairwise leT' s -> sorted (lexord leT leT') (sort T leT s)).
  by case.
elim/sort_ind: (sort _ leT s) => // xs xs' [IHxs IHxs'] ys ys' [IHys IHys'].
rewrite pairwise_cat; split=> [P|/and3P[hlr /IHxs' ? /IHys' ?]].
  by rewrite all_cat all_merge => /andP[/IHxs -> /IHys ->].
apply/merge_stable_sorted => //=.
apply/IHxs; apply/sub_all: hlr => ?; apply/IHys.
Qed.

(* Corollary 3.12 (B.6) *)
Lemma sort_stable : total leT -> transitive leT' ->
  forall s : seq T, sorted leT' s -> sorted (lexord leT leT') (sort _ leT s).
Proof.
by move=> ? ? s; rewrite sorted_pairwise//; apply: sort_pairwise_stable.
Qed.

End SortSeq.

(* Lemma B.7 *)
Lemma count_sort (T : Type) (leT : rel T) (p : pred T) (s : seq T) :
  count p (sort T leT s) = count p s.
Proof.
elim/sort_ind: (sort _ leT s) => // xs xs' IHxs ys ys' IHys.
by rewrite count_merge !count_cat IHxs IHys.
Qed.

(* Lemma B.8 *)
Lemma size_sort (T : Type) (leT : rel T) (s : seq T) :
  size (sort _ leT s) = size s.
Proof. exact: (count_sort _ predT). Qed.

(* Lemma B.9 *)
Lemma sort_nil (T : Type) (leT : rel T) : sort _ leT [::] = [::].
Proof. by case: (sort _) (size_sort leT [::]). Qed.

(* Lemma B.10 *)
Lemma all_sort (T : Type) (p : pred T) (leT : rel T) (s : seq T) :
  all p (sort _ leT s) = all p s.
Proof. by rewrite !all_count count_sort size_sort. Qed.

Section EqSortSeq.

Context (T : eqType) (leT : rel T) (s : seq T).

(* Lemma 3.7 (B.11) *)
Lemma perm_sort : perm_eql (sort _ leT s) s.
Proof.
(* A simpler proof using `permP` and `count_sort`, shown in Lemma B.11 *)
Succeed by apply/permPl/permP => ?; rewrite count_sort.
(* The proof shown in Lemma 3.7 in Section 3.4.1 *)
apply/permPl; elim/sort_ind: (sort _ leT s) => // xs xs' + ys ys'.
by rewrite perm_merge; apply: perm_cat.
Qed.

(* Corollary 3.8 (B.12) *)
Lemma mem_sort : sort _ leT s =i s.
Proof. exact/perm_mem/permPl/perm_sort. Qed.

(* Lemma B.13 *)
Lemma sort_uniq : uniq (sort _ leT s) = uniq s.
Proof. exact/perm_uniq/permPl/perm_sort. Qed.

End EqSortSeq.

(* Lemma 3.13 *)
Local Lemma param_sort : StableSort.sort_ty_R sort sort.
Proof.
move=> T T' T_R leT leT' leT_R xs xs' xs_R; rewrite -!asort_mergeE.
apply: (@param_asort _ _ T_R _ _ (list_R T_R) _ _ (merge_R leT_R));
  by do ?constructor.
Qed.

(* Lemma 3.14 (B.2) *)
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

Lemma sorted_sort_in (T : Type) (P : {pred T}) (leT : rel T) :
  {in P & &, transitive leT} ->
  forall s : seq T, all P s -> sorted leT s -> sort _ leT s = s.
Proof.
move=> /in3_sig ? _ /all_sigP[s ->].
by rewrite sort_map sorted_map => /sorted_sort->.
Qed.

Lemma sort_pairwise_stable_in (T : Type) (P : {pred T}) (leT leT' : rel T) :
  {in P &, total leT} -> forall s : seq T, all P s -> pairwise leT' s ->
  sorted (lexord leT leT') (sort _ leT s).
Proof.
move=> /in2_sig leT_total _ /all_sigP[s ->].
by rewrite sort_map pairwise_map sorted_map; apply: sort_pairwise_stable.
Qed.

Lemma sort_stable_in (T : Type) (P : {pred T}) (leT leT' : rel T) :
  {in P &, total leT} -> {in P & &, transitive leT'} ->
  forall s : seq T, all P s -> sorted leT' s ->
  sorted (lexord leT leT') (sort _ leT s).
Proof.
move=> /in2_sig leT_total /in3_sig leT_tr _ /all_sigP[s ->].
by rewrite sort_map !sorted_map; apply: sort_stable.
Qed.

(* Theorem 3.16 (B.14) *)
Lemma filter_sort (T : Type) (leT : rel T) :
  total leT -> transitive leT ->
  forall (p : pred T) (s : seq T),
    filter p (sort _ leT s) = sort _ leT (filter p s).
Proof.
move=> leT_total leT_tr p s; case Ds: s => [|x s1]; first by rewrite sort_nil.
pose lt := lexord (relpre (nth x s) leT) ltn.
have lt_tr: transitive lt by apply/lexord_trans/ltn_trans/relpre_trans.
rewrite -{s1}Ds -(mkseq_nth x s) !(filter_map, sort_map); congr map.
apply/(@irr_sorted_eq _ lt); rewrite /lt /lexord //=.
- exact/lexord_irr/ltnn.
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

(* Lemma B.15 *)
Lemma sorted_filter_sort (T : Type) (leT : rel T) :
  total leT -> transitive leT ->
  forall (p : pred T) (s : seq T),
  sorted leT (filter p s) -> filter p (sort _ leT s) = filter p s.
Proof. by move=> *; rewrite filter_sort// sorted_sort. Qed.

Lemma sorted_filter_sort_in (T : Type) (P : {pred T}) (leT : rel T) :
  {in P &, total leT} -> {in P & &, transitive leT} ->
  forall (p : pred T) (s : seq T),
  all P s -> sorted leT (filter p s) -> filter p (sort _ leT s) = filter p s.
Proof.
move=> /in2_sig leT_total /in3_sig leT_tr p _ /all_sigP[s ->].
by rewrite sort_map !filter_map sorted_map /= => /sorted_filter_sort ->.
Qed.

(* Corollary 3.17 (C.1) *)
Fact sort_stable_leroy (T : Type) (leT : rel T) :
  total leT -> transitive leT ->
  forall (x : T) (s : list T),
    [seq y <- sort T leT s | leT x y && leT y x] =
      [seq y <- s | leT x y && leT y x].
Proof.
move=> leT_total leT_trans x s.
apply/sorted_filter_sort/(@path_sorted _ _ x) => //.
move: (filter _ _) (filter_all (fun y => leT x y && leT y x) s) => {}s.
elim: s x => //= x s IHs y /andP[/andP[yx xy] alls] /=.
rewrite yx IHs //; apply: sub_all alls => z /andP[yz zy].
by rewrite (leT_trans _ _ _ xy yz) (leT_trans _ _ _ zy yx).
Qed.

(* Lemma B.16 *)
Lemma sort_sort (T : Type) (leT leT' : rel T) :
  total leT -> transitive leT -> total leT' -> transitive leT' ->
  forall s : seq T, sort _ leT (sort _ leT' s) = sort _ (lexord leT leT') s.
Proof.
move=> leT_total leT_tr leT'_total leT'_tr s.
case Ds: s => [|x s1]; first by rewrite !sort_nil.
pose lt' := lexord (relpre (nth x s) leT') ltn.
pose lt := lexord (relpre (nth x s) leT) lt'.
have lt'_tr: transitive lt' by apply/lexord_trans/ltn_trans/relpre_trans.
have lt_tr : transitive lt by apply/lexord_trans/lt'_tr/relpre_trans.
rewrite -{s1}Ds -(mkseq_nth x s) !sort_map; congr map.
apply/(@irr_sorted_eq _ lt); rewrite /lt /lexord //=.
- exact/lexord_irr/lexord_irr/ltnn.
- exact/sort_stable/sort_stable/iota_ltn_sorted/ltn_trans.
- under eq_sorted do rewrite lexordA.
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

(* Lemma B.17 *)
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

(* Lemma B.18 *)
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

(* Lemma B.19 *)
Lemma eq_sort (sort1 sort2 : stableSort) (T : Type) (leT : rel T) :
  total leT -> transitive leT -> sort1 _ leT =1 sort2 _ leT.
Proof.
move=> leT_total leT_tr s; case Ds: s => [|x s1]; first by rewrite !sort_nil.
pose lt := lexord (relpre (nth x s) leT) ltn.
have lt_tr: transitive lt by apply/lexord_trans/ltn_trans/relpre_trans.
rewrite -{s1}Ds -(mkseq_nth x s) !sort_map; congr map.
apply/(@irr_sorted_eq _ lt); rewrite /lt /lexord //=.
- exact/lexord_irr/ltnn.
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

Context (sort : stableSort).

Section Stability.

Context (T : Type) (leT : rel T).
Context (leT_total : total leT) (leT_tr : transitive leT).

(* Lemma B.20 *)
Lemma eq_sort_insert : sort _ leT =1 Insertion.sort leT.
Proof. exact: eq_sort. Qed.

(* Lemma B.21 *)
Lemma sort_cat (s1 s2 : seq T) :
  sort _ leT (s1 ++ s2) = path.merge leT (sort _ leT s1) (sort _ leT s2).
Proof. by rewrite !eq_sort_insert; elim: s1 => //= x s1 ->; rewrite mergeA. Qed.

(* Lemma B.22 *)
Lemma mask_sort (s : seq T) (m : bitseq) :
  {m_s : bitseq | mask m_s (sort _ leT s) = sort _ leT (mask m s)}.
Proof.
case Ds: s => [|x s1]; first by exists [::]; rewrite mask0 sort_nil.
rewrite -{s1}Ds -(mkseq_nth x s) -map_mask !sort_map.
exists [seq i \in mask m (iota 0 (size s)) |
            i <- sort _ (xrelpre (nth x s) leT) (iota 0 (size s))].
rewrite -map_mask -filter_mask [in RHS]mask_filter ?iota_uniq ?filter_sort //.
by move=> ? ? ?; exact: leT_tr.
Qed.

(* Lemma B.23 *)
Lemma sorted_mask_sort (s : seq T) (m : bitseq) :
  sorted leT (mask m s) -> {m_s : bitseq | mask m_s (sort _ leT s) = mask m s}.
Proof. by move/(sorted_sort sort leT_tr) <-; exact: mask_sort. Qed.

End Stability.

Section Stability_in.

Context (T : Type) (P : {pred T}) (leT : rel T).
Context (leT_total : {in P &, total leT}) (leT_tr : {in P & &, transitive leT}).

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

Context (T : eqType) (leT : rel T).
Context (leT_total : total leT) (leT_tr : transitive leT).

(* Lemma B.24 *)
Lemma subseq_sort : {homo sort _ leT : t s / subseq t s}.
Proof.
move=> _ s /subseqP [m _ ->].
by have [m' <-] := mask_sort leT_total leT_tr s m; exact: mask_subseq.
Qed.

(* Lemma B.25 *)
Lemma sorted_subseq_sort (t s : seq T) :
  subseq t s -> sorted leT t -> subseq t (sort _ leT s).
Proof.
by move=> subseq_ts /(sorted_sort sort leT_tr) <-; exact: subseq_sort.
Qed.

(* Lemma B.26 *)
Lemma mem2_sort (s : seq T) (x y : T) :
  leT x y -> mem2 s x y -> mem2 (sort _ leT s) x y.
Proof.
move=> lexy; rewrite !mem2E => /subseq_sort; rewrite !eq_sort_insert //.
by case: (_ == _); rewrite //= lexy.
Qed.

End Stability_subseq.

Section Stability_subseq_in.

Context (T : eqType) (leT : rel T).

Lemma subseq_sort_in (t s : seq T) :
  {in s &, total leT} -> {in s & &, transitive leT} ->
  subseq t s -> subseq (sort _ leT t) (sort _ leT s).
Proof.
move=> leT_total leT_tr /subseqP [m _ ->].
have [m' <-] := mask_sort_in leT_total leT_tr m (allss _).
exact: mask_subseq.
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

Arguments sort_ind                sort {T leT R} _ _ _ s.
Arguments map_sort                sort {T T' f leT' leT} _ _.
Arguments sort_map                sort {T T' f leT} s.
Arguments pairwise_sort           sort {T leT s} _.
Arguments sorted_sort             sort {T leT} leT_tr {s} _.
Arguments sorted_sort_in          sort {T P leT} leT_tr {s} _ _.
Arguments sort_pairwise_stable    sort {T leT leT'} leT_total {s} _.
Arguments sort_pairwise_stable_in sort {T P leT leT'} leT_total {s} _ _.
Arguments sort_stable             sort {T leT leT'} leT_total leT'_tr {s} _.
Arguments sort_stable_in          sort {T P leT leT'} leT_total leT'_tr {s} _ _.
Arguments count_sort              sort {T} leT p s.
Arguments size_sort               sort {T} leT s.
Arguments sort_nil                sort {T} leT.
Arguments all_sort                sort {T} p leT s.
Arguments perm_sort               sort {T} leT s _.
Arguments mem_sort                sort {T} leT s _.
Arguments sort_uniq               sort {T} leT s.
Arguments filter_sort             sort {T leT} leT_total leT_tr p s.
Arguments filter_sort_in          sort {T P leT} leT_total leT_tr p {s} _.
Arguments sorted_filter_sort      sort {T leT} leT_total leT_tr p {s} _.
Arguments sorted_filter_sort_in   sort {T P leT} leT_total leT_tr p {s} _ _.
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
Arguments eq_in_sort_insert       sort {T P leT} leT_total leT_tr {s} _.
Arguments sort_cat                sort {T leT} leT_total leT_tr s1 s2.
Arguments sort_cat_in             sort {T P leT} leT_total leT_tr {s1 s2} _ _.
Arguments mask_sort               sort {T leT} leT_total leT_tr s m.
Arguments mask_sort_in            sort {T P leT} leT_total leT_tr {s} m _.
Arguments sorted_mask_sort        sort {T leT} leT_total leT_tr {s m} _.
Arguments sorted_mask_sort_in     sort {T P leT} leT_total leT_tr {s m} _ _.
Arguments subseq_sort             sort {T leT} leT_total leT_tr {x y} _.
Arguments subseq_sort_in          sort {T leT t s} leT_total leT_tr _.
Arguments sorted_subseq_sort      sort {T leT} leT_total leT_tr {t s} _ _.
Arguments sorted_subseq_sort_in   sort {T leT t s} leT_total leT_tr _ _.
Arguments mem2_sort               sort {T leT} leT_total leT_tr {s x y} _ _.
Arguments mem2_sort_in            sort {T leT s} leT_total leT_tr x y _ _.
