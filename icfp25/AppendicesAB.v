(* This file re-exports the definitions and lemmas listed in Appendices A and *)
(* B from the MathComp and Stablesort libraries. In order to make the         *)
(* re-exportation self-contained, some libraries are just `Require`d but not  *)
(* `Import`ed, and the section mechanism is not used.                         *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From mathcomp Require seq path order.
From stablesort Require stablesort.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Declare Scope seq_scope.
Delimit Scope seq_scope with SEQ.
Open Scope seq_scope.

Notation stableSort := stablesort.StableSort.function.
Notation StableSort := stablesort.StableSort.Pack.
Coercion stablesort.StableSort.apply : stableSort >-> Funclass.

Implicit Types (sort : stableSort) (T R S : Type).

(******************************************************************************)
(* Appendix A: Basic definitions and facts used for proofs                    *)
(******************************************************************************)

(******************************************)
(* Appendix A.1: Predicates and relations *)
(******************************************)

Definition pred T : Type := T -> bool.
Definition rel T : Type := T -> pred T.

Definition total T (R : rel T) : Prop := forall x y : T, R x y || R y x.

Definition transitive T (R : rel T) : Prop :=
  forall y x z : T, R x y -> R y z -> R x z.

Definition antisymmetric T (R : rel T) : Prop :=
  forall x y : T, R x y && R y x -> x = y.

Definition reflexive T (R : rel T) : Prop := forall x : T, R x x.

Definition irreflexive T (R : rel T) : Prop := forall x : T, R x x = false.

Lemma relpre_trans (T' T : Type) (leT : rel T) (f : T' -> T) :
  transitive leT -> transitive (relpre f leT).
Proof. by move=> + y x z; apply. Qed.

Definition lexord T (leT leT' : rel T) :=
  [rel x y | leT x y && (leT y x ==> leT' x y)].

Lemma lexord_total T (leT leT' : rel T) :
  total leT -> total leT' -> total (lexord leT leT').
Proof. exact: stablesort.lexord_total. Qed.

Lemma lexord_trans T (leT leT' : rel T) :
  transitive leT -> transitive leT' -> transitive (lexord leT leT').
Proof. exact: stablesort.lexord_trans. Qed.

Lemma lexord_irr T (leT leT' : rel T) :
  irreflexive leT' -> irreflexive (lexord leT leT').
Proof. exact: stablesort.lexord_irr. Qed.

Lemma lexordA T (leT leT' leT'' : rel T) :
  lexord leT (lexord leT' leT'') =2 lexord (lexord leT leT') leT''.
Proof. exact: stablesort.lexordA. Qed.

(**************************************************)
(* Appendix A.2: Lists and list surgery operators *)
(**************************************************)

Infix "::" := cons (only parsing) : seq_scope.

Notation "[ :: ]" := nil (at level 0, only parsing) : seq_scope.

Notation "[ :: x1 ]" := (x1 :: [::]) (at level 0, only parsing) : seq_scope.

Notation "[ :: x1 ; x2 ; .. ; xn ]" := (x1 :: x2 :: .. [:: xn] ..)
  (at level 0, only parsing) : seq_scope.

Canonical seq.seq_predType.

Definition cat T : list T -> list T -> list T :=
  fix cat (s1 s2 : list T) {struct s1} : list T :=
    if s1 is x :: s1' then x :: cat s1' s2 else s2.

Notation "s1 ++ s2" := (cat s1 s2) (only parsing) : seq_scope.

Lemma catA T (x y z : list T) : x ++ (y ++ z) = (x ++ y) ++ z.
Proof. exact: seq.catA. Qed.

Definition foldr T R (f : T -> R -> R) (z0 : R) : list T -> R :=
  fix foldr (s : list T) {struct s} : R :=
    if s is x :: s' then f x (foldr s') else z0.

Definition flatten T : list (list T) -> list T := foldr (@cat T) [::].

Definition catrev T : list T -> list T -> list T :=
  fix catrev (s1 s2 : list T) {struct s1} : list T :=
    if s1 is x :: s1' then catrev s1' (x :: s2) else s2.

Definition rev T (s : list T) : list T := catrev s [::].

Lemma catrevE T (s t : list T) : catrev s t = rev s ++ t.
Proof. exact: seq.catrevE. Qed.

Lemma revK T (s : list T) : rev (rev s) = s.
Proof. exact: seq.revK. Qed.

Lemma rev_cat T (s t : list T) : rev (s ++ t) = rev t ++ rev s.
Proof. exact: seq.rev_cat. Qed.

Definition take T : nat -> list T -> list T :=
  fix take (n : nat) (s : list T) {struct s} : list T :=
    match s, n with
    | [::], _ | _, 0 => nil
    | x :: s', S n' => x :: take n' s'
    end.

Definition drop T : nat -> list T -> list T :=
  fix drop (n : nat) (s : list T) {struct s} : list T :=
    match s, n with
    | [::], _ | _ :: _, 0 => s
    | _ :: s', S n' => drop n' s'
    end.

Lemma cat_take_drop (n : nat) T (s : list T) : take n s ++ drop n s = s.
Proof. exact: seq.cat_take_drop. Qed.

(***********************************)
(* Appendix A.3: Counting and size *)
(***********************************)

Definition count T (p : pred T) : list T -> nat :=
  foldr (fun x n => p x + n) 0.

Definition size T : list T -> nat := foldr (fun _ n => S n) 0.

Lemma count_predT T (s : list T) : count (fun _ => true) s = size s.
Proof. exact: seq.count_predT. Qed.

Lemma count_cat T (p : pred T) (s1 s2 : list T) :
  count p (s1 ++ s2) = count p s1 + count p s2.
Proof. exact: seq.count_cat. Qed.

Lemma count_rev T (p : pred T) (s : list T) : count p (rev s) = count p s.
Proof. exact: seq.count_rev. Qed.

(*************************************)
(* Appendix A.4: Predicates on lists *)
(*************************************)

Definition all T (p : pred T) : list T -> bool :=
  foldr (fun x b => p x && b) true.

Lemma all_count T (p : pred T) (s : list T) : all p s = (count p s == size s).
Proof. exact: seq.all_count. Qed.

Lemma all_cat T (p : pred T) (s1 s2 : list T) :
  all p (s1 ++ s2) = all p s1 && all p s2.
Proof. exact: seq.all_cat. Qed.

Lemma all_rev T (p : pred T) (s : list T) : all p (rev s) = all p s.
Proof. exact: seq.all_rev. Qed.

Lemma sub_all T (p1 p2 : pred T) :
  (forall x : T, p1 x -> p2 x) -> forall s : list T, all p1 s -> all p2 s.
Proof. exact: seq.sub_all. Qed.

(* For _in lemmas *)
Lemma allP (T : eqType) (p : pred T) (s : list T) :
  reflect {in s, forall x : T, p x} (all p s).
Proof. exact: seq.allP. Qed.

(* For _in lemmas *)
Lemma allss (T : eqType) (s : list T) : all [in s] s.
Proof. exact: seq.allss. Qed.

Definition allrel T S (r : T -> S -> bool) (xs : list T) (ys : list S) : bool :=
  all (fun x => all (r x) ys) xs.

Lemma allrelC T S (r : T -> S -> bool) (xs : list T) (ys : list S) :
  allrel r xs ys = allrel (fun x y => r y x) ys xs.
Proof. exact: seq.allrelC. Qed.

Lemma allrel_rev2 T S (r : T -> S -> bool) (s1 : list T) (s2 : list S) :
  allrel r (rev s1) (rev s2) = allrel r s1 s2.
Proof. exact: stablesort.allrel_rev2. Qed.

Definition uniq (T : eqType) : list T -> bool :=
  fix uniq (s : list T) {struct s} : bool :=
    if s is x :: s' then (x \notin s') && uniq s' else true.

(********************************)
(* Appendix A.5: Map and filter *)
(********************************)

Definition map T1 T2 (f : T1 -> T2) : list T1 -> list T2 :=
  foldr (fun x s => f x :: s) [::].

Definition filter T (p : pred T) : list T -> list T :=
  foldr (fun x s => if p x then x :: s else s) [::].

Notation "[ 'seq' x <- s | C ]" := (filter (fun x => C%B) s)
 (at level 0, x at level 99, only parsing) : seq_scope.

(* For _in lemmas *)
Lemma map_cat T1 T2 (f : T1 -> T2) (s1 s2 : list T1) :
  map f (cat s1 s2) = cat (map f s1) (map f s2).
Proof. exact: seq.map_cat. Qed.

Lemma filter_map T1 T2 (f : T1 -> T2) (p : pred T2) (s : list T1) :
  filter p (map f s) = map f (filter (fun x => p (f x)) s).
Proof. exact: seq.filter_map. Qed.

Lemma filter_all T (p : pred T) (s : list T) : all p (filter p s).
Proof. exact: seq.filter_all. Qed.

Lemma eq_filter T (p1 p2 : pred T) : p1 =1 p2 -> filter p1 =1 filter p2.
Proof. exact: seq.eq_filter. Qed.

Lemma mem_filter (T : eqType) (p : pred T) (x : T) (s : list T) :
  (x \in filter p s) = p x && (x \in s).
Proof. exact: seq.mem_filter. Qed.

(******************************)
(* Appendix A.6: Subsequences *)
(******************************)

Definition mask T : list bool -> list T -> list T :=
  fix mask (m : list bool) (s : list T) {struct m} : list T :=
    match m, s with
    | [::], _ | _, [::] => [::]
    | b :: m', x :: s' => if b then x :: mask m' s' else mask m' s'
    end.

Lemma mask0 T (m : list bool) : mask m [::] = [::] :> list T.
Proof. exact: seq.mask0. Qed.

(* For _in lemmas *)
Lemma all_mask T (p : pred T) (m : list bool) (s : list T) :
  all p s -> all p (mask m s).
Proof. exact: seq.all_mask. Qed.

Lemma map_mask T1 T2 (f : T1 -> T2) (m : list bool) (s : list T1) :
  map f (mask m s) = mask m (map f s).
Proof. exact: seq.map_mask. Qed.

Lemma filter_mask T (p : pred T) (s : list T) : filter p s = mask (map p s) s.
Proof. exact: seq.filter_mask. Qed.

Lemma mask_filter (T : eqType) (s : list T) (m : list bool) :
  uniq s -> mask m s = filter [in mask m s] s.
Proof. exact: seq.mask_filter. Qed.

Definition subseq (T : eqType) : list T -> list T -> bool :=
  fix subseq (s1 s2 : list T) {struct s2} : bool :=
    match s2, s1 with
      | _, [::] => true
      | [::], _ :: _ => false
      | y :: s2', x :: s1' => subseq (if x == y then s1' else s1) s2'
    end.

Lemma subseqP (T : eqType) (s1 s2 : list T) :
  reflect
    (exists2 m : list bool, size m = size s2 & s1 = mask m s2) (subseq s1 s2).
Proof. exact: seq.subseqP. Qed.

Lemma mask_subseq (T : eqType) (m : list bool) (s : list T) :
  subseq (mask m s) s.
Proof. exact: seq.mask_subseq. Qed.

(* For _in lemmas *)
Lemma mem_subseq (T : eqType) (s1 s2 : list T) :
  subseq s1 s2 -> {subset s1 <= s2}.
Proof. exact: seq.mem_subseq. Qed.

Definition index (T : eqType) (x : T) : list T -> nat :=
  fix find (s : list T) {struct s} : nat :=
    if s is y :: s' then
      if y == x then 0 else S (find s')
    else
      0.

Definition mem2 (T : eqType) (s : list T) (x y : T) : bool :=
  y \in drop (index x s) s.

Lemma mem2E (T : eqType) (s : list T) (x y : T) :
  mem2 s x y = subseq (if x == y then [:: x] else [:: x; y]) s.
Proof. exact: path.mem2E. Qed.

(*****************************)
(* Appendix A.7: Permutation *)
(*****************************)

Definition perm_eq (T : eqType) (s1 s2 : list T) : bool :=
  all [pred x | count (pred1 x) s1 == count (pred1 x) s2] (s1 ++ s2).

Notation perm_eql s1 s2 := (perm_eq s1 =1 perm_eq s2) (only parsing).

Lemma permP (T : eqType) (s1 s2 : list T) :
  reflect (forall p : pred T, count p s1 = count p s2) (perm_eq s1 s2).
Proof. exact: seq.permP. Qed.

Lemma permPl (T : eqType) (s1 s2 : list T) :
  reflect (perm_eql s1 s2) (perm_eq s1 s2).
Proof. exact: seq.permPl. Qed.

Lemma perm_mem (T : eqType) (s1 s2 : list T) : perm_eq s1 s2 -> s1 =i s2.
Proof. exact: seq.perm_mem. Qed.

(* For _in lemmas *)
Lemma perm_all (T : eqType) (s1 s2 : list T) (p : pred T) :
  perm_eq s1 s2 -> all p s1 = all p s2.
Proof. exact: seq.perm_all. Qed.

Lemma perm_uniq (T : eqType) (s1 s2 : list T) :
  perm_eq s1 s2 -> uniq s1 = uniq s2.
Proof. exact: seq.perm_uniq. Qed.

Lemma perm_cat (T : eqType) (s1 s2 t1 t2 : list T) :
  perm_eq s1 s2 -> perm_eq t1 t2 -> perm_eq (s1 ++ t1) (s2 ++ t2).
Proof. exact: seq.perm_cat. Qed.

Lemma perm_catC (T : eqType) (s1 s2 : list T) : perm_eql (s1 ++ s2) (s2 ++ s1).
Proof. exact: seq.perm_catC. Qed.

Lemma perm_rev (T : eqType) (s : list T) : perm_eql (rev s) s.
Proof. exact: seq.perm_rev. Qed.

(* For _in lemmas *)
Lemma perm_map_inj (T1 T2 : eqType) (f : T1 -> T2) :
  injective f ->
  forall s t : list T1, perm_eq (map f s) (map f t) -> perm_eq s t.
Proof. exact: seq.perm_map_inj. Qed.

(****************************)
(* Appendix A.8: Sortedness *)
(****************************)

Definition pairwise T (r : T -> T -> bool) : list T -> bool :=
  fix pairwise (xs : list T) {struct xs} : bool :=
    if xs is x :: xs0 then all (r x) xs0 && pairwise xs0 else true.

Lemma pairwise_cat T (r : T -> T -> bool) (s1 s2 : list T) :
  pairwise r (s1 ++ s2) = allrel r s1 s2 && (pairwise r s1 && pairwise r s2).
Proof. exact: seq.pairwise_cat. Qed.

(* For _in lemmas *)
Lemma pairwise_map T T' (f : T' -> T) (r : rel T) (xs : list T') :
  pairwise r (map f xs) = pairwise (relpre f r) xs.
Proof. exact: seq.pairwise_map. Qed.

Definition path T (e : rel T) : T -> list T -> bool :=
  fix path (x : T) (p : list T) {struct p} : bool :=
    if p is y :: p' then e x y && path y p' else true.

Definition sorted T (e : rel T) (s : list T) : bool :=
  if s is x :: s' then path e x s' else true.

Lemma pairwise_sorted T (r : rel T) (s : list T) : pairwise r s -> sorted r s.
Proof. exact: path.pairwise_sorted. Qed.

Lemma sorted_pairwise T (r : rel T) :
  transitive r -> forall s : list T, sorted r s = pairwise r s.
Proof. exact: path.sorted_pairwise. Qed.

Lemma path_sorted T (e : rel T) (x : T) (s : list T) : path e x s -> sorted e s.
Proof. exact: path.path_sorted. Qed.

Lemma rev_sorted T (r : rel T) (s : list T) :
  sorted r (rev s) = sorted (fun x y : T => r y x) s.
Proof. exact: path.rev_sorted. Qed.

Lemma sub_sorted T (e e' : rel T) :
  (forall x y : T, e x y -> e' x y) -> forall s, sorted e s -> sorted e' s.
Proof. exact: path.sub_sorted. Qed.

Lemma eq_sorted T (e e' : rel T) : e =2 e' -> sorted e =1 sorted e'.
Proof. exact: path.eq_sorted. Qed.

(* For _in lemmas *)
Lemma sorted_map T T' (f : T -> T') (r : rel T') (s : list T) :
  sorted r (map f s) = sorted (relpre f r) s.
Proof. exact: path.sorted_map. Qed.

Lemma sorted_filter T (r : rel T) : transitive r ->
  forall (p : pred T) (s : list T), sorted r s -> sorted r (filter p s).
Proof. exact: path.sorted_filter. Qed.

Lemma sorted_eq (T : eqType) (leT : rel T) :
  transitive leT -> antisymmetric leT ->
  forall s1 s2 : list T,
    sorted leT s1 -> sorted leT s2 -> perm_eq s1 s2 -> s1 = s2.
Proof. exact: path.sorted_eq. Qed.

Lemma irr_sorted_eq (T : eqType) (leT : rel T) :
  transitive leT -> irreflexive leT ->
  forall s1 s2 : list T, sorted leT s1 -> sorted leT s2 -> s1 =i s2 -> s1 = s2.
Proof. exact: path.irr_sorted_eq. Qed.

(**************************)
(* Appendix A.9: Indexing *)
(**************************)

Fixpoint iota (m n : nat) {struct n} : list nat :=
  if n is S n' then m :: iota (S m) n' else [::].

Definition nth T (x0 : T) : list T -> nat -> T :=
  fix nth (s : list T) (n : nat) {struct n} : T :=
    match s, n with
    | [::], _ => x0
    | x :: _, 0 => x
    | _ :: s', S n' => nth s' n'
    end.

Lemma iota_uniq (m n : nat) : uniq (iota m n).
Proof. exact: seq.iota_uniq. Qed.

Lemma mkseq_nth T (x0 : T) (s : list T) : map (nth x0 s) (iota 0 (size s)) = s.
Proof. exact: seq.mkseq_nth. Qed.

Lemma iota_ltn_sorted (i n : nat) : sorted ltn (iota i n).
Proof. exact: path.iota_ltn_sorted. Qed.

(************************)
(* Appendix A.10: Merge *)
(************************)

Definition merge T (leT : rel T) :=
  fix merge (s1 : list T) {struct s1} : list T -> list T :=
    match s1 with
    | [::] => id
    | x1 :: s1' =>
      fix merge_s1 (s2 : list T) {struct s2} : list T :=
        match s2 with
        | [::] => s1
        | x2 :: s2' =>
          if leT x1 x2 then x1 :: merge s1' s2 else x2 :: merge_s1 s2'
        end
    end.

Arguments merge T leT !s1 !s2.

Lemma count_merge T (leT : rel T) (p : pred T) (s1 s2 : list T) :
  count p (merge leT s1 s2) = count p (s1 ++ s2).
Proof. exact: stablesort.count_merge. Qed.

Lemma all_merge T (p : pred T) (leT : rel T) (s1 s2 : list T) :
  all p (merge leT s1 s2) = all p s1 && all p s2.
Proof. exact: path.all_merge. Qed.

Lemma perm_merge (T : eqType) (r : rel T) (s1 s2 : list T) :
  perm_eql (merge r s1 s2) (s1 ++ s2).
Proof. exact: path.perm_merge. Qed.

Lemma allrel_merge T (leT : rel T) (s1 s2 : list T) :
  allrel leT s1 s2 -> merge leT s1 s2 = s1 ++ s2.
Proof. exact: path.allrel_merge. Qed.

Lemma merge_stable_sorted T (r r' : rel T) :
  total r -> forall s1 s2 : list T,
  allrel r' s1 s2 -> sorted (lexord r r') s1 -> sorted (lexord r r') s2 ->
  sorted (lexord r r') (merge r s1 s2).
Proof. exact: path.merge_stable_sorted. Qed.

Lemma mergeA T (leT : rel T) :
  total leT -> transitive leT -> associative (merge leT).
Proof. exact: path.mergeA. Qed.

(* For _in lemmas *)
Lemma merge_map T T' (f : T' -> T) (leT : rel T) (s1 s2 : list T') :
  merge leT (map f s1) (map f s2) = map f (merge (relpre f leT) s1 s2).
Proof. exact: path.merge_map. Qed.

(******************************)
(* Appendix A.11: Sigma types *)
(******************************)

Lemma in2_sig T1 T2 (D1 : pred T1) (D2 : pred T2) (P2 : T1 -> T2 -> Prop) :
  {in D1 & D2, forall (x : T1) (y : T2), P2 x y} ->
  forall (x : sig D1) (y : sig D2), P2 (val x) (val y).
Proof. exact: in2_sig. Qed.

Lemma in3_sig
    T1 T2 T3 (D1 : pred T1) (D2 : pred T2) (D3 : pred T3)
    (P3 : T1 -> T2 -> T3 -> Prop) :
  {in D1 & D2 & D3, forall (x : T1) (y : T2) (z : T3), P3 x y z} ->
  forall (x : sig D1) (y : sig D2) (z : sig D3), P3 (val x) (val y) (val z).
Proof. exact: in3_sig. Qed.

Lemma all_sigP T (p : pred T) (s : list T) :
  all p s -> {s' : list (sig p) | s = map val s'}.
Proof. exact: seq.all_sigP. Qed.

(******************************************************************************)
(* Appendix B: The theory of stable sort functions                            *)
(******************************************************************************)

Lemma sort_ind sort T (leT : rel T) (R : list T -> list T -> Prop) :
  (forall xs xs' : list T, R xs xs' -> forall ys ys' : list T, R ys ys' ->
    R (xs ++ ys) (merge leT xs' ys')) ->
  (forall xs xs' : list T, R xs xs' -> forall ys ys' : list T, R ys ys' ->
    R (xs ++ ys) (rev (merge (fun x y => leT y x) (rev ys') (rev xs')))) ->
  (forall x : T, R [:: x] [:: x]) ->
  R nil nil ->
  forall s : list T, R s (sort T leT s).
Proof. exact: stablesort.sort_ind. Qed.

Lemma map_sort sort T T' (f : T' -> T) (leT' : rel T') (leT : rel T) :
  (forall x y : T', leT (f x) (f y) = leT' x y) ->
  forall s : list T', map f (sort T' leT' s) = sort T leT (map f s).
Proof. exact: stablesort.map_sort. Qed.

Lemma sort_map sort T T' (f : T' -> T) (leT : rel T) (s : list T') :
  sort T leT (map f s) = map f (sort T' (relpre f leT) s).
Proof. exact: stablesort.sort_map. Qed.

Lemma pairwise_sort sort T (leT : rel T) (s : list T) :
  pairwise leT s -> sort T leT s = s.
Proof.
exact: stablesort.pairwise_sort.
Restart.
elim/sort_ind: (sort _ leT s) => // xs xs' IHxs ys ys' IHys.
  by rewrite pairwise_cat => /and3P[/allrel_merge <- /IHxs -> /IHys ->].
rewrite pairwise_cat allrelC -allrel_rev2 => /and3P[hlr /IHxs -> /IHys ->].
by rewrite allrel_merge // rev_cat !revK.
Qed.

Lemma sorted_sort sort T (leT : rel T) :
  transitive leT -> forall s : list T, sorted leT s -> sort T leT s = s.
Proof.
exact: stablesort.sorted_sort.
Restart.
by move=> leT_tr s; rewrite sorted_pairwise //; apply/pairwise_sort.
Qed.

Lemma sorted_sort_in sort T (P : pred T) (leT : rel T) :
  {in P & &, transitive leT} ->
  forall s : list T, all P s -> sorted leT s -> sort T leT s = s.
Proof.
exact: stablesort.sorted_sort_in.
Restart.
move=> /in3_sig ? _ /all_sigP[s ->].
by rewrite sort_map sorted_map => /sorted_sort->.
Qed.

Lemma sort_pairwise_stable sort T (leT leT' : rel T) : total leT ->
  forall s : list T, pairwise leT' s -> sorted (lexord leT leT') (sort T leT s).
Proof.
exact: stablesort.sort_pairwise_stable.
Restart.
move=> leT_total s.
suff: (forall P, all P s -> all P (sort T leT s)) /\
        (pairwise leT' s -> sorted (lexord leT leT') (sort T leT s)).
  by case.
elim/sort_ind: (sort _ leT s) => // xs xs' [IHxs IHxs'] ys ys' [IHys IHys'];
  rewrite pairwise_cat; split => [P|/and3P[hlr /IHxs' ? /IHys' ?]].
- by rewrite all_cat all_merge => /andP[/IHxs -> /IHys ->].
- apply/merge_stable_sorted => //=.
  by apply/IHxs; apply/sub_all: hlr => ?; apply/IHys.
- by rewrite all_cat all_rev all_merge !all_rev => /andP[/IHxs -> /IHys ->].
- rewrite rev_sorted; apply/merge_stable_sorted; rewrite ?rev_sorted //.
  rewrite allrel_rev2 allrelC.
  by apply/IHxs; apply/sub_all: hlr => ?; apply/IHys.
Qed.

Lemma sort_pairwise_stable_in sort T (P : pred T) (leT leT' : rel T) :
  {in P &, total leT} -> forall s : list T, all P s -> pairwise leT' s ->
  sorted (lexord leT leT') (sort T leT s).
Proof.
exact: stablesort.sort_pairwise_stable_in.
Restart.
move=> /in2_sig leT_total _ /all_sigP[s ->].
by rewrite sort_map pairwise_map sorted_map; apply: sort_pairwise_stable.
Qed.

Lemma sort_stable sort T (leT leT' : rel T) : total leT -> transitive leT' ->
  forall s : list T, sorted leT' s -> sorted (lexord leT leT') (sort T leT s).
Proof.
exact: stablesort.sort_stable.
Restart.
by move=> ? ? s; rewrite sorted_pairwise//; apply: sort_pairwise_stable.
Qed.

Lemma sort_stable_in sort T (P : pred T) (leT leT' : rel T) :
  {in P &, total leT} -> {in P & &, transitive leT'} ->
  forall s : list T, all P s -> sorted leT' s ->
  sorted (lexord leT leT') (sort T leT s).
Proof.
exact: stablesort.sort_stable_in.
Restart.
move=> /in2_sig leT_total /in3_sig leT_tr _ /all_sigP[s ->].
by rewrite sort_map !sorted_map; apply: sort_stable.
Qed.

Lemma count_sort sort T (leT : rel T) (p : pred T) (s : list T) :
  count p (sort T leT s) = count p s.
Proof.
exact: stablesort.count_sort.
Restart.
by elim/sort_ind: (sort _ leT s) => // xs xs' IHxs ys ys' IHys;
  rewrite ?count_rev count_merge !count_cat ?count_rev IHxs IHys // addnC.
Qed.

Lemma size_sort sort T (leT : rel T) (s : list T) :
  size (sort T leT s) = size s.
Proof.
exact: stablesort.size_sort.
Restart.
exact: (count_sort sort leT predT).
Qed.

Lemma sort_nil sort T (leT : rel T) : sort T leT [::] = [::].
Proof.
exact: stablesort.sort_nil.
Restart.
by case: (sort _) (size_sort sort leT [::]).
Qed.

Lemma all_sort sort T (p : pred T) (leT : rel T) (s : list T) :
  all p (sort T leT s) = all p s.
Proof.
exact: stablesort.all_sort.
Restart.
by rewrite !all_count count_sort size_sort.
Qed.

Lemma perm_sort sort (T : eqType) (leT : rel T) (s : list T) :
  perm_eql (sort T leT s) s.
Proof.
exact: stablesort.perm_sort.
Restart.
by apply/permPl/permP => ?; rewrite count_sort.
Qed.

Lemma mem_sort sort (T : eqType) (leT : rel T) (s : list T) : sort T leT s =i s.
Proof.
exact: stablesort.mem_sort.
Restart.
exact/perm_mem/permPl/perm_sort.
Qed.

Lemma sort_uniq sort (T : eqType) (leT : rel T) (s : list T) :
  uniq (sort T leT s) = uniq s.
Proof.
exact: stablesort.sort_uniq.
Restart.
exact/perm_uniq/permPl/perm_sort.
Qed.

Lemma filter_sort sort T (leT : rel T) : total leT -> transitive leT ->
  forall (p : pred T) (s : list T),
  filter p (sort T leT s) = sort T leT (filter p s).
Proof.
exact: stablesort.filter_sort.
Restart.
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

Lemma filter_sort_in sort T (P : pred T) (leT : rel T) :
  {in P &, total leT} -> {in P & &, transitive leT} ->
  forall (p : pred T) (s : list T),
  all P s -> filter p (sort T leT s) = sort T leT (filter p s).
Proof.
exact: stablesort.filter_sort_in.
Restart.
move=> /in2_sig leT_total /in3_sig leT_tr p _ /all_sigP[s ->].
by rewrite !(sort_map, filter_map) filter_sort.
Qed.

Lemma sorted_filter_sort sort T (leT : rel T) :
  total leT -> transitive leT ->
  forall (p : pred T) (s : list T),
  sorted leT (filter p s) -> filter p (sort _ leT s) = filter p s.
Proof.
exact: stablesort.sorted_filter_sort.
Restart.
by move=> *; rewrite filter_sort// sorted_sort.
Qed.

Lemma sorted_filter_sort_in sort T (P : {pred T}) (leT : rel T) :
  {in P &, total leT} -> {in P & &, transitive leT} ->
  forall (p : pred T) (s : list T),
  all P s -> sorted leT (filter p s) -> filter p (sort _ leT s) = filter p s.
Proof.
exact: stablesort.sorted_filter_sort_in.
Restart.
move=> /in2_sig leT_total /in3_sig leT_tr p _ /all_sigP[s ->].
by rewrite sort_map !filter_map sorted_map /= => /sorted_filter_sort ->.
Qed.

Lemma sort_sort sort T (leT leT' : rel T) :
  total leT -> transitive leT -> total leT' -> transitive leT' ->
  forall s : list T, sort T leT (sort T leT' s) = sort T (lexord leT leT') s.
Proof.
exact: stablesort.sort_sort.
Restart.
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

Lemma sort_sort_in sort T (P : pred T) (leT leT' : rel T) :
  {in P &, total leT} -> {in P & &, transitive leT} ->
  {in P &, total leT'} -> {in P & &, transitive leT'} ->
  forall s : list T,
  all P s -> sort T leT (sort T leT' s) = sort T (lexord leT leT') s.
Proof.
exact: stablesort.sort_sort_in.
Restart.
move=> /in2_sig leT_total /in3_sig leT_tr /in2_sig leT'_total /in3_sig leT'_tr.
by move=> _ /all_sigP[s ->]; rewrite !sort_map sort_sort.
Qed.

Lemma sort_sorted sort T (leT : rel T) :
  total leT -> forall s : list T, sorted leT (sort T leT s).
Proof.
exact: stablesort.sort_sorted.
Restart.
move=> leT_total s; apply/sub_sorted/sort_stable => //= [? ? /andP[] //|].
by case: s => // x s; elim: s x => /=.
Qed.

Lemma sort_sorted_in sort T (P : pred T) (leT : rel T) :
  {in P &, total leT} ->
  forall s : list T, all P s -> sorted leT (sort T leT s).
Proof.
exact: stablesort.sort_sorted_in.
Restart.
by move=> /in2_sig ? _ /all_sigP[s ->]; rewrite sort_map sorted_map sort_sorted.
Qed.

Lemma perm_sortP sort (T : eqType) (leT : rel T) :
  total leT -> transitive leT -> antisymmetric leT ->
  forall s1 s2 : list T,
  reflect (sort T leT s1 = sort T leT s2) (perm_eq s1 s2).
Proof.
exact: stablesort.perm_sortP.
Restart.
move=> leT_total leT_tr leT_asym s1 s2.
apply: (iffP idP) => eq12; last by rewrite -(perm_sort sort leT) eq12 perm_sort.
apply: (sorted_eq leT_tr leT_asym); rewrite ?sort_sorted //.
by rewrite perm_sort (permPl _ _ eq12) -(perm_sort sort leT).
Qed.

Lemma perm_sort_inP sort (T : eqType) (leT : rel T) (s1 s2 : list T) :
  {in s1 &, total leT} -> {in s1 & &, transitive leT} ->
  {in s1 &, antisymmetric leT} ->
  reflect (sort T leT s1 = sort T leT s2) (perm_eq s1 s2).
Proof.
exact: stablesort.perm_sort_inP.
Restart.
move=> /in2_sig leT_total /in3_sig leT_tr /in2_sig/(_ _ _ _)/val_inj leT_asym.
apply: (iffP idP) => s1s2; last by rewrite -(perm_sort sort leT) s1s2 perm_sort.
move: (s1s2); have /all_sigP[s1' ->] := allss s1.
have /all_sigP[{s1s2}s2 ->] : all (mem s1) s2.
  by rewrite -(perm_all _ s1s2) allss.
by rewrite !sort_map => /(perm_map_inj val_inj) /(perm_sortP sort leT_total)->.
Qed.

Lemma eq_sort sort1 sort2 T (leT : rel T) :
  total leT -> transitive leT -> sort1 T leT =1 sort2 T leT.
Proof.
exact: stablesort.eq_sort.
Restart.
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

Lemma eq_in_sort sort1 sort2 T (P : pred T) (leT : rel T) :
  {in P &, total leT} -> {in P & &, transitive leT} ->
  forall s : list T, all P s -> sort1 T leT s = sort2 T leT s.
Proof.
exact: stablesort.eq_in_sort.
Restart.
move=> /in2_sig ? /in3_sig ? _ /all_sigP[s ->].
by rewrite !sort_map; congr map; exact: eq_sort.
Qed.

Lemma eq_sort_insert sort T (leT : rel T) : total leT -> transitive leT ->
  sort T leT =1 foldr (fun x : T => merge leT [:: x]) [::].
Proof.
exact: stablesort.eq_sort_insert.
Qed.

Lemma eq_in_sort_insert sort T (P : pred T) (leT : rel T) :
  {in P &, total leT} -> {in P & &, transitive leT} ->
  forall s : list T, all P s ->
  sort T leT s = foldr (fun x : T => merge leT [:: x]) [::] s.
Proof.
exact: stablesort.eq_in_sort_insert.
Qed.

Lemma sort_cat sort T (leT : rel T) : total leT -> transitive leT ->
  forall s1 s2 : list T,
  sort T leT (s1 ++ s2) = merge leT (sort T leT s1) (sort T leT s2).
Proof.
exact: stablesort.sort_cat.
Restart.
move=> leT_total leT_tr s1 s2.
by rewrite !eq_sort_insert; elim: s1 => //= x s1 ->; rewrite mergeA.
Qed.

Lemma sort_cat_in sort T (P : pred T) (leT : rel T) :
  {in P &, total leT} -> {in P & &, transitive leT} ->
  forall s1 s2 : list T, all P s1 -> all P s2 ->
  sort T leT (s1 ++ s2) = merge leT (sort T leT s1) (sort T leT s2).
Proof.
exact: stablesort.sort_cat_in.
Restart.
move=> leT_total leT_tr s1 s2 /all_sigP [{}s1 ->] /all_sigP [{}s2 ->].
rewrite -map_cat !sort_map merge_map; congr map; apply: sort_cat.
  exact: in2_sig leT_total.
exact: in3_sig leT_tr.
Qed.

Lemma mask_sort sort T (leT : rel T) : total leT -> transitive leT ->
  forall (s : list T) (m : list bool),
  {m_s : list bool | mask m_s (sort T leT s) = sort T leT (mask m s)}.
Proof.
exact: stablesort.mask_sort.
Restart.
move=> leT_total leT_tr s m.
case Ds: {-}s => [|x s1]; first by exists [::]; rewrite Ds mask0 sort_nil.
rewrite -(mkseq_nth x s) -map_mask !sort_map.
exists (map (mem (mask m (iota 0 (size s))))
            (sort _ (xrelpre (nth x s) leT) (iota 0 (size s)))).
rewrite -map_mask -filter_mask [in RHS]mask_filter ?iota_uniq ?filter_sort //.
by move=> ? ? ?; exact: leT_tr.
Qed.

Lemma mask_sort_in sort T (P : pred T) (leT : rel T) :
  {in P &, total leT} -> {in P & &, transitive leT} ->
  forall (s : list T) (m : list bool), all P s ->
  {m_s : list bool | mask m_s (sort T leT s) = sort T leT (mask m s)}.
Proof.
exact: stablesort.mask_sort_in.
Restart.
move=> leT_total leT_tr s m.
pose le_sT := relpre (val : sig P -> _) leT.
pose le_sT_total : total le_sT := in2_sig leT_total.
pose le_sT_tr : transitive le_sT := in3_sig leT_tr.
move=> /all_sigP [{}s ->].
case: (mask_sort sort le_sT_total le_sT_tr s m) => //.
by move=> m' m'E; exists m'; rewrite -map_mask !sort_map -map_mask m'E.
Qed.

Lemma sorted_mask_sort sort T (leT : rel T) : total leT -> transitive leT ->
  forall (s : list T) (m : list bool), sorted leT (mask m s) ->
  {m_s : list bool | mask m_s (sort T leT s) = mask m s}.
Proof.
exact: stablesort.sorted_mask_sort.
Restart.
move=> leT_total leT_tr s m.
by move/(sorted_sort sort leT_tr) <-; exact: mask_sort.
Qed.

Lemma sorted_mask_sort_in sort T (P : pred T) (leT : rel T) :
  {in P &, total leT} -> {in P & &, transitive leT} ->
  forall (s : list T) (m : list bool), all P s -> sorted leT (mask m s) ->
  {m_s : list bool | mask m_s (sort T leT s) = mask m s}.
Proof.
exact: stablesort.sorted_mask_sort_in.
Restart.
move=> leT_total leT_tr s m allPs /(sorted_sort_in sort leT_tr _) <-.
  exact/mask_sort_in/allPs.
exact: all_mask.
Qed.

Lemma subseq_sort sort (T : eqType) (leT : rel T) :
  total leT -> transitive leT ->
  forall t s : list T, subseq t s -> subseq (sort T leT t) (sort T leT s).
Proof.
exact: stablesort.subseq_sort.
Restart.
move=> leT_total leT_tr _ s /subseqP [m _ ->].
by have [m' <-] := mask_sort sort leT_total leT_tr s m; exact: mask_subseq.
Qed.

Lemma subseq_sort_in sort (T : eqType) (leT : rel T) (t s : list T) :
  {in s &, total leT} -> {in s & &, transitive leT} ->
  subseq t s -> subseq (sort T leT t) (sort T leT s).
Proof.
exact: stablesort.subseq_sort_in.
Restart.
move=> leT_total leT_tr /subseqP [m _ ->].
have [m' <-] := mask_sort_in sort leT_total leT_tr m (allss _).
exact: mask_subseq.
Qed.

Lemma sorted_subseq_sort sort (T : eqType) (leT : rel T) :
  total leT -> transitive leT ->
  forall t s : list T, subseq t s -> sorted leT t -> subseq t (sort T leT s).
Proof.
exact: stablesort.sorted_subseq_sort.
Restart.
move=> ? leT_tr t s subseq_ts /(sorted_sort sort leT_tr) <-.
exact: subseq_sort.
Qed.

Lemma sorted_subseq_sort_in sort (T : eqType) (leT : rel T) (t s : list T) :
  {in s &, total leT} -> {in s & &, transitive leT} ->
  subseq t s -> sorted leT t -> subseq t (sort T leT s).
Proof.
exact: stablesort.sorted_subseq_sort_in.
Restart.
move=> ? leT_tr ? /(sorted_sort_in sort leT_tr) <-; last exact/allP/mem_subseq.
exact: subseq_sort_in.
Qed.

Lemma mem2_sort sort (T : eqType) (leT : rel T) :
  total leT -> transitive leT ->
  forall (s : list T) (x y : T),
  leT x y -> mem2 s x y -> mem2 (sort T leT s) x y.
Proof.
exact: stablesort.mem2_sort.
Restart.
move=> leT_total leT_tr s x y lexy; rewrite !mem2E => ?.
by apply: sorted_subseq_sort => //; case: (_ == _); rewrite //= lexy.
Qed.

Lemma mem2_sort_in sort (T : eqType) (leT : rel T) (s : list T) :
  {in s &, total leT} -> {in s & &, transitive leT} ->
  forall x y : T, leT x y -> mem2 s x y -> mem2 (sort T leT s) x y.
Proof.
exact: stablesort.mem2_sort_in.
Restart.
move=> leT_total leT_tr x y lexy; rewrite !mem2E.
move=> /[dup] /mem_subseq /allP ? /(subseq_sort_in sort leT_total leT_tr).
rewrite !(eq_in_sort_insert sort leT_total leT_tr) ?allss //.
by case: (_ == _); rewrite /= ?lexy; apply.
Qed.
