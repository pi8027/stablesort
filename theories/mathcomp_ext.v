From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition pairwise {T : Type} (r : rel T) :=
  fix pairwise (xs : seq T) : bool :=
    if xs is x :: xs then all (r x) xs && pairwise xs else true.

Lemma pairwise_cat {T : Type} (r : rel T) (xs ys : seq T) :
  pairwise r (xs ++ ys) = [&& allrel r xs ys, pairwise r xs & pairwise r ys].
Proof. by elim: xs => //= x xs ->; rewrite all_cat -!andbA; bool_congr. Qed.

Lemma pairwise_map {T T' : Type} (f : T' -> T) (r : rel T) xs :
  pairwise r (map f xs) = pairwise (relpre f r) xs.
Proof. by elim: xs => //= x xs ->; rewrite all_map. Qed.

Lemma mergeA (T : Type) (leT : rel T) :
  total leT -> transitive leT -> associative (merge leT).
Proof.
move=> leT_total leT_tr.
elim=> // x xs IHxs; elim=> // y ys IHys; elim=> [|z zs IHzs] /=.
  by case: ifP.
case: ifP; case: ifP => /= lexy leyz.
- by rewrite lexy (leT_tr _ _ _ lexy leyz) -IHxs /= leyz.
- by rewrite lexy leyz -IHys.
- case: ifP => lexz; first by rewrite -IHxs //= leyz.
  by rewrite -!/(merge _ (_ :: _)) IHzs /= lexy.
- suff->: leT x z = false by rewrite leyz // -!/(merge _ (_ :: _)) IHzs /= lexy.
by apply/contraFF/leT_tr: leyz; have := leT_total x y; rewrite lexy.
Qed.

Lemma all_merge (T : Type) (P : {pred T}) (leT : rel T) (s1 s2 : seq T) :
  all P (merge leT s1 s2) = all P s1 && all P s2.
Proof.
elim: s1 s2 => //= x s1 IHs1; elim=> [|y s2 IHs2]; rewrite ?andbT //=.
by case: ifP => _; rewrite /= ?IHs1 ?IHs2 //=; bool_congr.
Qed.

Lemma allrel_merge (T : Type) (leT : rel T) s1 s2 :
  allrel leT s1 s2 -> merge leT s1 s2 = s1 ++ s2.
Proof.
elim: s1 s2 => [|x s1 IHs1] [|y s2]; rewrite ?cats0 //=.
by rewrite allrel_consl /= -andbA => /and3P [-> _ /IHs1->].
Qed.

Lemma eq_sorted (T : Type) (e e' : rel T) : e =2 e' -> sorted e =1 sorted e'.
Proof. by move=> ee' [] //; apply: eq_path. Qed.

Lemma sorted_pairwise (T : Type) (leT : rel T) :
  transitive leT -> forall s : seq T, sorted leT s = pairwise leT s.
Proof.
by move=> leT_tr; elim => //= x s <-; rewrite path_sortedE.
Qed.

Lemma pairwise_sorted (T : Type) (leT : rel T) (s : seq T) :
  pairwise leT s -> sorted leT s.
Proof. by elim: s => //= x s IHs /andP[/path_min_sorted -> /IHs]. Qed.

Lemma path_relI (T : Type) (leT leT' : rel T) (x : T) (s : seq T) :
  path [rel x y | leT x y && leT' x y] x s = path leT x s && path leT' x s.
Proof. by elim: s x => //= y s IHs x; rewrite andbACA IHs. Qed.

Lemma sorted_relI (T : Type) (leT leT' : rel T) (s : seq T) :
  sorted [rel x y | leT x y && leT' x y] s = sorted leT s && sorted leT' s.
Proof. by case: s; last apply: path_relI. Qed.

Lemma nilp_rev (T : Type) (s : seq T) : nilp (rev s) = nilp s.
Proof. by move: s (rev s) (size_rev s) => [|? ?] []. Qed.

Lemma ifnilE (T A : Type) (s : seq T) (a b : A) :
  (if s is [::] then a else b) = if nilp s then a else b.
Proof. by case: s. Qed.

Lemma relpre_trans {T' T : Type} {leT : rel T} {f : T' -> T} :
  transitive leT -> transitive (relpre f leT).
Proof. by move=> + y x z; apply. Qed.

Lemma allrel_revl {T S : Type} (r : T -> S -> bool) (s1 : seq T) (s2 : seq S) :
  allrel r (rev s1) s2 = allrel r s1 s2.
Proof. exact: all_rev. Qed.

Lemma allrel_revr {T S : Type} (r : T -> S -> bool) (s1 : seq T) (s2 : seq S) :
  allrel r s1 (rev s2) = allrel r s1 s2.
Proof. by rewrite allrelC allrel_revl allrelC. Qed.

Lemma allrel_rev2 {T S : Type} (r : T -> S -> bool) (s1 : seq T) (s2 : seq S) :
  allrel r (rev s1) (rev s2) = allrel r s1 s2.
Proof. by rewrite allrel_revr allrel_revl. Qed.

Lemma eq_allrel_l {T : eqType} {S} (r : T -> S -> bool) (s1 s1' : seq T) s2 :
  s1 =i s1' -> allrel r s1 s2 = allrel r s1' s2.
Proof. by move=> eqs1; apply: eq_all_r. Qed.

Lemma eq_allrel_r {T} {S : eqType} (r : T -> S -> bool) s1 (s2 s2' : seq S) :
  s2 =i s2' -> allrel r s1 s2 = allrel r s1 s2'.
Proof. by rewrite ![allrel _ s1 _]allrelC; apply: eq_allrel_l. Qed.

Lemma eq_allrel2 {T S : eqType} (r : T -> S -> bool)
    (s1 s1' : seq T) (s2 s2' : seq S) :
  s1 =i s1' -> s2 =i s2' -> allrel r s1 s2 = allrel r s1' s2'.
Proof. by move=> /eq_allrel_l -> /eq_allrel_r ->. Qed.

Section MergeProps.
Context {T : Type} {leT : rel T}.
Implicit Type s : seq T.

Lemma merge0s s : merge leT [::] s = s. Proof. by elim: s. Qed.
Lemma merges0 s : merge leT s [::] = s. Proof. by elim: s. Qed.

Lemma merge_cons x y s s' : merge leT (x :: s) (y :: s') =
  if leT x y then x :: merge leT s (y :: s') else y :: merge leT (x :: s) s'.
Proof. by []. Qed.

Lemma merge_eq0P s1 s2 : (merge leT s1 s2 = [::]) <-> (s1 = [::]) /\ (s2 = [::]).
Proof.
elim: s1 => [|x s1 IHs1]/= in s2 *; rewrite /= ?merge0s; first by split=> // -[].
case: s2 => [|y s2]; first by split=> // -[].
by rewrite merge_cons; case: ifP => //=; split=> // -[].
Qed.

End MergeProps.
