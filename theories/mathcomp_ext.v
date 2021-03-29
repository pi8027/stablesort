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

Lemma sorted_pairwise (T : Type) (leT : rel T) :
  transitive leT -> forall s : seq T, sorted leT s = pairwise leT s.
Proof.
by move=> leT_tr; elim => //= x s <-; rewrite path_sortedE.
Qed.

Lemma pairwise_sorted (T : Type) (leT : rel T) (s : seq T) :
  pairwise leT s -> sorted leT s.
Proof. by elim: s => //= x s IHs /andP[/path_min_sorted -> /IHs]. Qed.

Lemma path_relI (T : Type) (leT leT' : rel T) (x : T) (s : seq T) :
  path leT x s && path leT' x s = path [rel x y | leT x y && leT' x y] x s.
Proof. by elim: s x => //= y s IHs x; rewrite andbACA IHs. Qed.

Lemma sorted_relI (T : Type) (leT leT' : rel T) (s : seq T) :
  sorted leT s && sorted leT' s = sorted [rel x y | leT x y && leT' x y] s.
Proof. by case: s; last apply: path_relI. Qed.

Lemma nilp_rev (T : Type) (s : seq T) : nilp (rev s) = nilp s.
Proof. by move: s (rev s) (size_rev s) => [|? ?] []. Qed.

Lemma ifnilE (T A : Type) (s : seq T) (a b : A) :
  (if s is [::] then a else b) = if nilp s then a else b.
Proof. by case: s. Qed.
