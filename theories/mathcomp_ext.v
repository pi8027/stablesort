From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition lexord (T : Type) (leT leT' : rel T) :=
  [rel x y | leT x y && (leT y x ==> leT' x y)].

Lemma lexord_total (T : Type) (leT leT' : rel T) :
  total leT -> total leT' -> total (lexord leT leT').
Proof.
move=> leT_total leT'_total x y /=.
by move: (leT_total x y) (leT'_total x y) => /orP[->|->] /orP[->|->];
  rewrite /= ?implybE ?orbT ?andbT //= (orbAC, orbA) (orNb, orbN).
Qed.

Lemma lexord_trans (T : Type) (leT leT' : rel T) :
  transitive leT -> transitive leT' -> transitive (lexord leT leT').
Proof.
move=> leT_tr leT'_tr y x z /= /andP[lexy leyx] /andP[leyz lezy].
rewrite (leT_tr _ _ _ lexy leyz); apply/implyP => lezx; move: leyx lezy.
by rewrite (leT_tr _ _ _ leyz lezx) (leT_tr _ _ _ lezx lexy); exact: leT'_tr.
Qed.

Lemma lexord_irr (T : Type) (leT leT' : rel T) :
  irreflexive leT' -> irreflexive (lexord leT leT').
Proof. by move=> irr x /=; rewrite irr implybF andbN. Qed.

Lemma lexordA (T : Type) (leT leT' leT'' : rel T) :
  lexord leT (lexord leT' leT'') =2 lexord (lexord leT leT') leT''.
Proof. by move=> x y /=; case: (leT x y) (leT y x) => [] []. Qed.

Definition condrev (T : Type) (r : bool) (xs : seq T) : seq T :=
  if r then rev xs else xs.

Lemma condrev_nilp (T : Type) (r : bool) (xs : seq T) :
  nilp (condrev r xs) = nilp xs.
Proof. by case: r; rewrite /= ?rev_nilp. Qed.

Lemma relpre_trans {T' T} {leT : rel T} {f : T' -> T} :
  transitive leT -> transitive (relpre f leT).
Proof. by move=> + y x z; apply. Qed.

Lemma allrel_rev2 {T S} (r : T -> S -> bool) (s1 : seq T) (s2 : seq S) :
  allrel r (rev s1) (rev s2) = allrel r s1 s2.
Proof. by rewrite [LHS]all_rev [LHS]allrelC [RHS]allrelC [LHS]all_rev. Qed.

Lemma count_merge (T : Type) (leT : rel T) (p : pred T) (s1 s2 : seq T) :
  count p (merge leT s1 s2) = count p (s1 ++ s2).
Proof.
rewrite count_cat; elim: s1 s2 => // x s1 IH1.
elim=> //= [|y s2 IH2]; first by rewrite addn0.
by case: (leT x); rewrite /= ?IH1 ?IH2 ?[p y + _]addnCA addnA.
Qed.

Lemma sortedP {T : Type} {e : rel T} {s : seq T} (x : T) :
  reflect (forall i, i.+1 < size s -> e (nth x s i) (nth x s i.+1))
    (sorted e s).
Proof. by case: s => *; [constructor|apply: pathP]. Qed.
