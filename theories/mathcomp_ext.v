From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
