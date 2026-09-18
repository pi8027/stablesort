From elpi Require Export derive.param2.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Elpi derive.param2 unit.
Elpi derive.param2 bool.
Elpi derive.param2 nat.
Elpi derive.param2 option.
Elpi derive.param2 prod.
Elpi derive.param2 list.
Elpi derive.param2 pred.
Elpi derive.param2 rel.
Elpi derive.param2 negb.
Elpi derive.param2 addb.
Elpi derive.param2 eqb.
Elpi derive.param2 size.
Elpi derive.param2 merge.
Elpi derive.param2 catrev.
Elpi derive.param2 rev.
Elpi derive.param2 take.
Elpi derive.param2 drop.
Elpi derive.param2 foldr.
Elpi derive.param2 map.

Lemma bool_R_refl b1 b2 : b1 = b2 -> bool_R b1 b2.
Proof. by case: b1 => <-; constructor. Qed.

Lemma nat_R_refl n1 n2 : n1 = n2 -> nat_R n1 n2.
Proof. by move=> <-; elim: n1 => [|n]; constructor. Qed.

Lemma nat_R_eq n1 n2 : nat_R n1 n2 -> n1 = n2.
Proof. by elim => // {}n1 {}n2 _ ->. Qed.

Lemma map_rel_map A B (f : A -> B) (l : seq A) :
  list_R (fun x y => f x = y) l (map f l).
Proof. by elim: l; constructor. Qed.

Lemma rel_map_map A B (f : A -> B) (l : seq A) (fl : seq B) :
  list_R (fun x y => f x = y) l fl -> fl = map f l.
Proof. by elim/list_R_ind: l fl / => //= ? ? <- ? ? _ ->. Qed.

Lemma half_R n1 n2 : nat_R n1 n2 -> nat_R (half n1) (half n2).
Proof. by move=> /nat_R_eq<-; apply/nat_R_refl. Qed.

Elpi derive.param2.register half half_R.
