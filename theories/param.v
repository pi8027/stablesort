From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Declare ML Module "paramcoq".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Ltac destruct_reflexivity := 
  intros ; repeat match goal with 
    | [ x : _ |- _ = _ ] => destruct x; reflexivity; fail
  end.
 
Global Parametricity Tactic := ((destruct_reflexivity; fail) || auto).

Parametricity bool.
Parametricity list.
Parametricity pred.
Parametricity rel.

Lemma bool_R_refl b1 b2 : b1 = b2 -> bool_R b1 b2.
Proof. by case: b1 => <-; constructor. Qed.

Lemma map_rel_map A B (f : A -> B) (l : seq A) :
  list_R (fun x y => f x = y) l (map f l).
Proof. by elim: l; constructor. Qed.

Lemma rel_map_map A B (f : A -> B) (l : seq A) (fl : seq B) :
  list_R (fun x y => f x = y) l fl -> fl = map f l.
Proof. by elim/list_R_ind: l fl / => //= ? ? <- ? ? _ ->. Qed.
