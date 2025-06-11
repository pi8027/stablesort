(******************************************************************************)
(* Appendix D: Definitions of mergesorts in Rocq                              *)
(* This file provides copies of the implementations (excluding proofs) of     *)
(* mergesort functions in `stablesort.v`, with some stylistic modifications,  *)
(* e.g., replacing `seq` with `list`, and adding `{struct ..}` annotations.   *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*******************************************************)
(* Appendix D.1: Non-tail-recursive mergesorts in Rocq *)
(*******************************************************)

Module Type MergeSig.
Parameter merge : forall (T : Type) (leT : rel T), list T -> list T -> list T.
Parameter mergeE : forall (T : Type) (leT : rel T), merge leT =2 path.merge leT.
End MergeSig.

Module Merge <: MergeSig.

Fixpoint merge (T : Type) (leT : rel T) (xs ys : list T) : list T :=
  if xs is x :: xs' then
    (fix merge' (ys : list T) : list T :=
       if ys is y :: ys' then
         if leT x y then x :: merge leT xs' ys else y :: merge' ys'
       else xs) ys
  else ys.

Lemma mergeE (T : Type) (leT : rel T) : merge leT =2 path.merge leT.
Proof. by elim=> // x xs IHxs; elim=> //= y ys IHys; rewrite IHxs IHys. Qed.

End Merge.

Module CBN_ (M : MergeSig).
Section CBN.
Context (T : Type) (leT : rel T).

Fixpoint push (xs : list T) (stack : list (list T)) {struct stack} :
    list (list T) :=
  match stack with
  | [::] :: stack | [::] as stack => xs :: stack
  | ys :: stack => [::] :: push (M.merge leT ys xs) stack
  end.

Fixpoint pop (xs : list T) (stack : list (list T)) {struct stack} : list T :=
  if stack is ys :: stack then pop (M.merge leT ys xs) stack else xs.

Fixpoint sort1rec (stack : list (list T)) (xs : list T) {struct xs} : list T :=
  if xs is x :: xs then sort1rec (push [:: x] stack) xs else pop [::] stack.

Definition sort1 : list T -> list T := sort1rec [::].

Fixpoint sort2rec (stack : list (list T)) (xs : list T) {struct xs} : list T :=
  if xs is x1 :: x2 :: xs then
    let t := if leT x1 x2 then [:: x1; x2] else [:: x2; x1] in
    sort2rec (push t stack) xs
  else pop xs stack.

Definition sort2 : list T -> list T := sort2rec [::].

Fixpoint sort3rec (stack : list (list T)) (xs : list T) {struct xs} : list T :=
  match xs with
  | x1 :: x2 :: x3 :: xs =>
    let t :=
        if leT x1 x2 then
          if leT x2 x3 then [:: x1; x2; x3]
          else if leT x1 x3 then [:: x1; x3; x2] else [:: x3; x1; x2]
        else
          if leT x1 x3 then [:: x2; x1; x3]
          else if leT x2 x3 then [:: x2; x3; x1] else [:: x3; x2; x1]
    in
    sort3rec (push t stack) xs
  | [:: x1; x2] => pop (if leT x1 x2 then xs else [:: x2; x1]) stack
  | _ => pop xs stack
  end.

Definition sort3 : list T -> list T := sort3rec [::].

Fixpoint sortNrec (stack : list (list T)) (x : T) (xs : list T) {struct xs} :
    list T :=
  if xs is y :: xs then
    if leT x y then incr stack y xs [:: x] else decr stack y xs [:: x]
  else
    pop [:: x] stack
with incr (stack : list (list T)) (x : T) (xs accu : list T) {struct xs} :
    list T :=
  if xs is y :: xs then
    if leT x y then
      incr stack y xs (x :: accu)
    else
      sortNrec (push (catrev accu [:: x]) stack) y xs
  else
    pop (catrev accu [:: x]) stack
with decr (stack : list (list T)) (x : T) (xs accu : list T) {struct xs} :
    list T :=
  if xs is y :: xs then
    if leT x y then
      sortNrec (push (x :: accu) stack) y xs
    else
      decr stack y xs (x :: accu)
  else
    pop (x :: accu) stack.

Definition sortN (xs : list T) : list T :=
  if xs is x :: xs then sortNrec [::] x xs else [::].

End CBN.
End CBN_.

(***************************************************)
(* Appendix D.2: Tail-recursive mergesorts in Rocq *)
(***************************************************)

Module Type RevmergeSig.
Parameter revmerge :
  forall (T : Type) (leT : rel T), list T -> list T -> list T.
Parameter revmergeE : forall (T : Type) (leT : rel T) (xs ys : list T),
    revmerge leT xs ys = rev (path.merge leT xs ys).
End RevmergeSig.

Module Revmerge <: RevmergeSig.

Fixpoint merge_rec (T : Type) (leT : rel T) (xs ys accu : list T) {struct xs} :
    list T :=
  if xs is x :: xs' then
    (fix merge_rec' (ys accu : list T) {struct ys} :=
       if ys is y :: ys' then
         if leT x y then
           merge_rec leT xs' ys (x :: accu) else merge_rec' ys' (y :: accu)
       else
         catrev xs accu) ys accu
  else catrev ys accu.

Definition revmerge (T : Type) (leT : rel T) (xs ys : list T) : list T :=
  merge_rec leT xs ys [::].

Lemma revmergeE (T : Type) (leT : rel T) (xs ys : list T) :
  revmerge leT xs ys = rev (path.merge leT xs ys).
Proof.
rewrite /revmerge /rev; move: xs ys [::].
by elim=> [|x xs IHxs]; elim=> [|y ys IHys] accu //=; case: ifP => /=.
Qed.

End Revmerge.

Module CBV_ (M : RevmergeSig).
Section CBV.
Context (T : Type) (leT : rel T).
Let geT x y := leT y x.

Fixpoint push (xs : list T) (stack : list (list T)) {struct stack} :
    list (list T) :=
  match stack with
  | [::] :: stack | [::] as stack => xs :: stack
  | ys :: [::] :: stack | ys :: ([::] as stack) =>
    [::] :: M.revmerge leT ys xs :: stack
  | ys :: zs :: stack =>
    [::] :: [::] :: push (M.revmerge geT (M.revmerge leT ys xs) zs) stack
  end.

Fixpoint pop (mode : bool) (xs : list T) (stack : list (list T)) {struct stack}
    : list T :=
  match stack, mode with
  | [::], true => rev xs
  | [::], false => xs
  | [::] :: [::] :: stack, _ => pop mode xs stack
  | [::] :: stack, _ => pop (~~ mode) (rev xs) stack
  | ys :: stack, true => pop false (M.revmerge geT xs ys) stack
  | ys :: stack, false => pop true (M.revmerge leT ys xs) stack
  end.

Fixpoint sort1rec (stack : list (list T)) (xs : list T) {struct xs} : list T :=
  if xs is x :: xs then
    sort1rec (push [:: x] stack) xs
  else
    pop false [::] stack.

Definition sort1 : list T -> list T := sort1rec [::].

Fixpoint sort2rec (stack : list (list T)) (xs : list T) {struct xs} : list T :=
  if xs is x1 :: x2 :: xs then
    let t := if leT x1 x2 then [:: x1; x2] else [:: x2; x1] in
    sort2rec (push t stack) xs
  else pop false xs stack.

Definition sort2 : list T -> list T := sort2rec [::].

Fixpoint sort3rec (stack : list (list T)) (xs : list T) {struct xs} : list T :=
  match xs with
  | x1 :: x2 :: x3 :: xs =>
    let t :=
        if leT x1 x2 then
          if leT x2 x3 then [:: x1; x2; x3]
          else if leT x1 x3 then [:: x1; x3; x2] else [:: x3; x1; x2]
        else
          if leT x1 x3 then [:: x2; x1; x3]
          else if leT x2 x3 then [:: x2; x3; x1] else [:: x3; x2; x1]
    in
    sort3rec (push t stack) xs
  | [:: x1; x2] => pop false (if leT x1 x2 then xs else [:: x2; x1]) stack
  | _ => pop false xs stack
  end.

Definition sort3 : list T -> list T := sort3rec [::].

Fixpoint sortNrec (stack : list (list T)) (x : T) (xs : list T) {struct xs} :
    list T :=
  if xs is y :: xs then
    if leT x y then incr stack y xs [:: x] else decr stack y xs [:: x]
  else
    pop false [:: x] stack
with incr (stack : list (list T)) (x : T) (xs accu : list T) {struct xs} :
    list T :=
  if xs is y :: xs then
    if leT x y then
      incr stack y xs (x :: accu)
    else
      sortNrec (push (catrev accu [:: x]) stack) y xs
  else
    pop false (catrev accu [:: x]) stack
with decr (stack : list (list T)) (x : T) (xs accu : list T) {struct xs} :
    list T :=
  if xs is y :: xs then
    if leT x y then
      sortNrec (push (x :: accu) stack) y xs
    else
      decr stack y xs (x :: accu)
  else
    pop false (x :: accu) stack.

Definition sortN (xs : list T) : list T :=
  if xs is x :: xs then sortNrec [::] x xs else [::].

End CBV.
End CBV_.
