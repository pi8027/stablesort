From stablesort Require Import mathcomp_ext.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From stablesort Require Import param.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(******************************************************************************)
(* The abstract interface for stable (merge)sort algorithms                   *)
(******************************************************************************)

Module StableSort.

(* the type of polymorphic sort functions                                     *)
Definition sort_ty :=
  forall T : Type,                      (* the type of elements               *)
    rel T ->                            (* the comparison function [leT]      *)
    seq T ->                            (* input                              *)
    seq T.                              (* output                             *)

(* the type of sort functions abstracted over the type of sorted lists and    *)
(* some operations on them, e.g., merge                                       *)
Definition asort_ty :=
  forall T : Type,                      (* the type of elements               *)
  forall R : Type,                      (* the type of sorted lists           *)
    rel T ->                            (* the comparison function [leT]      *)
    (R -> R -> R) ->                    (* merge by [leT]                     *)
    (R -> R -> R) ->                    (* merge by the converse of [leT]     *)
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
  (* the binary parametricity of [asort]                                      *)
  _ : asort_ty_R asort asort;
  (* [asort] instantiated with merge is extensionally equal to [apply]        *)
  _ : forall T (leT : rel T),
    let geT x y := leT y x in
    asort leT (merge leT) (fun xs ys => rev (merge geT (rev ys) (rev xs)))
      (fun x => [:: x]) [::]
    =1 apply leT;
  (* [asort] instantiated with concatenation is the identity function         *)
  _ : forall T (leT : rel T), asort leT cat cat (fun x => [:: x]) [::] =1 id;
}.

Module Exports.
Arguments Pack apply asort _ _ _ : clear implicits.
Notation stableSort := function.
Notation StableSort := Pack.
Coercion apply : function >-> Funclass.
End Exports.

End StableSort.
Export StableSort.Exports.

(******************************************************************************)
(* Merge functions                                                            *)
(******************************************************************************)

(* The [MergeSig] and [RevmergeSig] module types are interfaces for           *)
(* non-tail-recursive and tail-recursive merge functions, respectively.       *)
Module Type MergeSig.
Parameter merge : forall (T : Type) (leT : rel T), seq T -> seq T -> seq T.
Parameter mergeE : forall (T : Type) (leT : rel T), merge leT =2 path.merge leT.
End MergeSig.

Module Type RevmergeSig.
Parameter revmerge : forall (T : Type) (leT : rel T), seq T -> seq T -> seq T.
Parameter revmergeE : forall (T : Type) (leT : rel T) (xs ys : seq T),
    revmerge leT xs ys = rev (path.merge leT xs ys).
End RevmergeSig.

(* The [Merge] module implements a non-tail-recursive merge function using    *)
(* nested recursion. This implementation is suited for computation inside Coq.*)
Module Merge <: MergeSig.

Fixpoint merge (T : Type) (leT : rel T) (xs ys : seq T) : seq T :=
  if xs is x :: xs' then
    (fix merge' (ys : seq T) : seq T :=
       if ys is y :: ys' then
         if leT x y then x :: merge leT xs' ys else y :: merge' ys'
       else xs) ys
  else ys.

Lemma mergeE (T : Type) (leT : rel T) : merge leT =2 path.merge leT.
Proof. by elim=> // x xs IHxs; elim=> //= y ys IHys; rewrite IHxs IHys. Qed.

End Merge.

(* The [MergeAcc] module implements a non-tail-recursive merge function using *)
(* well-founded recursion. This implementation is suited for code extraction. *)
Module MergeAcc <: MergeSig.

Definition mergeord {T : Type} (p1 p2 : seq T * seq T) : Prop :=
  if p2 is (x :: xs, y :: ys) then
    (xs, y :: ys) = p1 \/ (x :: xs, ys) = p1 else False.

Fixpoint wf_mergeord (T : Type) (xs ys : seq T) : Acc mergeord (xs, ys) :=
  if xs is x :: xs' then
    (fix wf_mergeord' (ys : seq T) : Acc mergeord (x :: xs', ys) :=
       if ys is y :: ys' then
         Acc_intro
           (x :: xs', y :: ys')
           (fun _ H =>
              match H with
              | or_introl H0 =>
                let: erefl in (_ = y1) := H0 return Acc mergeord y1 in
                wf_mergeord xs' (y :: ys')
              | or_intror H0 =>
                let: erefl in (_ = y1) := H0 return Acc mergeord y1 in
                wf_mergeord' ys'
              end)
       else
         Acc_intro (x :: xs', [::]) (fun _ => False_ind _)) ys
  else
    Acc_intro ([::], ys) (fun _ => False_ind _).

Fixpoint merge_rec (T : Type) (leT : rel T)
                   (xs ys : seq T) (fuel : Acc mergeord (xs, ys)) : seq T :=
  match fuel, xs, ys return xs = _ -> ys = _ -> _ with
  | _, [::], ys => fun _ _ => ys
  | _, xs, [::] => fun _ _ => xs
  | Acc_intro fuel, x :: xs', y :: ys' =>
    fun (xsE : x :: xs' = xs) (ysE : y :: ys' = ys) =>
    if leT x y then
      x :: @merge_rec T leT xs' ys
        (fuel _ match xsE in _ = xs0, ysE in _ = ys0
                      return mergeord (xs', ys0) (xs0, ys0) with
                  erefl, erefl => or_introl erefl
                end)
    else
      y :: @merge_rec T leT xs ys'
        (fuel _ match xsE in _ = xs0, ysE in _ = ys0
                      return mergeord (xs0, ys') (xs0, ys0) with
                  erefl, erefl => or_intror erefl
                end)
  end erefl erefl.

Definition merge (T : Type) (leT : rel T) (xs ys : seq T) : seq T :=
  @merge_rec T leT xs ys (wf_mergeord xs ys).

Lemma mergeE (T : Type) (leT : rel T) : merge leT =2 path.merge leT.
Proof.
rewrite /merge => xs ys; move: xs ys (wf_mergeord xs ys).
by elim=> [|x xs IHxs]; elim=> [|y ys IHys] [acc] //=; rewrite IHxs IHys.
Qed.

End MergeAcc.

(* The [Revmerge] module implements a tail-recursive merge function using     *)
(* nested recursion. This implementation is suited for computation inside Coq.*)
Module Revmerge <: RevmergeSig.

Fixpoint merge_rec (T : Type) (leT : rel T) (xs ys accu : seq T) : seq T :=
  if xs is x :: xs' then
    (fix merge_rec' (ys accu : seq T) :=
       if ys is y :: ys' then
         if leT x y then
           merge_rec leT xs' ys (x :: accu) else merge_rec' ys' (y :: accu)
       else
         catrev xs accu) ys accu
  else catrev ys accu.

Definition revmerge (T : Type) (leT : rel T) (xs ys : seq T) : seq T :=
  merge_rec leT xs ys [::].

Lemma revmergeE (T : Type) (leT : rel T) (xs ys : seq T) :
  revmerge leT xs ys = rev (path.merge leT xs ys).
Proof.
rewrite /revmerge -[RHS]cats0.
elim: xs ys [::] => [|x xs IHxs]; elim=> [|y ys IHys] accu //=;
  try by rewrite catrevE rev_cons cat_rcons.
by case: ifP => _; rewrite rev_cons cat_rcons.
Qed.

End Revmerge.

(* The [RevmergeAcc] module implements a tail-recursive merge function using  *)
(* well-founded recursion. This implementation is suited for code extraction. *)
Module RevmergeAcc <: RevmergeSig.

Import MergeAcc.

Fixpoint merge_rec (T : Type) (leT : rel T) (xs ys accu : seq T)
                   (fuel : Acc mergeord (xs, ys)) : seq T :=
  match fuel, xs, ys return xs = _ -> ys = _ -> _ with
  | _, [::], ys => fun _ _ => catrev ys accu
  | _, xs, [::] => fun _ _ => catrev xs accu
  | Acc_intro fuel, x :: xs', y :: ys' =>
    fun (xsE : x :: xs' = xs) (ysE : y :: ys' = ys) =>
    if leT x y then
      @merge_rec T leT xs' ys (x :: accu)
        (fuel _ match xsE in _ = xs0, ysE in _ = ys0
                      return mergeord (xs', ys0) (xs0, ys0) with
                  erefl, erefl => or_introl erefl
                end)
    else
      @merge_rec T leT xs ys' (y :: accu)
        (fuel _ match xsE in _ = xs0, ysE in _ = ys0
                      return mergeord (xs0, ys') (xs0, ys0) with
                  erefl, erefl => or_intror erefl
                end)
  end erefl erefl.

Definition revmerge (T : Type) (leT : rel T) (xs ys : seq T) : seq T :=
  @merge_rec T leT xs ys [::] (wf_mergeord xs ys).

Lemma revmergeE (T : Type) (leT : rel T) (xs ys : seq T) :
  revmerge leT xs ys = rev (path.merge leT xs ys).
Proof.
rewrite /revmerge -[RHS]cats0; move: xs ys [::] (wf_mergeord xs ys).
elim=> [|x xs IHxs]; elim=> [|y ys IHys] accu [acc] //=;
  try by rewrite catrevE rev_cons cat_rcons.
by case: ifP => _; rewrite rev_cons cat_rcons.
Qed.

End RevmergeAcc.

(******************************************************************************)
(* Insertion sort                                                             *)
(******************************************************************************)

Module Insertion.

Module Abstract.

Definition sort (T R : Type) (leT : rel T)
  (merge : R -> R -> R) (merge' : R -> R -> R)
  (singleton : T -> R) (empty : R) :=
  foldr (fun x => merge (singleton x)) empty.

Parametricity sort.

End Abstract.

Section Insertion.

Variables (T : Type) (leT : rel T).

Definition sort : seq T -> seq T := foldr (fun x => merge leT [:: x]) [::].

Lemma asort_catE : Abstract.sort leT cat cat (fun x => [:: x]) [::] =1 id.
Proof. by elim=> //= x xs ->. Qed.

End Insertion.

Definition sort_stable :=
  StableSort sort Abstract.sort Abstract.sort_R (fun _ _ _ => erefl) asort_catE.

End Insertion.

Canonical Insertion.sort_stable.

(******************************************************************************)
(* The [CBN_] functor module takes a module [M] of type [MergeSig] and        *)
(* provides a family of mergesort functions [sort1], [sort2], [sort3], and    *)
(* [sortN]. These functions are bottom-up and structurally recursive and use  *)
(* [M.merge] internally for merging sorted lists.                             *)
(* The numbers [1], [2], and [3] in their names stand for the fact that they  *)
(* repeat to take a fixed-size prefix from the input, put it into the given   *)
(* order, and push it to a stack that manages the sorting process. Among      *)
(* those, [sort2] is exactly the same as [path.sort] of MathComp except that  *)
(* it is parameterized by the merge function. On the other hand, [sortN]      *)
(* takes the longest sorted prefix (in ascending or descending order) instead *)
(* of a fixed-size prefix, as in GHC's [Data.List.sort].                      *)
(* Since [M.merge] is expected to be a non-tail-recursive merge function,     *)
(* these sorting functions should allow us to compute the output              *)
(* incrementally in the call-by-need evaluation. In fact, computing the first *)
(* k smallest elements of a list of length n using one of these sort          *)
(* functions has O(n + k log k) time complexity, which is the known optimal   *)
(* time complexity of the partial and incremental sorting problems. However,  *)
(* the non-tail-recursive merge function linearly consumes the call stack and *)
(* triggers a stack overflow in the call-by-value evaluation.                 *)
(******************************************************************************)

Module CBN_ (M : MergeSig).

Module Abstract.
Section Abstract.

Variables (T R : Type) (leT : rel T).
Variables (merge : R -> R -> R) (merge' : R -> R -> R).
Variables (singleton : T -> R) (empty : R).

Fixpoint push (xs : R) (stack : seq (option R)) : seq (option R) :=
  match stack with
  | None :: stack | [::] as stack => Some xs :: stack
  | Some ys :: stack => None :: push (merge ys xs) stack
  end.

Fixpoint pop (xs : R) (stack : seq (option R)) : R :=
  match stack with
  | [::] => xs
  | None :: stack => pop xs stack
  | Some ys :: stack => pop (merge ys xs) stack
  end.

Fixpoint sort1rec (stack : seq (option R)) (xs : seq T) : R :=
  if xs is x :: xs then
    sort1rec (push (singleton x) stack) xs
  else
    pop empty stack.

#[using="All"]
Definition sort1 : seq T -> R := sort1rec [::].

Fixpoint sort2rec (stack : seq (option R)) (xs : seq T) : R :=
  match xs with
  | [:: x1, x2 & xs] =>
    sort2rec (push (merge (singleton x1) (singleton x2)) stack) xs
  | [:: x] => pop (singleton x) stack
  | [::] => pop empty stack
  end.

#[using="All"]
Definition sort2 : seq T -> R := sort2rec [::].

Fixpoint sort3rec (stack : seq (option R)) (xs : seq T) : R :=
  match xs with
  | [:: x1, x2, x3 & xs] =>
    let t := merge' (merge (singleton x1) (singleton x2)) (singleton x3) in
    sort3rec (push t stack) xs
  | [:: x1; x2] => pop (merge (singleton x1) (singleton x2)) stack
  | [:: x] => pop (singleton x) stack
  | [::] => pop empty stack
  end.

#[using="All"]
Definition sort3 : seq T -> R := sort3rec [::].

Fixpoint sortNrec (stack : seq (option R)) (x : T) (xs : seq T) : R :=
  if xs is y :: xs then
    if leT x y then
      incr stack y xs (singleton x)
    else
      decr stack y xs (singleton x)
  else
    pop (singleton x) stack
with incr (stack : seq (option R)) (x : T) (xs : seq T) (accu : R) : R :=
  if xs is y :: xs then
    if leT x y then
      incr stack y xs (merge' accu (singleton x))
    else
      sortNrec (push (merge' accu (singleton x)) stack) y xs
  else
    pop (merge' accu (singleton x)) stack
with decr (stack : seq (option R)) (x : T) (xs : seq T) (accu : R) : R :=
  if xs is y :: xs then
    if leT x y then
      sortNrec (push (merge accu (singleton x)) stack) y xs
    else
      decr stack y xs (merge accu (singleton x))
  else
    pop (merge accu (singleton x)) stack.

#[using="All"]
Definition sortN (xs : seq T) : R :=
  if xs is x :: xs then sortNrec [::] x xs else empty.

End Abstract.

Parametricity sort1.
Parametricity sort2.
Parametricity sort3.
Parametricity sortN.

End Abstract.

Section CBN.

Variable (T : Type) (leT : rel T).

Fixpoint push (xs : seq T) (stack : seq (seq T)) : seq (seq T) :=
  match stack with
  | [::] :: stack | [::] as stack => xs :: stack
  | ys :: stack => [::] :: push (M.merge leT ys xs) stack
  end.

Fixpoint pop (xs : seq T) (stack : seq (seq T)) : seq T :=
  if stack is ys :: stack then pop (M.merge leT ys xs) stack else xs.

Fixpoint sort1rec (stack : seq (seq T)) (xs : seq T) : seq T :=
  if xs is x :: xs then sort1rec (push [:: x] stack) xs else pop [::] stack.

Definition sort1 : seq T -> seq T := sort1rec [::].

Fixpoint sort2rec (stack : seq (seq T)) (xs : seq T) : seq T :=
  if xs is [:: x1, x2 & xs] then
    let t := if leT x1 x2 then [:: x1; x2] else [:: x2; x1] in
    sort2rec (push t stack) xs
  else pop xs stack.

Definition sort2 : seq T -> seq T := sort2rec [::].

Fixpoint sort3rec (stack : seq (seq T)) (xs : seq T) : seq T :=
  match xs with
  | [:: x1, x2, x3 & xs] =>
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

Definition sort3 : seq T -> seq T := sort3rec [::].

Fixpoint sortNrec (stack : seq (seq T)) (x : T) (xs : seq T) : seq T :=
  if xs is y :: xs then
    if leT x y then incr stack y xs [:: x] else decr stack y xs [:: x]
  else
    pop [:: x] stack
with incr (stack : seq (seq T)) (x : T) (xs accu : seq T) : seq T :=
  if xs is y :: xs then
    if leT x y then
      incr stack y xs (x :: accu)
    else
      sortNrec (push (catrev accu [:: x]) stack) y xs
  else
    pop (catrev accu [:: x]) stack
with decr (stack : seq (seq T)) (x : T) (xs accu : seq T) : seq T :=
  if xs is y :: xs then
    if leT x y then
      sortNrec (push (x :: accu) stack) y xs
    else
      decr stack y xs (x :: accu)
  else
    pop (x :: accu) stack.

Definition sortN (xs : seq T) : seq T :=
  if xs is x :: xs then sortNrec [::] x xs else [::].

(* Proofs *)

Let geT x y := leT y x.
Let astack_of_stack : seq (seq T) -> seq (option (seq T)) :=
  map (fun xs => if xs is [::] then None else Some xs).

Notation merge := (path.merge leT) (only parsing).
Notation merge' :=
  (fun xs ys => rev (path.merge geT (rev ys) (rev xs))) (only parsing).
Notation flatten_stack :=
  (foldl (fun xs : seq T => oapp (cat^~ xs) xs)) (only parsing).

Lemma apop_mergeE xs stack :
  Abstract.pop merge xs (astack_of_stack stack) = pop xs stack.
Proof.
by elim: stack xs => [|[|y ys] stack IHstack] xs //=; rewrite M.mergeE IHstack.
Qed.

Lemma apush_mergeE xs stack :
  ~~ nilp xs ->
  Abstract.push merge xs (astack_of_stack stack)
  = astack_of_stack (push xs stack).
Proof.
elim: stack xs => [|[|y ys] stack IHstack]; try by case.
by move=> xs Hxs /=; rewrite M.mergeE IHstack // /nilp size_merge.
Qed.

Lemma asort1_mergeE :
  Abstract.sort1 leT merge merge' (fun x => [:: x]) [::] =1 sort1.
Proof.
rewrite /Abstract.sort1 /sort1 -[Nil (option _)]/(astack_of_stack [::]) => xs.
elim: xs (Nil (seq _)) => /= [|x xs IHxs] stack; first by rewrite apop_mergeE.
by rewrite -IHxs apush_mergeE.
Qed.

Lemma asort2_mergeE :
  Abstract.sort2 leT merge merge' (fun x => [:: x]) [::] =1 sort2.
Proof.
move=> xs; have [n] := ubnP (size xs).
rewrite /Abstract.sort2 /sort2 -[Nil (option _)]/(astack_of_stack [::]).
elim: n (Nil (seq _)) xs => // n IHn stack [|x [|x' xs /= /ltnW /IHn <-]] /=;
  try by rewrite apop_mergeE.
by rewrite apush_mergeE; last case: ifP.
Qed.

Lemma asort3_mergeE :
  Abstract.sort3 leT merge merge' (fun x => [:: x]) [::] =1 sort3.
Proof.
move=> xs; have [n] := ubnP (size xs).
rewrite /Abstract.sort3 /sort3 -[Nil (option _)]/(astack_of_stack [::]).
move: n (Nil (seq _)) xs.
elim=> // n IHn stack [|x [|x' [|x'' xs /= /ltnW /ltnW /IHn <-]]] /=;
  try by rewrite apop_mergeE.
rewrite apush_mergeE; last by rewrite /nilp !(size_rev, size_merge).
by rewrite !(fun_if rev, fun_if (path.merge _ _), fun_if (cons _)).
Qed.

Lemma asortN_mergeE :
  Abstract.sortN leT merge merge' (fun x => [:: x]) [::] =1 sortN.
Proof.
case=> // x xs; have [n] := ubnP (size xs).
rewrite /Abstract.sortN /sortN -[Nil (option _)]/(astack_of_stack [::]).
elim: n (Nil (seq _)) x xs => // n IHn stack x [|y xs /= /ltnSE Hxs].
  by rewrite [LHS]apop_mergeE.
rewrite /Abstract.sortNrec.
rewrite -/(Abstract.incr _ _ merge' _) -/(Abstract.decr _ _ merge' _).
pose rs := Nil T; rewrite -{1}[[:: x]]/(rcons (rev rs) x) -/(x :: rs).
elim: xs Hxs x y rs => [_|z xs IHxs /= /ltnW Hxs] x y rs.
  rewrite /Abstract.incr /Abstract.decr !apop_mergeE rev_rcons revK /= /geT.
  by case: leT.
rewrite /Abstract.incr -/(Abstract.incr _ _ merge' _).
rewrite /Abstract.decr -/(Abstract.decr _ _ merge' _).
rewrite -/(Abstract.sortNrec _ _ merge' _).
move: (IHxs Hxs y z (x :: rs)); rewrite -rev_cons rev_rcons revK /= /geT.
by do 2 case: leT; rewrite // apush_mergeE ?rev_nilp // IHn.
Qed.

Lemma apush_catE (xs ys : seq T) stack :
  flatten_stack ys (Abstract.push cat xs stack)
  = flatten_stack (xs ++ ys) stack.
Proof.
by elim: stack xs => [|[zs|] stack IHstack] xs //=; rewrite IHstack catA.
Qed.

Lemma apop_catE xs stack : Abstract.pop cat xs stack = flatten_stack xs stack.
Proof. by elim: stack xs => [|[]] /=. Qed.

Lemma asort1_catE : Abstract.sort1 leT cat cat (fun x => [:: x]) [::] =1 id.
Proof.
move=> xs; rewrite /Abstract.sort1 -[RHS]/(flatten_stack xs [::]).
elim: xs (Nil (option _)) => /= [|x xs IHxs] stack; first exact: apop_catE.
by rewrite IHxs apush_catE.
Qed.

Lemma asort2_catE : Abstract.sort2 leT cat cat (fun x => [:: x]) [::] =1 id.
Proof.
move=> xs; have [n] := ubnP (size xs).
rewrite /Abstract.sort2 -[RHS]/(flatten_stack xs [::]).
move: n (Nil (option _)) xs.
by elim=> // n IHn stack [|x [|x' xs /= /ltnW /IHn ->]] /=;
  rewrite (apop_catE, apush_catE).
Qed.

Lemma asort3_catE : Abstract.sort3 leT cat cat (fun x => [:: x]) [::] =1 id.
Proof.
move=> xs; have [n] := ubnP (size xs).
rewrite /Abstract.sort3 -[RHS]/(flatten_stack xs [::]).
move: n (Nil (option _)) xs.
by elim=> // n IHn stack [|x [|x' [|x'' xs /= /ltnW /ltnW /IHn ->]]] /=;
  rewrite (apop_catE, apush_catE).
Qed.

Lemma asortN_catE : Abstract.sortN leT cat cat (fun x => [:: x]) [::] =1 id.
Proof.
case=> // x xs; have [n] := ubnP (size xs).
rewrite /Abstract.sortN -[RHS]/(flatten_stack (x :: xs) [::]).
elim: n x (Nil (option _)) xs => // n IHn x stack [|y xs /= /ltnSE Hxs];
  first by rewrite [LHS]apop_catE.
rewrite /Abstract.sortNrec -/(Abstract.incr _ _ _ _) -/(Abstract.decr _ _ _ _).
pose rs := Nil T; rewrite -[x :: y :: _]/(rs ++ _) -[[:: x]]/(rs ++ _).
elim: xs Hxs x y rs => [_|z xs IHxs /= /ltnW Hxs] x y rs.
  by rewrite if_same [LHS]apop_catE -catA.
rewrite /Abstract.incr -/(Abstract.incr _ _ _ _).
rewrite /Abstract.decr -/(Abstract.decr _ _ _ _) -/(Abstract.sortNrec _ _ _ _).
move: (IHxs Hxs y z (rcons rs x)); rewrite IHn // apush_catE -cats1 -!catA /=.
by case: leT => ->; rewrite if_same.
Qed.

End CBN.

Definition sort1_stable :=
  StableSort sort1 Abstract.sort1 Abstract.sort1_R asort1_mergeE asort1_catE.
Definition sort2_stable :=
  StableSort sort2 Abstract.sort2 Abstract.sort2_R asort2_mergeE asort2_catE.
Definition sort3_stable :=
  StableSort sort3 Abstract.sort3 Abstract.sort3_R asort3_mergeE asort3_catE.
Definition sortN_stable :=
  StableSort sortN Abstract.sortN Abstract.sortN_R asortN_mergeE asortN_catE.

End CBN_.

Module CBN := CBN_(Merge).
Module CBNAcc := CBN_(MergeAcc).

Canonical CBN.sort1_stable.
Canonical CBN.sort2_stable.
Canonical CBN.sort3_stable.
Canonical CBN.sortN_stable.
Canonical CBNAcc.sort1_stable.
Canonical CBNAcc.sort2_stable.
Canonical CBNAcc.sort3_stable.
Canonical CBNAcc.sortN_stable.

(******************************************************************************)
(* The [CBV_] functor module takes a module [M] of type [RevmergeSig] and     *)
(* provides a family of mergesort functions [sort1], [sort2], [sort3], and    *)
(* [sortN]. These functions are bottom-up and structurally recursive and use  *)
(* [M.revmerge] internally for merging sorted lists. Their naming convention  *)
(* is the same as in the above [CBN_] functor module.                         *)
(* As opposed to the [M.merge] function of a [M : MergeSig], the [M.revmerge] *)
(* function puts its result in the reverse order, and is expected to be a     *)
(* tail-recursive merge function, so that it does not consume the stack       *)
(* linearly in the call-by-value evaluation. Merging with the converse        *)
(* relation of the given order [leT] allows us to merge two lists sorted in   *)
(* the reverse order without taking their reversals (see, e.g., the last case *)
(* of [merge_sort_push]). Also, the push/pop trick of [path.sort] allows us   *)
(* to implement bottom-up mergesort functions with only O(log n) stack        *)
(* consumption. However, this algorithm does not allow us to compute the      *)
(* output incrementally in the optimal O(n + k log k) time regardless of the  *)
(* evaluation strategy.                                                       *)
(******************************************************************************)

Module CBV_ (M : RevmergeSig).

Module Abstract.
Section Abstract.

Variables (T R : Type) (leT : rel T).
Variables (merge : R -> R -> R) (merge' : R -> R -> R).
Variables (singleton : T -> R) (empty : R).

Fixpoint push (xs : R) (stack : seq (option R)) : seq (option R) :=
  match stack with
  | None :: stack | [::] as stack => Some xs :: stack
  | Some ys :: None :: stack | Some ys :: ([::] as stack) =>
    None :: Some (merge ys xs) :: stack
  | Some ys :: Some zs :: stack =>
    None :: None :: push (merge' zs (merge ys xs)) stack
  end.

Fixpoint pop (mode : bool) (xs : R) (stack : seq (option R)) : R :=
  match stack with
  | [::] => xs
  | None :: None :: stack => pop mode xs stack
  | None :: stack => pop (~~ mode) xs stack
  | (Some ys) :: stack =>
    pop (~~ mode) (if mode then merge' ys xs else merge ys xs) stack
  end.

Fixpoint sort1rec (stack : seq (option R)) (xs : seq T) : R :=
  if xs is x :: xs then
    sort1rec (push (singleton x) stack) xs
  else
    pop false empty stack.

#[using="All"]
Definition sort1 : seq T -> R := sort1rec [::].

Fixpoint sort2rec (stack : seq (option R)) (xs : seq T) : R :=
  match xs with
  | [:: x1, x2 & xs] =>
    sort2rec (push (merge (singleton x1) (singleton x2)) stack) xs
  | [:: x] => pop false (singleton x) stack
  | [::] => pop false empty stack
  end.

#[using="All"]
Definition sort2 : seq T -> R := sort2rec [::].

Fixpoint sort3rec (stack : seq (option R)) (xs : seq T) : R :=
  match xs with
  | [:: x1, x2, x3 & xs] =>
    let t := merge' (merge (singleton x1) (singleton x2)) (singleton x3) in
    sort3rec (push t stack) xs
  | [:: x1; x2] => pop false (merge (singleton x1) (singleton x2)) stack
  | [:: x] => pop false (singleton x) stack
  | [::] => pop false empty stack
  end.

#[using="All"]
Definition sort3 : seq T -> R := sort3rec [::].

Fixpoint sortNrec (stack : seq (option R)) (x : T) (xs : seq T) : R :=
  if xs is y :: xs then
    if leT x y then
      incr stack y xs (singleton x)
    else
      decr stack y xs (singleton x)
  else
    pop false (singleton x) stack
with incr (stack : seq (option R)) (x : T) (xs : seq T) (accu : R) : R :=
  if xs is y :: xs then
    if leT x y then
      incr stack y xs (merge' accu (singleton x))
    else
      sortNrec (push (merge' accu (singleton x)) stack) y xs
  else
    pop false (merge' accu (singleton x)) stack
with decr (stack : seq (option R)) (x : T) (xs : seq T) (accu : R) : R :=
  if xs is y :: xs then
    if leT x y then
      sortNrec (push (merge accu (singleton x)) stack) y xs
    else
      decr stack y xs (merge accu (singleton x))
  else
    pop false (merge accu (singleton x)) stack.

#[using="All"]
Definition sortN (xs : seq T) : R :=
  if xs is x :: xs then sortNrec [::] x xs else empty.

End Abstract.

Parametricity sort1.
Parametricity sort2.
Parametricity sort3.
Parametricity sortN.

End Abstract.

Section CBV.

Variables (T : Type) (leT : rel T).
Let geT x y := leT y x.

Fixpoint push (xs : seq T) (stack : seq (seq T)) : seq (seq T) :=
  match stack with
  | [::] :: stack | [::] as stack => xs :: stack
  | ys :: [::] :: stack | ys :: ([::] as stack) =>
    [::] :: M.revmerge leT ys xs :: stack
  | ys :: zs :: stack =>
    [::] :: [::] :: push (M.revmerge geT (M.revmerge leT ys xs) zs) stack
  end.

Fixpoint pop (mode : bool) (xs : seq T) (stack : seq (seq T)) : seq T :=
  match stack, mode with
  | [::], true => rev xs
  | [::], false => xs
  | [::] :: [::] :: stack, _ => pop mode xs stack
  | [::] :: stack, _ => pop (~~ mode) (rev xs) stack
  | ys :: stack, true => pop false (M.revmerge geT xs ys) stack
  | ys :: stack, false => pop true (M.revmerge leT ys xs) stack
  end.

Fixpoint sort1rec (stack : seq (seq T)) (xs : seq T) : seq T :=
  if xs is x :: xs then
    sort1rec (push [:: x] stack) xs
  else
    pop false [::] stack.

Definition sort1 : seq T -> seq T := sort1rec [::].

Fixpoint sort2rec (stack : seq (seq T)) (xs : seq T) : seq T :=
  if xs is [:: x1, x2 & xs] then
    let t := if leT x1 x2 then [:: x1; x2] else [:: x2; x1] in
    sort2rec (push t stack) xs
  else pop false xs stack.

Definition sort2 : seq T -> seq T := sort2rec [::].

Fixpoint sort3rec (stack : seq (seq T)) (xs : seq T) : seq T :=
  match xs with
  | [:: x1, x2, x3 & xs] =>
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

Definition sort3 : seq T -> seq T := sort3rec [::].

Fixpoint sortNrec (stack : seq (seq T)) (x : T) (xs : seq T) : seq T :=
  if xs is y :: xs then
    if leT x y then incr stack y xs [:: x] else decr stack y xs [:: x]
  else
    pop false [:: x] stack
with incr (stack : seq (seq T)) (x : T) (xs accu : seq T) : seq T :=
  if xs is y :: xs then
    if leT x y then
      incr stack y xs (x :: accu)
    else
      sortNrec (push (catrev accu [:: x]) stack) y xs
  else
    pop false (catrev accu [:: x]) stack
with decr (stack : seq (seq T)) (x : T) (xs accu : seq T) : seq T :=
  if xs is y :: xs then
    if leT x y then
      sortNrec (push (x :: accu) stack) y xs
    else
      decr stack y xs (x :: accu)
  else
    pop false (x :: accu) stack.

Definition sortN (xs : seq T) : seq T :=
  if xs is x :: xs then sortNrec [::] x xs else [::].

(* Proofs *)

Let condrev (r : bool) (s : seq T) : seq T := if r then rev s else s.

Lemma condrev_nilp mode xs : nilp (condrev mode xs) = nilp xs.
Proof. by case: mode; rewrite /= ?rev_nilp. Qed.

Lemma condrevK mode : involutive (condrev mode).
Proof. by case: mode; first exact: revK. Qed.

Let Fixpoint astack_of_stack (mode : bool) (stack : seq (seq T)) :=
  match stack with
  | [::] => [::]
  | xs :: stack =>
    (if nilp xs then None else Some (condrev mode xs)) ::
      astack_of_stack (~~ mode) stack
  end.

Notation merge := (path.merge leT) (only parsing).
Notation merge' :=
  (fun xs ys => rev (path.merge geT (rev ys) (rev xs))) (only parsing).
Notation flatten_stack :=
  (foldl (fun xs : seq T => oapp (cat^~ xs) xs)) (only parsing).

Lemma apop_mergeE mode xs stack :
  Abstract.pop merge merge' mode xs (astack_of_stack mode stack)
  = pop mode (condrev mode xs) stack.
Proof.
have [n] := ubnP (size stack).
by elim: n mode xs stack => // n IHn [] xs [|[[|[|z zs] stack]|y ys stack]] /=;
  rewrite ?M.revmergeE ?revK //; try move/(@ltnW _.+2); move=> /IHn ->.
Qed.

Lemma apush_mergeE xs stack :
  ~~ nilp xs ->
  Abstract.push merge merge' xs (astack_of_stack false stack)
  = astack_of_stack false (push xs stack).
Proof.
have [n] := ubnP (size stack).
by elim: n xs stack => // n IHn xs [|[|y ys] [|[|z zs] stack]] //=;
  try move=> /(@ltnW _.+2) /IHn ->; try (by case: ifP);
  rewrite ?M.revmergeE revK /nilp ?(size_rev, size_merge, size_cat).
Qed.

Lemma asort1_mergeE :
  Abstract.sort1 leT merge merge' (fun x => [:: x]) [::] =1 sort1.
Proof.
rewrite /Abstract.sort1 /sort1 -/(astack_of_stack false [::]) => xs.
elim: xs (Nil (seq _)) => /= [|x xs IHxs] stack; first exact: apop_mergeE.
by rewrite -IHxs apush_mergeE.
Qed.

Lemma asort2_mergeE :
  Abstract.sort2 leT merge merge' (fun x => [:: x]) [::] =1 sort2.
Proof.
move=> xs; have [n] := ubnP (size xs).
rewrite /Abstract.sort2 /sort2 -/(astack_of_stack false [::]).
elim: n (Nil (seq _)) xs => // n IHn stack [|x [|x' xs /= /ltnW /IHn <-]] /=;
  try by rewrite apop_mergeE.
by rewrite apush_mergeE; last case: ifP.
Qed.

Lemma asort3_mergeE :
  Abstract.sort3 leT merge merge' (fun x => [:: x]) [::] =1 sort3.
Proof.
move=> xs; have [n] := ubnP (size xs).
rewrite /Abstract.sort3 /sort3 -/(astack_of_stack false [::]).
move: n (Nil (seq _)) xs.
elim=> // n IHn stack [|x [|x' [|x'' xs /= /ltnW /ltnW /IHn <-]]] /=;
  try by rewrite apop_mergeE.
rewrite apush_mergeE; last by rewrite /nilp !(size_rev, size_merge).
by rewrite !(fun_if rev, fun_if (path.merge _ _), fun_if (cons _)).
Qed.

Lemma asortN_mergeE :
  Abstract.sortN leT merge merge' (fun x => [:: x]) [::] =1 sortN.
Proof.
case=> // x xs; have [n] := ubnP (size xs).
rewrite /Abstract.sortN /sortN -/(astack_of_stack false [::]).
elim: n (Nil (seq _)) x xs => // n IHn stack x [|y xs /= /ltnSE Hxs].
  by rewrite [LHS]apop_mergeE.
rewrite /Abstract.sortNrec -/(Abstract.incr _ _ _ _) -/(Abstract.decr _ _ _ _).
pose rs := Nil T; rewrite -{1}[[:: x]]/(rcons (rev rs) x) -/(x :: rs).
elim: xs Hxs x y rs => [_|z xs IHxs /= /ltnW Hxs] x y rs.
  rewrite /Abstract.incr /Abstract.decr !apop_mergeE rev_rcons revK /= /geT.
  by case: leT.
rewrite /Abstract.incr -/(Abstract.incr _ _ _ _).
rewrite /Abstract.decr -/(Abstract.decr _ _ _ _) -/(Abstract.sortNrec _ _ _ _).
move: (IHxs Hxs y z (x :: rs)); rewrite -rev_cons rev_rcons revK /= /geT.
by do 2 case: leT; rewrite // apush_mergeE ?rev_nilp // IHn.
Qed.

Lemma apush_catE (xs ys : seq T) stack :
  flatten_stack ys (Abstract.push cat cat xs stack)
  = flatten_stack (xs ++ ys) stack.
Proof.
have [n] := ubnP (size stack).
by elim: n xs stack => // n IHn xs [|[zs [|[zs'|] stack]|stack]] //=;
  try move=> /(@ltnW _.+2) /IHn ->; rewrite !catA.
Qed.

Lemma apop_catE mode xs stack :
  Abstract.pop cat cat mode xs stack = flatten_stack xs stack.
Proof.
have [n] := ubnP (size stack).
by elim: n mode xs stack => // n IHn mode xs [|[ys stack|[|[zs|] stack]]] //=;
  try move/(@ltnW _.+2); move=> /IHn ->; rewrite ?if_same.
Qed.

Lemma asort1_catE : Abstract.sort1 leT cat cat (fun x => [:: x]) [::] =1 id.
Proof.
move=> xs; rewrite /Abstract.sort1 -[RHS]/(flatten_stack xs [::]).
elim: xs (Nil (option _)) => /= [|x xs IHxs] stack; first exact: apop_catE.
by rewrite IHxs apush_catE.
Qed.

Lemma asort2_catE : Abstract.sort2 leT cat cat (fun x => [:: x]) [::] =1 id.
Proof.
move=> xs; have [n] := ubnP (size xs).
rewrite /Abstract.sort2 -[RHS]/(flatten_stack xs [::]).
move: n (Nil (option _)) xs.
by elim=> // n IHn stack [|x [|x' xs /= /ltnW /IHn ->]] /=;
  rewrite (apop_catE, apush_catE).
Qed.

Lemma asort3_catE : Abstract.sort3 leT cat cat (fun x => [:: x]) [::] =1 id.
Proof.
move=> xs; have [n] := ubnP (size xs).
rewrite /Abstract.sort3 -[RHS]/(flatten_stack xs [::]).
move: n (Nil (option _)) xs.
by elim=> // n IHn stack [|x [|x' [|x'' xs /= /ltnW /ltnW /IHn ->]]] /=;
  rewrite (apop_catE, apush_catE).
Qed.

Lemma asortN_catE : Abstract.sortN leT cat cat (fun x => [:: x]) [::] =1 id.
Proof.
case=> // x xs; have [n] := ubnP (size xs).
rewrite /Abstract.sortN -[RHS]/(flatten_stack (x :: xs) [::]).
elim: n x (Nil (option _)) xs => // n IHn x stack [|y xs /= /ltnSE Hxs];
  first by rewrite [LHS]apop_catE.
rewrite /Abstract.sortNrec -/(Abstract.incr _ _ _ _) -/(Abstract.decr _ _ _ _).
pose rs := Nil T; rewrite -[x :: y :: _]/(rs ++ _) -[[:: x]]/(rs ++ _).
elim: xs Hxs x y rs => [_|z xs IHxs /= /ltnW Hxs] x y rs.
  by rewrite if_same [LHS]apop_catE -catA.
rewrite /Abstract.incr -/(Abstract.incr _ _ _ _).
rewrite /Abstract.decr -/(Abstract.decr _ _ _ _) -/(Abstract.sortNrec _ _ _ _).
move: (IHxs Hxs y z (rcons rs x)); rewrite IHn // apush_catE -cats1 -!catA /=.
by case: leT => ->; rewrite if_same.
Qed.

End CBV.

Definition sort1_stable :=
  StableSort sort1 Abstract.sort1 Abstract.sort1_R asort1_mergeE asort1_catE.
Definition sort2_stable :=
  StableSort sort2 Abstract.sort2 Abstract.sort2_R asort2_mergeE asort2_catE.
Definition sort3_stable :=
  StableSort sort3 Abstract.sort3 Abstract.sort3_R asort3_mergeE asort3_catE.
Definition sortN_stable :=
  StableSort sortN Abstract.sortN Abstract.sortN_R asortN_mergeE asortN_catE.

End CBV_.

Module CBV := CBV_(Revmerge).
Module CBVAcc := CBV_(RevmergeAcc).

Canonical CBV.sort1_stable.
Canonical CBV.sort2_stable.
Canonical CBV.sort3_stable.
Canonical CBV.sortN_stable.
Canonical CBVAcc.sort1_stable.
Canonical CBVAcc.sort2_stable.
Canonical CBVAcc.sort3_stable.
Canonical CBVAcc.sortN_stable.

(******************************************************************************)
(* Theory of stable sort functions                                            *)
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

Local Lemma lexordA (T : Type) (leT leT' leT'' : rel T) :
  lexord leT (lexord leT' leT'') =2 lexord (lexord leT leT') leT''.
Proof. by move=> x y /=; case: (leT x y) (leT y x) => [] []. Qed.

Section StableSortTheory_Part1.

Variable (sort : stableSort).

Local Lemma param_asort :
  StableSort.asort_ty_R (StableSort.asort sort) (StableSort.asort sort).
Proof. by case: sort. Qed.

Section SortSeq.

Variable (T : Type) (P : {pred T}) (leT : rel T).
Let geT x y := leT y x.

Local Lemma asort_mergeE :
  StableSort.asort sort leT (merge leT)
    (fun xs ys => rev (merge geT (rev ys) (rev xs))) (fun x => [:: x]) [::]
  =1 sort _ leT.
Proof. by case: sort. Qed.

Local Lemma asort_catE :
  StableSort.asort sort leT cat cat (fun x => [:: x]) [::] =1 id.
Proof. by case: sort. Qed.

Lemma sort_ind (R : seq T -> seq T -> Prop) :
  (forall xs xs', R xs xs' -> forall ys ys', R ys ys' ->
     R (cat xs ys) (merge leT xs' ys')) ->
  (forall xs xs', R xs xs' -> forall ys ys', R ys ys' ->
     R (cat xs ys) (rev (merge geT (rev ys') (rev xs')))) ->
  (forall x, R [:: x] [:: x]) -> R [::] [::] ->
  forall s, R s (sort _ leT s).
Proof.
move=> ? ? Hsingleton ? s; rewrite -[s in R s _]asort_catE -asort_mergeE.
apply: (@param_asort _ _ eq _ _ R) => //.
- by move=> ? ? -> ? ? ->; apply: bool_R_refl.
- by move=> ? ? ->; apply: Hsingleton.
by elim: s; constructor.
Qed.

Lemma all_sort (s : seq T) : all P (sort _ leT s) = all P s.
Proof.
by elim/sort_ind: (sort _ leT s) => // xs xs' IHxs ys ys' IHys;
  rewrite !(all_rev, all_merge) all_cat IHxs IHys // andbC.
Qed.

Lemma size_sort (s : seq T) : size (sort _ leT s) = size s.
Proof.
by elim/sort_ind: (sort _ leT s) => // xs xs' IHxs ys ys' IHys;
  rewrite ?size_rev size_merge !size_cat ?size_rev IHxs IHys // addnC.
Qed.

Lemma sort_nil : sort _ leT [::] = [::].
Proof. by case: (sort _) (size_sort [::]). Qed.

Lemma pairwise_sort (s : seq T) : pairwise leT s -> sort _ leT s = s.
Proof.
elim/sort_ind: (sort _ leT s) => // xs xs' IHxs ys ys' IHys.
  rewrite pairwise_cat => /and3P[hlr /IHxs -> /IHys ->].
  by rewrite !allrel_merge.
rewrite pairwise_cat => /and3P[hlr /IHxs -> /IHys ->].
by rewrite allrel_merge 1?allrel_rev2 1?allrelC // rev_cat !revK.
Qed.

Lemma sorted_sort : transitive leT ->
  forall s : seq T, sorted leT s -> sort _ leT s = s.
Proof. by move=> leT_tr s; rewrite sorted_pairwise //; apply/pairwise_sort. Qed.

End SortSeq.

Local Lemma param_sort : StableSort.sort_ty_R sort sort.
Proof.
move=> T T' T_R leT leT' leT_R xs xs' xs_R; rewrite -!asort_mergeE.
apply: (@param_asort _ _ T_R _ _ (list_R T_R) _ _ leT_R _ _ (merge_R leT_R));
  try by do ?constructor.
move=> ys ys' ys_R zs zs' zs_R; apply/rev_R/merge_R/rev_R/ys_R/rev_R/zs_R.
by move=> ? ? ? ? ? ?; apply/leT_R.
Qed.

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

Section EqSortSeq.

Variables (T : eqType) (leT : rel T).

Lemma perm_sort (s : seq T) : perm_eql (sort _ leT s) s.
Proof.
by apply/permPl; elim/sort_ind: (sort _ leT s) => // xs xs' IHxs ys ys' IHys;
  rewrite 1?perm_rev perm_merge -1?rev_cat 1?perm_rev perm_cat.
Qed.

Lemma mem_sort (s : seq T) : sort _ leT s =i s.
Proof. exact/perm_mem/permPl/perm_sort. Qed.

Lemma sort_uniq (s : seq T) : uniq (sort _ leT s) = uniq s.
Proof. exact/perm_uniq/permPl/perm_sort. Qed.

End EqSortSeq.

Lemma sort_pairwise_stable (T : Type) (leT leT' : rel T) :
  total leT -> forall s : seq T, pairwise leT' s ->
  sorted (lexord leT leT') (sort _ leT s).
Proof.
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

Lemma sort_pairwise_stable_in (T : Type) (P : {pred T}) (leT leT' : rel T) :
  {in P &, total leT} -> forall s : seq T, all P s -> pairwise leT' s ->
  sorted (lexord leT leT') (sort _ leT s).
Proof.
move=> /in2_sig leT_total _ /all_sigP[s ->].
by rewrite sort_map pairwise_map sorted_map; apply: sort_pairwise_stable.
Qed.

Lemma sort_stable (T : Type) (leT leT' : rel T) :
  total leT -> transitive leT' -> forall s : seq T, sorted leT' s ->
  sorted (lexord leT leT') (sort _ leT s).
Proof.
by move=> ? ? s; rewrite sorted_pairwise//; apply: sort_pairwise_stable.
Qed.

Lemma sort_stable_in (T : Type) (P : {pred T}) (leT leT' : rel T) :
  {in P &, total leT} -> {in P & &, transitive leT'} ->
  forall s : seq T, all P s -> sorted leT' s ->
  sorted (lexord leT leT') (sort _ leT s).
Proof.
move=> /in2_sig leT_total /in3_sig leT_tr _ /all_sigP[s ->].
by rewrite sort_map !sorted_map; apply: sort_stable.
Qed.

Lemma filter_sort (T : Type) (leT : rel T) :
  total leT -> transitive leT ->
  forall (p : pred T) (s : seq T),
    filter p (sort _ leT s) = sort _ leT (filter p s).
Proof.
move=> leT_total leT_tr p s; case Ds: s => [|x s1]; first by rewrite sort_nil.
pose lt := lexord (relpre (nth x s) leT) ltn.
have lt_tr: transitive lt by apply/lexord_trans/ltn_trans/relpre_trans.
rewrite -{s1}Ds -(mkseq_nth x s) !(filter_map, sort_map); congr map.
have lt_irr : irreflexive lt by move=> ?; rewrite /= ltnn implybF andbN.
apply/(@irr_sorted_eq _ lt); rewrite /lt /lexord //=; last 1 first.
- by move=> ?; rewrite !(mem_filter, mem_sort).
- exact/sorted_filter/sort_stable/iota_ltn_sorted/ltn_trans.
- exact/sort_stable/sorted_filter/iota_ltn_sorted/ltn_trans/ltn_trans.
Qed.

Lemma filter_sort_in (T : Type) (P : {pred T}) (leT : rel T) :
  {in P &, total leT} -> {in P & &, transitive leT} ->
  forall (p : pred T) (s : seq T),
    all P s -> filter p (sort _ leT s) = sort _ leT (filter p s).
Proof.
move=> /in2_sig leT_total /in3_sig leT_tr p _ /all_sigP[s ->].
by rewrite !(sort_map, filter_map) filter_sort.
Qed.

Lemma sort_sort (T : Type) (leT leT' : rel T) :
  total leT -> transitive leT -> total leT' -> transitive leT' ->
  forall s : seq T, sort _ leT (sort _ leT' s) = sort _ (lexord leT leT') s.
Proof.
move=> leT_total leT_tr leT'_total leT'_tr s.
case s_eq : {-}s => [|x s1]; first by rewrite s_eq !sort_nil.
pose lt' := lexord (relpre (nth x s) leT') ltn.
pose lt := lexord (relpre (nth x s) leT) lt'.
have lt'_tr: transitive lt' by apply/lexord_trans/ltn_trans/relpre_trans.
have lt_tr : transitive lt by apply/lexord_trans/lt'_tr/relpre_trans.
rewrite -(mkseq_nth x s) !(filter_map, sort_map); congr map.
apply/(@irr_sorted_eq _ lt); rewrite /lt /lexord //=.
- by move=> ?; rewrite /= ltnn !(implybF, andbN).
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

Lemma eq_sort (sort1 sort2 : stableSort) (T : Type) (leT : rel T) :
  total leT -> transitive leT -> sort1 _ leT =1 sort2 _ leT.
Proof.
move=> leT_total leT_tr s; case Ds: s => [|x s1]; first by rewrite !sort_nil.
pose lt := lexord (relpre (nth x s) leT) ltn.
have lt_tr: transitive lt by apply/lexord_trans/ltn_trans/relpre_trans.
rewrite -{s1}Ds -(mkseq_nth x s) !(filter_map, sort_map); congr map.
apply/(@irr_sorted_eq _ lt); rewrite /lt /lexord //=.
- by move=> ?; rewrite /= ltnn implybF andbN.
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

Variable (sort : stableSort).

Section Stability.

Variables (T : Type) (leT : rel T).
Variables (leT_total : total leT) (leT_tr : transitive leT).

Lemma eq_sort_insert : sort _ leT =1 Insertion.sort leT.
Proof. exact: eq_sort. Qed.

Lemma sort_cat (s1 s2 : seq T) :
  sort _ leT (s1 ++ s2) = path.merge leT (sort _ leT s1) (sort _ leT s2).
Proof. by rewrite !eq_sort_insert; elim: s1 => //= x s1 ->; rewrite mergeA. Qed.

Lemma mask_sort (s : seq T) (m : bitseq) :
  {m_s : bitseq | mask m_s (sort _ leT s) = sort _ leT (mask m s)}.
Proof.
case Ds: {-}s => [|x s1]; first by exists [::]; rewrite Ds mask0 sort_nil.
rewrite -(mkseq_nth x s) -map_mask !sort_map.
exists [seq i \in mask m (iota 0 (size s)) |
            i <- sort _ (xrelpre (nth x s) leT) (iota 0 (size s))].
rewrite -map_mask -filter_mask [in RHS]mask_filter ?iota_uniq ?filter_sort //.
by move=> ? ? ?; exact: leT_tr.
Qed.

Lemma sorted_mask_sort (s : seq T) (m : bitseq) :
  sorted leT (mask m s) -> {m_s : bitseq | mask m_s (sort _ leT s) = mask m s}.
Proof. by move/(sorted_sort sort leT_tr) <-; exact: mask_sort. Qed.

End Stability.

Section Stability_in.

Variables (T : Type) (P : {pred T}) (leT : rel T).
Hypothesis leT_total : {in P &, total leT}.
Hypothesis leT_tr : {in P & &, transitive leT}.

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

Variables (T : eqType) (leT : rel T).
Variables (leT_total : total leT) (leT_tr : transitive leT).

Lemma subseq_sort : {homo sort _ leT : t s / subseq t s}.
Proof.
move=> _ s /subseqP [m _ ->].
have [m' <-] := mask_sort leT_total leT_tr s m; exact: mask_subseq.
Qed.

Lemma sorted_subseq_sort (t s : seq T) :
  subseq t s -> sorted leT t -> subseq t (sort _ leT s).
Proof.
by move=> subseq_ts /(sorted_sort sort leT_tr) <-; exact: subseq_sort.
Qed.

Lemma mem2_sort (s : seq T) (x y : T) :
  leT x y -> mem2 s x y -> mem2 (sort _ leT s) x y.
Proof.
move=> lexy; rewrite !mem2E => /subseq_sort; rewrite !eq_sort_insert //.
by case: (_ == _); rewrite //= lexy.
Qed.

End Stability_subseq.

Section Stability_subseq_in.

Variables (T : eqType) (leT : rel T).

Lemma subseq_sort_in (t s : seq T) :
  {in s &, total leT} -> {in s & &, transitive leT} ->
  subseq t s -> subseq (sort _ leT t) (sort _ leT s).
Proof.
move=> leT_total leT_tr /subseqP [m _ ->].
have [m' <-] := mask_sort_in leT_total leT_tr m (allss _); exact: mask_subseq.
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

Arguments all_sort                sort {T} P leT s.
Arguments size_sort               sort {T} leT s.
Arguments sort_nil                sort {T} leT.
Arguments pairwise_sort           sort {T leT s} _.
Arguments sorted_sort             sort {T leT} leT_tr {s} _.
Arguments map_sort                sort {T T' f leT' leT} _ _.
Arguments sort_map                sort {T T' f leT} s.
Arguments sorted_sort_in          sort {T P leT} leT_tr {s} _ _.
Arguments perm_sort               sort {T} leT s _.
Arguments mem_sort                sort {T} leT s _.
Arguments sort_uniq               sort {T} leT s.
Arguments sort_pairwise_stable    sort {T leT leT'} leT_total {s} _.
Arguments sort_pairwise_stable_in sort {T P leT leT'} leT_total {s} _ _.
Arguments sort_stable             sort {T leT leT'} leT_total leT'_tr {s} _.
Arguments sort_stable_in          sort {T P leT leT'} leT_total leT'_tr {s} _ _.
Arguments filter_sort             sort {T leT} leT_total leT_tr p s.
Arguments filter_sort_in          sort {T P leT} leT_total leT_tr p {s} _.
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
Arguments sort_cat                sort {T leT} leT_total leT_tr s1 s2.
Arguments mask_sort               sort {T leT} leT_total leT_tr s m.
Arguments sorted_mask_sort        sort {T leT} leT_total leT_tr {s m} _.
Arguments eq_in_sort_insert       sort {T P leT} leT_total leT_tr {s} _.
Arguments sort_cat_in             sort {T P leT} leT_total leT_tr {s1 s2} _ _.
Arguments mask_sort_in            sort {T P leT} leT_total leT_tr {s} m _.
Arguments sorted_mask_sort_in     sort {T P leT} leT_total leT_tr {s m} _ _.
Arguments subseq_sort             sort {T leT} leT_total leT_tr {x y} _.
Arguments sorted_subseq_sort      sort {T leT} leT_total leT_tr {t s} _ _.
Arguments mem2_sort               sort {T leT} leT_total leT_tr {s x y} _ _.
Arguments subseq_sort_in          sort {T leT t s} leT_total leT_tr _.
Arguments sorted_subseq_sort_in   sort {T leT t s} leT_total leT_tr _ _.
Arguments mem2_sort_in            sort {T leT s} leT_total leT_tr x y _ _.
