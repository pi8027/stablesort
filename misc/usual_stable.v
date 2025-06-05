(******************************************************************************)
(* Appendix C                                                                 *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
From stablesort Require Import stablesort.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Implicit Types (sort : stableSort) (T R S : Type).

Local Lemma relpre_trans {T' T} {leT : rel T} {f : T' -> T} :
  transitive leT -> transitive (relpre f leT).
Proof. by move=> + y x z; apply. Qed.

Definition lexord T (leT leT' : rel T) :=
  [rel x y | leT x y && (leT y x ==> leT' x y)].

Local Lemma lexord_trans T (leT leT' : rel T) :
  transitive leT -> transitive leT' -> transitive (lexord leT leT').
Proof. exact: stablesort.lexord_trans. Qed.

Local Lemma lexord_irr T (leT leT' : rel T) :
  irreflexive leT' -> irreflexive (lexord leT leT').
Proof. exact: stablesort.lexord_irr. Qed.

Local Lemma total_refl {T} (r : rel T) : total r -> reflexive r.
Proof. by move=> rt x; have /orP[] := rt x x. Qed.

Definition eqr {T} (r : rel T) : rel T := [rel x y | r x y && r y x].

Local Lemma eqr_sym {T} (r : rel T) : symmetric (eqr r).
Proof. by move=> x y; apply/andP/andP => -[]. Qed.
#[local] Hint Resolve eqr_sym : core.

Local Lemma eqrW {T} (r : rel T) : subrel (eqr r) r.
Proof. by move=> x y /andP[]. Qed.

Local Lemma eqr_trans {T} (r : rel T) : transitive r -> transitive (eqr r).
Proof.
by move=> tr y x z /andP[? ?] /andP[? ?]; apply/andP; split; apply: (tr y).
Qed.
Arguments eqr_trans {T r}.

Local Lemma eqr_refl {T} (r : rel T) : reflexive r -> reflexive (eqr r).
Proof. by move=> rr x; rewrite /eqr/= rr. Qed.

(* Lemma C.1 [Leroy [n. d.]] *)
Lemma sort_usual_stable sort T (leT : rel T) :
  total leT -> transitive leT ->
  forall (x : T) (s : list T),
    [seq y <- sort T leT s | eqr leT x y] = [seq y <- s | eqr leT x y].
Proof.
move=> leT_total leT_trans x s.
apply/sorted_filter_sort/(@path_sorted _ _ x) => //.
move: (filter _ _) (filter_all (fun y => leT x y && leT y x) s) => {}s.
elim: s x => //= x s IHs y /andP[/andP[yx xy] alls] /=.
rewrite yx IHs //; apply: sub_all alls => z /andP[yz zy].
by rewrite (leT_trans _ _ _ xy yz) (leT_trans _ _ _ zy yx).
Qed.

(* Lemma C.2 [Leino and Lucio 2015; Sternagel 2013] *)
From mathcomp Require Import order.
Import Order.TTheory.

Lemma sort_stable_sternagel
    sort T d (T' : orderType d) (key : T -> T') (x : T) (s : list T) :
  [seq y <- sort T (relpre key <=%O) s | key x == key y] =
    [seq y <- s | key x == key y].
Proof.
have key_total: total (relpre key <=%O) by move=> ? ?; apply: le_total.
have key_trans: transitive (relpre key <=%O) by move=> ? ? ?; apply: le_trans.
by congr eq: (sort_usual_stable sort key_total key_trans x s);
  apply: eq_filter => ?; rewrite eq_le.
Qed.

(* The converse implication *)

Section UsualStableSortTheory.

Section extract.
Context {T : Type} (x0 : T).
Implicit Types (P : {pred T}) (s : list T).

Local Definition egraph P s := filter (preim (nth x0 s) P) (iota 0 (size s)).
Arguments egraph : simpl never.
Definition extract P s := nth (size s) (egraph P s).
Definition unextract P s i := index i (egraph P s).

Local Lemma size_egraph P s : size (egraph P s) = count P s.
Proof. by rewrite size_filter -count_map map_nth_iota0 ?take_size. Qed.

Lemma extractK P s :
  {in gtn (count P s), cancel (extract P s) (unextract P s)}.
Proof.
rewrite /extract /unextract => i iPs.
by rewrite index_uniq ?size_egraph// filter_uniq ?iota_uniq.
Qed.

Definition extract_codom P s :=
  [predI (gtn (size s)) & preim (nth x0 s) P].

Lemma unextractK P s :
   {in extract_codom P s, cancel (unextract P s) (extract P s)}.
Proof.
rewrite /extract /unextract => i /[!inE] /andP[ilts Pi].
by rewrite nth_index// mem_filter /= Pi mem_iota.
Qed.

Definition extract_inj P s := can_in_inj (@extractK P s).

Local Lemma egraph_cons P s x : egraph P (x :: s) =
  if P x then 0 :: map S (egraph P s) else map S (egraph P s).
Proof.
by rewrite /egraph/=; case: ifPn => ?; rewrite (iotaDl 1) filter_map.
Qed.

Lemma extract_out P s i : i >= count P s -> extract P s i = size s.
Proof. by move=> igt; rewrite /extract nth_default// size_egraph. Qed.

Lemma extract_lt P s i : i < count P s -> extract P s i < size s.
Proof.
move=> ilt; apply/(@all_nthP _ (gtn (size s))); rewrite ?size_egraph//=.
by apply/allP => j /=; rewrite mem_filter inE mem_iota => /and3P[].
Qed.

Lemma unextract_lt P s i : i \in extract_codom P s ->
  unextract P s i < count P s.
Proof.
move=> /[!inE] /andP[ilt iPs]; rewrite /unextract -size_egraph index_mem.
by rewrite mem_filter/= mem_iota ilt iPs.
Qed.

Lemma nth_filter P s i : nth x0 (filter P s) i = nth x0 s (extract P s i).
Proof.
have [ismall|ilarge] := ltnP i (count P s); last first.
  by rewrite !nth_default// ?size_filter// /extract nth_default// size_egraph.
rewrite /extract; elim: s => [|x s IHs]//= in i ismall *.
rewrite egraph_cons; case: ifPn => [Px|PNx]/= in ismall *; last first.
  by rewrite IHs//= (nth_map (size s)) ?size_egraph.
case: i ismall => // i; rewrite ltnS => ismall /=.
by rewrite IHs// (nth_map (size s))//= size_egraph.
Qed.

Lemma nth_unextract P s i : i \in extract_codom P s ->
  nth x0 (filter P s) (unextract P s i) = nth x0 s i.
Proof. by move=> iPs; rewrite nth_filter ?unextractK. Qed.

Lemma extractP P s i : i < count P s -> P (nth x0 s (extract P s i)).
Proof.
move=> iPs; rewrite -nth_filter.
by apply/all_nthP; rewrite ?filter_all// size_filter.
Qed.

Lemma le_extract P s :
   {in gtn (count P s) &, {mono extract P s : i j / i <= j}}.
Proof.
apply: leq_mono_in => i j /[!inE] ilt jlt ij.
have ltn_trans := ltn_trans.
apply: (@sorted_ltn_nth _ ltn); rewrite -?topredE ?size_egraph//.
by rewrite sorted_filter// iota_ltn_sorted.
Qed.
Definition lt_extract P s := leqW_mono_in (@le_extract P s).

Lemma le_unextract P s :
  {in extract_codom P s &, {mono unextract P s : i j / i <= j}}.
Proof.
apply: can_mono_in (@le_extract P s); first exact/onW_can_in/unextractK.
by move=> i idom; rewrite inE unextract_lt.
Qed.
Definition lt_unextract P s := leqW_mono_in (@le_unextract P s).

End extract.

Context (sort : forall T, rel T -> list T -> list T).
Hypothesis sort_nil : forall T (leT : rel T), sort leT [::] = [::].
Hypothesis sort_sorted :
  forall T (leT : rel T) (s : list T), total leT -> sorted leT (sort leT s).
Hypothesis sort_usual_stable :
  forall T (leT : rel T), total leT -> transitive leT ->
  forall (s : list T) (x : T),
    filter (eqr leT x) (sort leT s) = filter (eqr leT x) s.

(* Lemma C.3 *)
Lemma usual_stable_sort_pairwise_stable T (leT leT' : rel T) :
  total leT -> transitive leT ->
  forall s : list T, pairwise leT' s -> sorted (lexord leT leT') (sort leT s).
Proof.
move=> leT_total leT_tr s.
wlog x0 : / T by case: s => [|x s']; [rewrite sort_nil//|apply].
move=> s_sorted; apply/(sortedP x0) => i; set s':= sort leT s => iSlt /=.
set u := nth x0 _; pose P := eqr leT (u i).
have lui : leT (u i) (u i.+1) by rewrite (sortedP _ _) ?sort_sorted.
rewrite lui/=; apply/implyP => gui.
have iPs : i \in extract_codom x0 P s'.
  by rewrite !inE ltnW//; apply/eqr_refl/total_refl.
have iSPs : i.+1 \in extract_codom x0 P s'.
  by rewrite !inE iSlt//=; apply/andP.
pose v := nth x0 (filter P s).
suff: exists j k, [/\ j < k < size (filter P s), u i = v j & u i.+1 = v k].
  move=> [j [k [/andP[jk klt] -> ->]]].
  apply: pairwiseP => //; first by rewrite pairwise_filter.
  by rewrite inE (ltn_trans _ klt).
exists (unextract x0 P s' i), (unextract x0 P s' i.+1).
rewrite /v -sort_usual_stable// lt_unextract//= ?nth_unextract//.
by split=> //; rewrite leqnn/= size_filter unextract_lt.
Qed.

(* Lemma C.4 *)
Lemma usual_stable_sort_stable T (leT leT' : rel T) :
  total leT -> transitive leT -> transitive leT' ->
  forall s : seq T, sorted leT' s -> sorted (lexord leT leT') (sort leT s).
Proof.
move=> leT_total leT_tr leT'_tr s; rewrite sorted_pairwise//.
exact: usual_stable_sort_pairwise_stable.
Qed.

Hypothesis mem_sort :
  forall (T : eqType) (leT : rel T) (s : seq T), sort leT s =i s.
Hypothesis sort_map :
  forall (T T' : Type) (f : T' -> T) (leT : rel T) (s : seq T'),
    sort leT (map f s) = map f (sort (relpre f leT) s).

(* Lemma C.5 *)
Lemma usual_stable_filter_sort T (leT : rel T) :
  total leT -> transitive leT ->
  forall (p : pred T) (s : seq T),
    filter p (sort leT s) = sort leT (filter p s).
Proof.
move=> leT_total leT_tr p s; case Ds: s => [|x s1]; first by rewrite sort_nil.
pose lt := lexord (relpre (nth x s) leT) ltn.
have lt_tr: transitive lt by apply/lexord_trans/ltn_trans/relpre_trans.
rewrite -{s1}Ds -(mkseq_nth x s) !(filter_map, sort_map); congr map.
apply/(@irr_sorted_eq _ lt); rewrite /lt /lexord //=.
- exact/lexord_irr/ltnn.
- apply/sorted_filter/usual_stable_sort_stable/iota_ltn_sorted/ltn_trans => //.
  by move=> ? ? ?; apply/leT_tr.
- apply/usual_stable_sort_stable/sorted_filter/iota_ltn_sorted => //.
  + by move=> ? ? ?; apply/leT_tr.
  + exact/ltn_trans.
  + exact/ltn_trans.
- by move=> ?; rewrite !(mem_filter, mem_sort).
Qed.

End UsualStableSortTheory.
