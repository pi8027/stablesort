This directory provides the supplementary material for the paper:
[A bargain for mergesorts — How to prove your mergesort correct and stable, almost for free](https://arxiv.org/abs/2403.08173).

- `Section3.v` is the Rocq formalization of Section 3, that provides:
  + the simpler version of the characteristic property that work only for
    non-tail-recursive mergesorts (Section 3.2),
  + the proofs that the insertion sort (Definition 3.1), top-down mergesort
    (Figure 2a), and bottom-up mergesort (Figure 2b) satisfy the characteristic
    property (Section 3.3), and
  + generic correctness proofs (Section 3.4), including all the lemmas listed in
    Appendix B.
- `Section4_1.v` is the Rocq formalization of top-down tail-recursive mergesort,
  that provides:
  + a Rocq implementation of top-down tail-recursive mergesort (Section 4.1) and
  + the proof that it satisfies the characteristic property provided by
    `stablesort.v` (Section 4.3.2).
- `AppendicesAB.v` re-exports the definitions and lemmas listed in Appendices A
  and B from the MathComp and Stablesort libraries.
- `AppendixC.v` is the Rocq formalization of Section 3.4.3 and Appendix C, that
  provides:
  + The proofs of the stability results in literature (Lemmas C.1 and C.2),
    showing that they are easy consequences of our stability result (mainly
    Theorem 3.16), and
  + The converse proof that Lemma C.1 implies a slighly less-general version
    Theorem 3.11 and Theorem 3.16, under some assumptions on `sort`.
- `AppendixD.v` provides copies of the implementations (excluding proofs) of
  mergesort functions in `stablesort.v`, with some stylistic modifications,
  e.g., replacing `seq` with `list`, and adding `{struct ..}` annotations.
