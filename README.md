<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Stable sort algorithms in Rocq

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/pi8027/stablesort/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/pi8027/stablesort/actions/workflows/docker-action.yml




This library provides a generic and modular way to prove the correctness,
including stability, of several mergesort functions. The correctness lemmas in
this library are overloaded using a canonical structure
(`StableSort.function`). This structure characterizes stable mergesort
functions, say `sort`, by its abstract version `asort` parameterized over the
type of sorted lists and its operators such as merge, the relational
parametricity of `asort`, and two equational properties that `asort`
instantiated with merge and concatenation are `sort` and the identity
function, respectively, which intuitively mean that replacing merge with
concatenation turns `sort` into the identity function.
From this characterization, we derive an induction principle over
traces—binary trees reflecting the underlying divide-and-conquer structure of
mergesort—to reason about the relation between the input and output of
`sort`, and the naturality of `sort`. These two properties are sufficient to
deduce several correctness results of mergesort, including stability. Thus,
one may prove the stability of a new sorting function by defining its abstract
version, proving the relational parametricity of the latter using the
parametricity translation (the Paramcoq plugin), and manually providing the
equational properties.

As an application of the above proof methodology, this library provides two
kinds of optimized mergesorts.
The first kind is non-tail-recursive mergesort. In call-by-need evaluation,
they allow us to compute the first k smallest elements of a list of length n
in the optimal O(n + k log k) time complexity of the partial and incremental
sorting problems. However, the non-tail-recursive merge function linearly
consumes the call stack and triggers a stack overflow in call-by-value
evaluation.
The second kind is tail-recursive mergesorts and thus solves the above issue
in call-by-value evaluation. However, it does not allow us to compute the
output incrementally regardless of the evaluation strategy.
Therefore, there is a performance trade-off between non-tail-recursive and
tail-recursive mergesorts, and the best mergesort function for lists depends
on the situation, in particular, the evaluation strategy and whether it should
be incremental or not.
In addition, each of the above two kinds of mergesort functions has a smooth
(also called natural) variant of mergesort, which takes advantage of sorted
slices in the input.

## Meta

- Author(s):
  - Kazuhiko Sakaguchi (initial)
  - Cyril Cohen
- License: [CeCILL-B Free Software License Agreement](CeCILL-B)
- Compatible Coq versions: 8.13 or later
- Additional dependencies:
  - [MathComp](https://math-comp.github.io) 1.13.0 or later
  - [Paramcoq](https://github.com/coq-community/paramcoq) 1.1.3 or later
  - [Mczify](https://github.com/math-comp/mczify) (required only for the test suite)
  - [Equations](https://github.com/mattam82/Coq-Equations) (required only for the test suite)
- Coq namespace: `stablesort`
- Related publication(s):
  - [A bargain for mergesorts — How to prove your mergesort correct and stable, almost for free](https://arxiv.org/abs/2403.08173) doi:[10.48550/arXiv.2403.08173](https://doi.org/10.48550/arXiv.2403.08173)

## Building and installation instructions
The easiest way to install the development version of Stable sort algorithms in Rocq
is via [OPAM](https://opam.ocaml.org/doc/Install.html):
``` shell
git clone https://github.com/pi8027/stablesort.git
cd stablesort
opam repo add rocq-released https://rocq-prover.org/opam/released
opam install ./coq-stablesort.opam
```

## Credits
The mergesort functions and the stability proofs provided in this library are
mostly based on ones in the `path` library of Mathematical Components.
