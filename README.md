<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Stable sort algorithms in Rocq

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/pi8027/stablesort/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/pi8027/stablesort/actions/workflows/docker-action.yml




This library provides a characterization of stable mergesort functions using
relational parametricity, and deduces several functional correctness results,
including stability, solely from the characteristic property. This library
allows the users to prove their mergesort correct just by proving that the
mergesort in question satisfies the characteristic property. The functional
correctness lemmas are overloaded using a canonical structure
(`StableSort.function`) that bundles the characteristic property, and
automatically apply to any declared instance of this structure.

As instances of the characteristic property, this library provides two kinds
of optimized mergesorts.
The first kind is non-tail-recursive mergesort. In call-by-need evaluation,
they compute the first k smallest elements of a list of length n in
O(n + k log k) time, which is known to be the optimal time complexity of the
partial and incremental sorting problems. However, the non-tail-recursive
merge function linearly consumes the call stack and triggers a stack overflow
in call-by-value evaluation.
The second kind is tail-recursive mergesorts and thus solves the above issue
in call-by-value evaluation. However, it does not allow us to compute the
output incrementally regardless of the evaluation strategy.
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
  - [Mczify](https://github.com/math-comp/mczify) (required only for `icfp25/`)
  - [Equations](https://github.com/mattam82/Coq-Equations) (required only for `icfp25/`)
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

## Files
The [`theories/`](theories/) directory is the main part of the library. The
[`icfp25/`](icfp25/) directory, which has a dedicated README file, contains
Rocq files corresponding more closely to the paper.

## Credits
The mergesort functions and the stability proofs provided in this library are
mostly based on ones in the `path` library of Mathematical Components.
