<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Stable sort algorithms in Rocq

[![Docker CI][docker-action-shield]][docker-action-link]
[![DOI][doi-shield]][doi-link]

[docker-action-shield]: https://github.com/pi8027/stablesort/actions/workflows/docker-action.yml/badge.svg?branch=master
[docker-action-link]: https://github.com/pi8027/stablesort/actions/workflows/docker-action.yml



[doi-shield]: https://zenodo.org/badge/DOI/10.5281/zenodo.15649813.svg
[doi-link]: https://doi.org/10.5281/zenodo.15649813

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
- Compatible Rocq/Coq versions: 8.19 or later
- Additional dependencies:
  - [MathComp](https://math-comp.github.io) ssreflect 2.3.0 or later
  - [Paramcoq](https://github.com/coq-community/paramcoq) 1.1.3 or later
  - [Mczify](https://github.com/math-comp/mczify) (required only for `icfp25/`)
  - [Equations](https://github.com/mattam82/Coq-Equations) (required only for `icfp25/`)
- Rocq/Coq namespace: `stablesort`
- Related publication(s):
  - [A bargain for mergesorts — How to prove your mergesort correct and stable, almost for free](https://arxiv.org/abs/2403.08173) doi:[10.48550/arXiv.2403.08173](https://doi.org/10.48550/arXiv.2403.08173)


## Files
The [`theories/`](theories/) directory is the main part of the library. The
[`icfp25/`](icfp25/) directory contains Rocq files corresponding more closely
to the paper. The latter files are not a part of the installation (see below),
and explained further in the [dedicated README file](icfp25/README.md).

## Building and installation instructions
The easiest way to install the development version of Stable sort algorithms in Rocq
and its dependencies is via [OPAM](https://opam.ocaml.org/doc/Install.html):
```shell
git clone https://github.com/pi8027/stablesort.git
cd stablesort
opam repo add rocq-released https://rocq-prover.org/opam/released
```
To build and install the `theories/` files:
```shell
opam install ./rocq-stablesort.opam
```
Alternatively, to build and install only the dependencies:
```shell
opam install ./rocq-stablesort.opam --deps-only --with-test
```
Given that the dependencies are installed, you can use one of the following
`make` targets to manually build the Rocq files:
- The default target: builds the `theories/` files.
- `build-icfp25`: builds the `icfp25/` files.
- `validate`: checks the compiled `theories/` files and their dependencies
  and prints a summary about their context (such as axioms), which should show
  that the `theories/` files are axiom-free.
- `validate-icfp25`: checks the compiled `icfp25/` files and their
  dependencies and prints a summary about their context, which should print
  the axiom of dependent functional extensionality
  (`functional_extensionality_dep`) on which the Equation plugin relies.


## Credits
The technique to make mergesort functions structurally-recursive and the
functional correctness proofs of mergesort, except for the use of
parametricity, are largely based on the `path` library of Mathematical
Components, to which the authors made significant contributions (in pull
requests [#328](https://github.com/math-comp/math-comp/pull/328),
[#358](https://github.com/math-comp/math-comp/pull/358),
[#601](https://github.com/math-comp/math-comp/pull/601),
[#650](https://github.com/math-comp/math-comp/pull/650),
[#680](https://github.com/math-comp/math-comp/pull/680),
[#727](https://github.com/math-comp/math-comp/pull/727),
[#1174](https://github.com/math-comp/math-comp/pull/1174), and
[#1186](https://github.com/math-comp/math-comp/pull/1186)).
The authors would like to thank other MathComp developers and contributors who
contributed to the discussion: Yves Bertot, Christian Doczkal, Georges
Gonthier, Assia Mahboubi, and Anton Trunov.
