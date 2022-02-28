<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Stable sort algorithms in Coq

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/pi8027/stablesort/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/pi8027/stablesort/actions?query=workflow:"Docker%20CI"




This library provides two kinds of optimized mergesort functions written in
Coq.
The first kind is non-tail-recursive mergesort functions. In the call-by-need
evaluation, they allow us to compute the first k smallest elements of a list
of length n in the optimal O(n + k log k) time complexity of the partial and
incremental sorting problems. However, the non-tail-recursive merge function
linearly consumes the call stack and triggers a stack overflow in the
call-by-value evaluation.
The second kind is tail-recursive mergesort functions and thus solves the
above issue in the call-by-value evaluation. However, it does not allow us to
compute the output incrementally in the optimal O(n + k log k) time regardless
of the evaluation strategy.
The point is that the best mergesort function for lists depends on the
situation, in particular, the evaluation strategy and whether it should be
incremental or not.

To prove the correctness (including stability) of these mergesort functions,
this library also provides a generic way to prove these properties. The
correctness lemmas provided in this library are overloaded using a canonical
structure (`StableSort.function`). Stable sort functions are characterized in
this interface by the parametricity axiom and binary trees representing the
divide-and-conquer structure of sort. Thus, one may prove the stability of a
new sorting function by using the parametricity translation (Paramcoq) and
by providing a lemma corresponding to the binary tree construction.

## Meta

- Author(s):
  - Kazuhiko Sakaguchi (initial)
- License: [CeCILL-B Free Software License Agreement](CeCILL-B)
- Compatible Coq versions: 8.10 or later
- Additional dependencies:
  - [MathComp](https://math-comp.github.io) 1.12.0 or later
  - [Paramcoq](https://github.com/coq-community/paramcoq) 1.1.3 or later
- Coq namespace: `stablesort`
- Related publication(s): none

## Building and installation instructions

The easiest way to install the latest released version of Stable sort algorithms in Coq
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-stablesort
```

To instead build and install manually, do:

``` shell
git clone https://github.com/pi8027/stablesort.git
cd stablesort
make   # or make -j <number-of-cores-on-your-machine> 
make install
```


## Credits
The mergesort functions and the stability proofs provided in this library are
mostly based on ones in the `path` library of Mathematical Components.
