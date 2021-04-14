<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Stable sort algorithms in Coq

[![Docker CI][docker-action-shield]][docker-action-link]

[docker-action-shield]: https://github.com/pi8027/stablesort/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/pi8027/stablesort/actions?query=workflow:"Docker%20CI"




This library provides a generic way to prove the stability of sorting
algorithms. The stability lemmas provided in this library are overloaded using
a canonical structure (`StableSort.interface`), and stable sort functions are
characterized in this interface by the parametricity axiom and binary trees
representing the divide-and-conquer structure of sort. One may prove the
stability of a new sorting function by using the parametricity translation
(Paramcoq) and providing a lemma corresponding to the binary tree
construction. This library also provides optimized mergesort algorithms: one
for the call-by-need evaluation (`CBNOpt.sort`) and another for the
call-by-value evaluation (`CBVOpt.sort`).

The mergesort functions and the stability proofs provided in this library are
mostly based on ones in the `path` library of Mathematical Components.

## Meta

- Author(s):
  - Kazuhiko Sakaguchi (initial)
- License: [CeCILL-B Free Software License Agreement](CeCILL-B)
- Compatible Coq versions: 8.10 or later
- Additional dependencies:
  - [MathComp](https://math-comp.github.io) 1.12.0 or later
  - [Paramcoq](https://github.com/coq-community/paramcoq) 1.1.2 or later
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



