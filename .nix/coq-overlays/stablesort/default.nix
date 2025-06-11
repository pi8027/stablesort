{ mkCoqDerivation, coq, mathcomp, paramcoq, mathcomp-zify, equations,
  version ? null }:

mkCoqDerivation {
  pname = "stablesort";
  defaultVersion = "null";
  inherit version;
  propagatedBuildInputs = [ mathcomp.ssreflect paramcoq mathcomp-zify equations ];
}
