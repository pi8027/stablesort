{ mkCoqDerivation, coq, paramcoq, equations, mathcomp-ssreflect, mathcomp-zify,
  version ? null }:

mkCoqDerivation {
  pname = "stablesort";
  defaultVersion = "null";
  inherit version;
  propagatedBuildInputs =
    [ paramcoq equations mathcomp-ssreflect mathcomp-zify ];
}
