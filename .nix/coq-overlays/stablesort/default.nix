{ mkCoqDerivation, coq, mathcomp, paramcoq, mathcomp-zify, equations,
  version ? null }:

mkCoqDerivation {
  pname = "stablesort";
  defaultVersion = "null";
  inherit version;
  propagatedBuildInputs = [ mathcomp paramcoq mathcomp-zify equations ];
}
