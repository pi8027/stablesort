{ mkCoqDerivation, coq, mathcomp, paramcoq,
  version ? null }:

mkCoqDerivation {
  pname = "stablesort";
  defaultVersion = "null";
  inherit version;
  propagatedBuildInputs = [ mathcomp paramcoq ];
}
