{ mkRocqDerivation, rocq-core, rocq-elpi, equations, mathcomp-boot, mathcomp-order, mathcomp-zify,
  version ? null }:

mkRocqDerivation {
  pname = "stablesort";
  defaultVersion = "null";
  inherit version;
  propagatedBuildInputs =
    [ rocq-elpi equations mathcomp-boot mathcomp-order mathcomp-zify ];
}
