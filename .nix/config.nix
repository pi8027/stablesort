with builtins; with (import <nixpkgs> {}).lib;
{
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  ## The attribute to build from the local sources,
  ## either using nixpkgs data or the overlays located in `.nix/coq-overlays`
  ## Will determine the default main-job of the bundles defined below
  attribute = "stablesort";

  ## If you want to select a different attribute (to build from the local sources as well)
  ## when calling `nix-shell` and `nix-build` without the `--argstr job` argument
  # shell-attribute = "{{nix_name}}";

  ## Lists the dependencies, phrased in terms of nix attributes.
  ## No need to list Coq, it is already included.
  ## These dependencies will systematically be added to the currently
  ## known dependencies, if any more than Coq.
  ## /!\ Remove this field as soon as the package is available on nixpkgs.
  ## /!\ Manual overlays in `.nix/coq-overlays` should be preferred then.
  # buildInputs = [ ];

  ## Indicate the relative location of your _CoqProject
  ## If not specified, it defaults to "_CoqProject"
  # coqproject = "_CoqProject";

  ## select an entry to build in the following `bundles` set
  ## defaults to "default"
  default-bundle = "9.3-2.6.0";

  ## write one `bundles.name` attribute set per
  ## alternative configuration
  ## When generating GitHub Action CI, one workflow file
  ## will be created per bundle
  bundles = let
    ## The combinations of MathComp and Rocq versions we test
    matrix = {
      "2.5.0" = ["9.0" "9.1"];
      "2.6.0" = ["9.0" "9.1" "9.2" "9.3"];
      "master" = ["9.1" "9.2" "9.3" "master"];
    };
    ## The fragments of bundles for each version of Rocq
    rocq-bundles = {
      "master".rocqPackages.stdlib.override.version = "master";
      "master".rocqPackages.equations.override.version = "master";
      "master".rocqPackages.rocq-elpi.override.version = "master";
      "master".rocqPackages.rocq-elpi.job = false;
      "master".rocqPackages.hierarchy-builder.override.version = "master";
      "master".rocqPackages.micromega-plugin.override.version = "master";
      "master".rocqPackages.micromega-plugin.job = false;
    };
    ## The fragments of bundles for each version of MathComp
    mc-bundles = {
      "master".rocqPackages.mathcomp-zify.override.version = "master";
    }; in
    attrsets.concatMapAttrs (mc: lists.foldr (rocq: bs:
      bs // {
      ${rocq + "-" + mc} = {
        rocqPackages =
          { rocq-core.override.version = rocq;
            stdlib.job = true;
            coq.override.version = rocq;
            equations.job = true;
            hierarchy-builder.job = true;
            mathcomp.override.version = mc;
            mathcomp.job = false;
            mathcomp-boot.job = true;
            mathcomp-order.job = true;
            mathcomp-algebra.job = true;
            mathcomp-zify.job = true; }
          // rocq-bundles.${rocq}.rocqPackages or { }
          // mc-bundles.${mc}.rocqPackages or { }; };
    }) { }) matrix;

  ## Cachix caches to use in CI
  ## Below we list some standard ones
  cachix.coq = { };
  cachix.math-comp = { };
  cachix.coq-community = { };

  ## If you have write access to one of these caches you can
  ## provide the auth token or signing key through a secret
  ## variable on GitHub. Then, you should give the variable
  ## name here. For instance, coq-community projects can use
  ## the following line instead of the one above:
  # cachix.coq-community.authToken = "CACHIX_AUTH_TOKEN";

  ## Or if you have a signing key for a given Cachix cache:
  # cachix.my-cache.signingKey = "CACHIX_SIGNING_KEY"

  ## Note that here, CACHIX_AUTH_TOKEN and CACHIX_SIGNING_KEY
  ## are the names of secret variables. They are set in
  ## GitHub's web interface.
}
