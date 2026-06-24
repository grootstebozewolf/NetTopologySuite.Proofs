# Self-contained Nix build (ready to use with a recent nixpkgs):
#   nix-build                       # build with the default coqPackages
#   nix-build --arg coq ...         # or override the Rocq/Coq version
#
# Sources are vendored from the corpus: run ./assemble.sh first (or build the
# release tarball, which is already assembled). Build uses the package Makefile
# (coq_makefile via _CoqProject); no Flocq or other external Coq deps.
{ pkgs ? import <nixpkgs> { }
, coqPackages ? pkgs.coqPackages
}:
coqPackages.mkCoqDerivation {
  pname = "spatial-algebra";
  owner = "grootstebozewolf";
  version = "0.1.0";
  src = ./.;
  # Pure Stdlib; zero external Coq dependencies, zero axioms.
  propagatedBuildInputs = [ ];
  meta = {
    description = "DE-9IM intersection-matrix algebra and integer orientation-determinant bounds (axiom-free)";
    license = pkgs.lib.licenses.bsd3;
  };
}
