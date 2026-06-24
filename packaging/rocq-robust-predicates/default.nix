# Self-contained Nix build (ready to use with a recent nixpkgs):
#   nix-build
#
# Sources are vendored from the corpus: run ./assemble.sh first (or build the
# release tarball, which is already assembled). Build uses the package Makefile
# (coq_makefile via _CoqProject). Depends on Flocq (coqPackages.flocq).
{ pkgs ? import <nixpkgs> { }
, coqPackages ? pkgs.coqPackages
}:
coqPackages.mkCoqDerivation {
  pname = "robust-predicates";
  owner = "grootstebozewolf";
  version = "0.1.0";
  src = ./.;
  propagatedBuildInputs = [ coqPackages.flocq ];
  meta = {
    description = "Machine-checked robust binary64 geometric predicates, sound vs. exact arithmetic";
    license = pkgs.lib.licenses.bsd3;
  };
}
