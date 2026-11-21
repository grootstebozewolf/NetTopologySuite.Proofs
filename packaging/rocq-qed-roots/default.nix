# Self-contained Nix build (ready to use with a recent nixpkgs):
#   nix-build
#
# Sources are vendored from the corpus: run ./assemble.sh first (or build the
# release tarball, which is already assembled). Build uses the package Makefile
# (coq_makefile via _CoqProject); Stdlib only, no Flocq.
{ pkgs ? import <nixpkgs> { }
, coqPackages ? pkgs.coqPackages
}:
coqPackages.mkCoqDerivation {
  pname = "rocq-qed-roots";
  owner = "MerkatorBV";
  version = "0.1.0";
  src = ./.;
  propagatedBuildInputs = [ ];
  meta = {
    description = "Kernel-checked real-root certificates for polynomials from rational coefficient enclosures";
    license = pkgs.lib.licenses.bsd3;
  };
}
