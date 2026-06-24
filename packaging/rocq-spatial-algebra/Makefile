# Makefile for coq-spatial-algebra.
#
# Delegates to the Rocq-generated Makefile.coq.  Run ./assemble.sh first to
# vendor the source .v files from the corpus (the opam source tarball produced
# by `make package` already contains them).

COQPROJECT := _CoqProject
COQMAKE    := rocq makefile

all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: $(COQPROJECT)
	$(COQMAKE) -f $(COQPROJECT) -o Makefile.coq

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

# Produce a self-contained opam source tarball (vendors files, then archives).
package: clean
	./assemble.sh
	mkdir -p dist
	tar czf dist/coq-spatial-algebra.tar.gz \
	    --transform 's,^,coq-spatial-algebra/,' \
	    MANIFEST _CoqProject Makefile assemble.sh README.md LICENSE \
	    coq-spatial-algebra.opam dune-project default.nix theories
	@echo "Wrote dist/coq-spatial-algebra.tar.gz"

clean:
	@if [ -f Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall || true; fi
	rm -f Makefile.coq Makefile.coq.conf

# Remove vendored sources too (back to the committed infra-only state).
# Keeps theories/dune (committed); only the assembled *.v are removed.
distclean: clean
	rm -f theories/*.v

.PHONY: all install package clean distclean
