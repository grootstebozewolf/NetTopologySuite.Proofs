# Makefile for coq-robust-predicates.
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
	tar czf ../coq-robust-predicates.tar.gz \
	    --transform 's,^,coq-robust-predicates/,' \
	    MANIFEST _CoqProject Makefile assemble.sh README.md LICENSE \
	    coq-robust-predicates.opam theories theories-flocq
	@echo "Wrote ../coq-robust-predicates.tar.gz"

clean:
	@if [ -f Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall || true; fi
	rm -f Makefile.coq Makefile.coq.conf

# Remove vendored sources too (back to the committed infra-only state).
distclean: clean
	rm -rf theories theories-flocq

.PHONY: all install package clean distclean
