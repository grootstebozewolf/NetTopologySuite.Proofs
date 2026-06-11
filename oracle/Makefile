# =============================================================================
# oracle/Makefile
# -----------------------------------------------------------------------------
# Compiles the Coq-extracted `extracted.ml` together with `driver.ml`
# into the standalone oracle binary `oracle_bin`.  Assumes `ocamlfind`
# and `ocamlopt` from the same OCaml toolchain that Rocq's extraction
# targets (the Dockerfile pins OCaml 4.14.2 + flambda).
#
# Two-stage workflow:
#
#   make -f Makefile.gen        # in project root: regenerates oracle/extracted.ml
#   make -C oracle              # here: compiles oracle_bin from extracted + driver
#
# `extracted.ml` is gitignored -- always regenerated from `Validate_binary64_extract.v`.
# =============================================================================

OCAMLOPT := ocamlfind ocamlopt
TARGET   := oracle_bin

.PHONY: all clean

all: $(TARGET)

extracted.cmi: extracted.mli
	$(OCAMLOPT) -c $<

extracted.cmx: extracted.ml extracted.cmi
	$(OCAMLOPT) -c extracted.ml

relate_matrix.cmx: relate_matrix.ml
	$(OCAMLOPT) -c $<

driver.cmx: driver.ml extracted.cmi relate_matrix.cmx
	$(OCAMLOPT) -package zarith -c driver.ml

$(TARGET): extracted.cmx driver.cmx relate_matrix.cmx
	$(OCAMLOPT) -package str,zarith -linkpkg extracted.cmx relate_matrix.cmx driver.cmx -o $@

clean:
	rm -f *.cmi *.cmo *.cmx *.o $(TARGET)
