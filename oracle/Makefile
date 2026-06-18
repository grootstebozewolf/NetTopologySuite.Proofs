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

.PHONY: all clean arc-arc-tests arc-segment-tests arc-arc-distance-tests arc-segment-distance-tests ring-simple-tests cp-ring-simple-tests arc-offset-tests

all: $(TARGET)

# Adversarial ARC_ARC_XY suite (issue #64 #5b / N-AA): drives oracle_bin and
# gates the Qed-proven invariants (I1 on-both-circles, I2 shared-vertex>=1,
# I3 symmetry, I4 reversal-stable).  Nonzero exit on any violation.
arc-arc-tests: $(TARGET)
	cd .. && python3 oracle/gen_arc_arc_tests.py

# Adversarial ARC_SEGMENT_XY suite (issue #224 W1 / N-AL): gates the proven
# invariants (I1 on-circle, I2 on-segment t in [0,1], I3 seg-reversal,
# I4 arc-reversal).  Nonzero exit on any violation.
arc-segment-tests: $(TARGET)
	cd .. && python3 oracle/gen_arc_segment_tests.py

# Adversarial ARC_ARC_DISTANCE suite (D-AA, JTS #1195 §7): gates the proven
# invariants (I1 lower-bound, I2 non-negative, I3 symmetry, I4 reversal-stable,
# I5 intersection-zero).  Nonzero exit on any violation.
arc-arc-distance-tests: $(TARGET)
	cd .. && python3 oracle/gen_arc_arc_distance_tests.py

# Adversarial ARC_SEGMENT_DISTANCE suite (D-SL, JTS #1195 §7): gates the proven
# invariants (I1 upper vs sampled pairs, I2 lower vs circle-line gap, I3 non-neg,
# I4 segment-reversal, I5 arc-reversal, I6 crossing=0).  Nonzero exit on violation.
arc-segment-distance-tests: $(TARGET)
	cd .. && python3 oracle/gen_arc_segment_distance_tests.py

# Adversarial RING_SIMPLE suite (V-CS/V-CP, JTS #1195 §7): gates the proven
# witness-soundness (I1: every NOT_SIMPLE witness lies on both non-adjacent
# segments, curve_ring_not_simple_of_witness), curated classes (I2), and
# rotation invariance (I3).  Nonzero exit on any violation.
ring-simple-tests: $(TARGET)
	cd .. && python3 oracle/gen_ring_simple_tests.py

# V-CP ring-simplicity component (JTS #1195 §7): composes RING_SIMPLE over a
# CurvePolygon's shell + hole rings.  Gates I1 composition, I2 per-ring
# witness-soundness, I3 hole-reuse.  Nonzero exit on any violation.
cp-ring-simple-tests: $(TARGET)
	cd .. && python3 oracle/gen_cp_ring_simple_tests.py

# Adversarial ARC_OFFSET_XY suite (OFF/BUF-1/BUF-NEG, JTS #1195 §7): gates
# I1 radial-dist |d|, I2 distance |r+d| from centre, I3 radial ray (homothety),
# I4 EMPTY iff r+d<=0, I5 identity at d=0.  Nonzero exit on any violation.
arc-offset-tests: $(TARGET)
	cd .. && python3 oracle/gen_arc_offset_tests.py

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
