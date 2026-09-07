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
#
# Phase 5 adds a second consumer of the SAME extracted.ml: the in-process C ABI
# `libntsrocq` (nts_ffi.ml + nts_ffi_stubs.c + nts_ffi.h), which .NET binds with
# DllImport instead of forking oracle_bin per call.
#
#   make -C oracle ffi          # builds libntsrocq.so + the ffi_probe driver
#   make -C oracle ffi-parity   # gates FFI == oracle_bin, bit for bit
#
# If `make ffi` fails with Unbound value b64_orient2d_exact, re-extract:
#   ./scripts/rebuild_oracle_ffi.sh [--parity]
#   (see docs/ffi-rungs-2026-08.md)
#
# =============================================================================

OCAMLOPT := ocamlfind ocamlopt
TARGET   := oracle_bin

# ---- Phase 5 FFI -----------------------------------------------------------
# The bundled OCaml runtime must be the PIC build (libasmrun_pic.a): the plain
# libasmrun.a in -output-complete-obj is non-PIC and cannot go into a shared
# object.  So: -output-obj (no runtime) + explicit -lasmrun_pic.
OCAML_WHERE := $(shell $(OCAMLOPT) -where)
CC          ?= cc
FFI_SOEXT   := so
FFI_LIB     := libntsrocq.$(FFI_SOEXT)
FFI_PROBE   := ffi_probe
FFI_CFLAGS  := -O2 -fPIC -I$(OCAML_WHERE) -I.
FFI_LDLIBS  := -L$(OCAML_WHERE) -lasmrun_pic -lm -ldl -lpthread

# Mesh scout lane: in-circle-only FFI (does not need full nts_ffi.ml extraction).
SCOUT_IC_LIB   := libscout_incircle.$(FFI_SOEXT)
SCOUT_IC_PROBE := scout_incircle_probe

.PHONY: all clean ffi ffi-parity jts1093-orient-scout scout-incircle-ffi jts1094-scout arc-arc-tests arc-segment-tests arc-arc-distance-tests arc-segment-distance-tests ring-simple-tests cp-ring-simple-tests cp-boundary-simplify-tests cp-boundary-simplify-test arc-offset-tests point-in-curve-ring-tests ring-orientation-tests holes-disjoint-tests curve-relate-matrix-tests buffer-region-tests arc-centroid-tests arc-area-centroid-tests arc-distance-tests arc-area-tests arc-buffer-simple-tests arc-simplify-decision-tests arc-offset-filtered-tests curve-adversarial-hunt elliptic-hunt bezier-hunt winding-number-tests disc-overlay-tests lec-circle-tests obstacle-distance-tests i-circular-tests

all: $(TARGET)

# Adversarial ARC_ARC_XY suite (issue #64 #5b / N-AA): drives oracle_bin and
# gates the Qed-proven invariants (I1 on-both-circles, I2 shared-vertex>=1,
# I3 symmetry, I4 reversal-stable).  Nonzero exit on any violation.
arc-arc-tests: $(TARGET)
	cd .. && python3 oracle/gen_arc_arc_tests.py

# Extracted Year-1 circular 𝓘 (I_CIRCULAR / CircularCookZ.v). Gates I1 locked
# HIT 0 1, I2 EMPTY, I3–I5 DECLINE, I6 replay hens. Nonzero exit on violation.
i-circular-tests: $(TARGET)
	cd .. && python3 oracle/gen_i_circular_tests.py

# Adversarial DISC_OVERLAY suite (OV-DISC / OverlayNGCurve two-disc): gates
# the Qed-proven invariants (I1 nodes on both circles, I2 locked fixture
# (3.5, ±√12.75), I3 CAP+XOR=CUP, I4 CAP+SUB=π r1², I5 disjoint areas,
# I6 CAP/CUP/XOR symmetry, I7 coincident-reject).  Nonzero exit on violation.
disc-overlay-tests: $(TARGET)
	cd .. && python3 oracle/gen_disc_overlay_tests.py

# Adversarial LEC_CIRCLE suite (LargestEmptyCircle closed form): gates the
# Qed-proven invariants of theories/LECChordGap.v (I1 exact echo, I2 locked
# sqrt2 pin at n=4/r=2, I3 chord-path underestimate + monotone convergence,
# I4 CIRCULARSTRING == direct form, I5 degenerate/NaN verdicts).  Nonzero
# exit on any violation.
lec-circle-tests: $(TARGET)
	cd .. && python3 oracle/gen_lec_circle_tests.py

# Adversarial OBSTACLE_DISTANCE suite (LEC typed obstacle clearance): gates
# the Qed-proven invariants of theories/LECObstacleDistance.v (I1 3-4-5
# witness pins, I2 clamped-weighted-min mirror, I3 filled-disc vs ring,
# I4 flatten/permutation, I5 witness-rectangle grid bound + maximisers,
# I6 degenerate/NaN verdicts).  Nonzero exit on any violation.
obstacle-distance-tests: $(TARGET)
	cd .. && python3 oracle/gen_obstacle_distance_tests.py

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

# CP_BOUNDARY_SIMPLIFY suite (Oracle wishlist #1: surfaces): densify a
# CurvePolygon ring -> EXTRACTED greedy_simplify_perp_b64 -> EXTRACTED
# b64_orient_sign_filtered per corner.  Gates I1 certified-scope (INTSAFE vs
# APPROX), I2 simplifier-sound (totality/head/length), I3 filter-honest
# (UNCERTAIN on near-collinear-at-scale).  Nonzero exit on any violation.
cp-boundary-simplify-tests: $(TARGET)
	cd .. && python3 oracle/gen_cp_boundary_simplify_tests.py > oracle/cp_boundary_simplify_tests.txt

# CurvePolygon exterior-ring boundary test (F-CP Option A, issue #849):
# builds sample CurvePolygons (oracle/curve_polygon.py) and asserts the
# CP_BOUNDARY_SIMPLIFY V/O output + INTSAFE/APPROX tagging.  Nonzero exit on
# any failed assertion.
cp-boundary-simplify-test: $(TARGET)
	ORACLE_BIN=./oracle_bin python3 test_cp_boundary_simplify.py

# Adversarial ARC_OFFSET_XY suite (OFF/BUF-1/BUF-NEG, JTS #1195 §7): gates
# I1 radial-dist |d|, I2 distance |r+d| from centre, I3 radial ray (homothety),
# I4 EMPTY iff r+d<=0, I5 identity at d=0.  Nonzero exit on any violation.
# Full slice: signed, collapse/3pt/EMPTY boundary, huge coords, major sweeps, tiny.
arc-offset-tests: $(TARGET)
	cd .. && python3 oracle/gen_arc_offset_tests.py

# V-CP holes-inside-shell (JTS #1195 §7): POINT_IN_CURVE_RING vs exact ray-parity
# (Overlay.point_in_ring) on the densified control polygon.  Gates I1 agreement
# over a query grid, I2 holes-inside-shell composition.  Nonzero exit on violation.
point-in-curve-ring-tests: $(TARGET)
	cd .. && python3 oracle/gen_point_in_curve_ring_tests.py

# V-CP sector orientation (JTS #1195 §7): RING_ORIENTATION true signed area
# (chord shoelace + arc sector areas) -> CCW/CW.  Gates I1 known-orientation,
# I2 reversal flips, I3 agreement vs recompute, I4 true-vs-inscribed.  Nonzero exit.
ring-orientation-tests: $(TARGET)
	cd .. && python3 oracle/gen_ring_orientation_tests.py

# V-CP holes-mutually-disjoint (JTS #1195 §7): HOLES_DISJOINT (boundary meet +
# nesting) over two curve rings.  Gates I1 CROSS witness-soundness, I2 curated
# DISJOINT/CROSS/nesting, I3 symmetry.  Nonzero exit on any violation.
holes-disjoint-tests: $(TARGET)
	cd .. && python3 oracle/gen_holes_disjoint_tests.py

# R-PR CURVE_RELATE_MATRIX (JTS #1195 §7): COMPUTE the full TRUE-OGC 9-cell
# DE-9IM of two curve geometries.  Gates I1 curated matrices, I2 transpose-under-
# swap, I3 independent dense-sampling agreement, I4 OGC predicates.  Nonzero exit
# on any violation.
curve-relate-matrix-tests: $(TARGET)
	cd .. && python3 oracle/gen_curve_relate_matrix_tests.py

# BUF-1 / BUF-NEG BUFFER_REGION (JTS #1195 §7): assemble the offset boundary of a
# closed curve ring + its signed area.  Gates I1 parallel-distance, I2 area vs
# Minkowski sampling, I3 convex Steiner, I4 EMPTY, I5 d=0 identity, I6 monotonic.
# Nonzero exit on any violation.
buffer-region-tests: $(TARGET)
	cd .. && python3 oracle/gen_buffer_region_tests.py

# C-LIN ARC_CENTROID: arc length weighted centroid of circular arc.  Gates I1 dist==offset,
# I2 on bisector, specials, bounds, degenerate.  Backing ArcCentroid.v .
arc-centroid-tests: $(TARGET)
	cd .. && python3 oracle/gen_arc_centroid_tests.py

# C-AREA ARC_AREA_CENTROID: area centroid of circular segment.  Gates I1 bounds,
# I2 bisector, specials, nonneg, degenerate.  Backing ArcAreaCentroid.v .
arc-area-centroid-tests: $(TARGET)
	cd .. && python3 oracle/gen_arc_area_centroid_tests.py

# D-PT ARC_DISTANCE: point to arc shortest dist with sweep clamp + endpoint fallback.
# Gates I1 radial if in, I2 fallback, I3 degen, I4 center, I5 nonneg. Backing ArcPointDistance.v + ArcDistance.v
arc-distance-tests: $(TARGET)
	cd .. && python3 oracle/gen_arc_distance_tests.py

# M-AREA-CP ARC_AREA: circular segment area (between arc + chord). Gates I1 nonneg,
# I2 semicircle pi r^2/2, I3 full pi r^2, I4 degen + formula match. Backing ArcArea.v .
arc-area-tests: $(TARGET)
	cd .. && python3 oracle/gen_arc_area_tests.py

# ARC_BUFFER_SIMPLE (single arc → CurvePolygon, BUF-1 cheap lane)
# Uses BUFFER_REGION on degenerate arc+chord ring + extra arc-offset checks.
arc-buffer-simple-tests: $(TARGET)
	cd .. && python3 oracle/gen_arc_buffer_simple_tests.py

arc-simplify-decision-tests: $(TARGET)
	printf 'ARC_SIMPLIFY_DECISION\nA 1 0 0 1 -1 0\n0.01\n' | ./$(TARGET) | grep -q PRESERVE_ARC && echo 'ARC_SIMPLIFY_DECISION basic ok'

arc-offset-filtered-tests: $(TARGET)
	printf 'ARC_OFFSET_FILTERED\nA 1 0 0 1 -1 0\n0.5\n' | ./$(TARGET) | grep -q FILTERED && echo 'ARC_OFFSET_FILTERED basic ok'

# WINDING_NUMBER: signed ray-crossing winding number for linear polygon rings.
# Gates I1 parity↔POINT_IN_CURVE_RING agreement, I2 simple→|w|≤1, I3 sign-flip
# under reversal, I4 exterior=0.  Star polygon shows |w|=2 (non-simple).
# Backing proof: theories/WindingNumber.v (winding_decides_membership, Qed).
winding-number-tests: $(TARGET)
	cd .. && python3 oracle/gen_winding_number_tests.py > oracle/winding_number_tests.txt

# CurveType hunters (0=CircularArc, 1=EllipticArc, 2=Bezier3Curve).
# These are the primary "adversarial tests for the enum" created via oracle-driven search.
curve-adversarial-hunt:
	cd .. && python3 oracle/gen_adversarial_curves.py --types 0,1,2 --budget 20000

elliptic-hunt:
	cd .. && python3 oracle/gen_adversarial_curves.py --types 1 --budget 10000

bezier-hunt:
	cd .. && python3 oracle/gen_adversarial_curves.py --types 2 --budget 10000

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

# ---- Phase 5: in-process C ABI (libntsrocq) --------------------------------

ffi: $(FFI_LIB) $(FFI_PROBE)

nts_ffi.cmx: nts_ffi.ml extracted.cmi extracted.cmx
	$(OCAMLOPT) -c nts_ffi.ml

# -output-obj emits the OCaml side WITHOUT the runtime; the runtime comes in
# below as libasmrun_pic.a so the result is linkable into a shared object.
nts_ffi_ml.o: extracted.cmx nts_ffi.cmx
	$(OCAMLOPT) -output-obj extracted.cmx nts_ffi.cmx -o nts_ffi_ml.o

nts_ffi_stubs.o: nts_ffi_stubs.c nts_ffi.h
	$(CC) $(FFI_CFLAGS) -c nts_ffi_stubs.c -o nts_ffi_stubs.o

$(FFI_LIB): nts_ffi_ml.o nts_ffi_stubs.o
	$(CC) -shared -o $@ nts_ffi_ml.o nts_ffi_stubs.o $(FFI_LDLIBS)

# Parity driver: same inputs as oracle_bin, results printed as raw IEEE 754
# bit patterns so the comparison cannot be blurred by float formatting.
$(FFI_PROBE): ffi_probe.c nts_ffi.h $(FFI_LIB)
	$(CC) -O2 -I. ffi_probe.c -o $@ -L. -lntsrocq -Wl,-rpath,'$$ORIGIN'

# Gate: every FFI entry point must agree with oracle_bin bit for bit.
ffi-parity: $(TARGET) $(FFI_PROBE)
	cd .. && python3 oracle/gen_ffi_parity_tests.py

# Orientation lane (jts#1093): Ozaki vs Shewchuk Stage A vs ORIENT_EXACT.
# Does not require libntsrocq; optional FFI_PROBE for filtered parity spot-check.
jts1093-orient-scout: $(TARGET)
	cd .. && python3 oracle/gen_jts1093_orient_scout.py

# ---- Mesh scout: in-circle-only FFI (JTS #1094 / #1212 lane) ---------------
# Builds when full `make ffi` cannot (stale extracted.ml missing e.g.
# b64_orient2d_exact).  Same b64_inCircle symbol as production nts_rocq_in_circle.
scout_incircle_ffi.cmx: scout_incircle_ffi.ml extracted.cmi extracted.cmx
	$(OCAMLOPT) -c scout_incircle_ffi.ml

scout_incircle_ml.o: extracted.cmx scout_incircle_ffi.cmx
	$(OCAMLOPT) -output-obj extracted.cmx scout_incircle_ffi.cmx -o scout_incircle_ml.o

scout_incircle_stubs.o: scout_incircle_stubs.c nts_ffi.h
	$(CC) $(FFI_CFLAGS) -c scout_incircle_stubs.c -o scout_incircle_stubs.o

$(SCOUT_IC_LIB): scout_incircle_ml.o scout_incircle_stubs.o
	$(CC) -shared -o $@ scout_incircle_ml.o scout_incircle_stubs.o $(FFI_LDLIBS)

$(SCOUT_IC_PROBE): scout_incircle_probe.c nts_ffi.h $(SCOUT_IC_LIB)
	$(CC) -O2 -I. scout_incircle_probe.c -o $@ -L. -lscout_incircle -Wl,-rpath,'$$ORIGIN'

scout-incircle-ffi: $(SCOUT_IC_LIB) $(SCOUT_IC_PROBE)

# Differential gate for JTS#1094 vs nts_rocq_in_circle (scout FFI).
jts1094-scout: scout-incircle-ffi $(TARGET)
	cd .. && python3 oracle/gen_jts1094_incircle_scout.py \
	  --oracle oracle/oracle_bin \
	  --ffi-probe oracle/scout_incircle_probe

clean:
	rm -f *.cmi *.cmo *.cmx *.o $(TARGET) $(FFI_LIB) $(FFI_PROBE) \
	  $(SCOUT_IC_LIB) $(SCOUT_IC_PROBE) scout_incircle_ml.o scout_incircle_stubs.o
