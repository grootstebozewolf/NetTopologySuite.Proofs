#!/bin/sh
# Generate hot-pixel passes-through hardening vectors for the Rocq <-> JTS
# differential bridge (snap-rounding noder; see GitHub issue #66).
#
# For each segment (P0,P1) and unit-grid hot-pixel centre C we emit BOTH:
#   * FILTER  -- the rounded computational filter the JTS noder mirrors
#               (oracle PASSES_THROUGH_FILTER = extracted
#               b64_passes_through_hot_pixel_compute), and
#   * EXACT   -- the exact-rational ground truth (oracle PASSES_THROUGH_EXACT,
#               zarith Q, no rounding).
#
# Where FILTER=TRUE but EXACT=FALSE the rounded filter OVER-ACCEPTS: a segment
# that exactly misses the closed pixel by a sub-ulp margin is flagged as a
# pass.  This is provably intrinsic to the rounded Liang-Barsky divide-and-clip
# (machine-checked: theories-flocq/PassesThrough_b64_compute_unsound.v); it is
# a conservative over-approximation, SAFE for a noder ("when uncertain, keep")
# but NOT sound against the sharp closed pixel.  JTS hardens its noder by
# diffing its own predicate against FILTER (must agree, bit-exact) and noting
# the EXACT column as the true geometry (the band requiring conservative
# treatment).
#
# Coordinate encoding (exact, round-trip-safe in OCaml + Java):
#   integers |c| <= 2^53 -> decimal;  off-grid bits -> hex float.
# Format:  x0 y0 x1 y1 cx cy  FILTER=<v> EXACT=<v>      # note     (v in TRUE/FALSE)
# Regenerate: sh oracle/gen_passes_through_vectors.sh > oracle/passes_through_proof_vectors.txt
BIN=./oracle/oracle_bin

emit() {
  f=$(printf 'PASSES_THROUGH_FILTER\n%s %s\n%s %s\n%s %s\n' "$1" "$2" "$3" "$4" "$5" "$6" | "$BIN")
  e=$(printf 'PASSES_THROUGH_EXACT\n%s %s\n%s %s\n%s %s\n'  "$1" "$2" "$3" "$4" "$5" "$6" | "$BIN")
  printf '%s %s %s %s %s %s  FILTER=%s EXACT=%s        # %s\n' "$1" "$2" "$3" "$4" "$5" "$6" "$f" "$e" "$7"
}
emit_ho() {
  f=$(printf 'PASSES_THROUGH_HALFOPEN\n%s %s\n%s %s\n%s %s\n'       "$1" "$2" "$3" "$4" "$5" "$6" | "$BIN")
  e=$(printf 'PASSES_THROUGH_HALFOPEN_EXACT\n%s %s\n%s %s\n%s %s\n' "$1" "$2" "$3" "$4" "$5" "$6" | "$BIN")
  printf '%s %s %s %s %s %s  HALFOPEN=%s HALFOPEN_EXACT=%s        # %s\n' "$1" "$2" "$3" "$4" "$5" "$6" "$f" "$e" "$7"
}

echo "# Hot-pixel passes-through hardening vectors (oracle PASSES_THROUGH_{FILTER,EXACT})."
echo "# Provenance: theories-flocq/PassesThrough_b64_compute_unsound.v and"
echo "#             PassesThroughHalfopen_b64_compute_unsound.v (GitHub #66)."
echo "# x0 y0 x1 y1 cx cy  FILTER=<v> EXACT=<v>   (rounded filter vs exact ground truth)"
echo "#"
echo "# --- agreement: clean passes and misses (FILTER == EXACT) ---"
emit 0.0 0.0   2.0 0.0    1.0 0.0   "segment through pixel centre -- pass"
emit 0.0 0.0   0.0 10.0   5.0 5.0   "far miss"
emit 0.0 -0.5  0.0 0.5    0.0 0.0   "vertical segment through centre"
echo "# --- ADVERSARIAL: rounded filter OVER-ACCEPTS (FILTER=TRUE, EXACT=FALSE) ---"
echo "# Machine-checked counterexample (b64_passes_through_compute_unsound): the"
echo "# segment misses the closed pixel by a sub-ulp margin; exact tlo_x ="
echo "# 2^49/(2^49+1) > thi_y = (2^49-1)/2^49, so the exact clipped t-interval is"
echo "# empty, but the rounded b64_div closes the gap inward."
emit 0x1p+0 -0x1.0000000000002p+1   0x1.ffffffffffffp-2 -0x1.4000000000002p+1   0x0p+0 -0x1p+1   "sub-ulp tangency, bottom-right corner"
echo "#"
echo "# --- half-open mode: same over-acceptance (HALFOPEN=TRUE, HALFOPEN_EXACT=FALSE) ---"
echo "# Counterexample (b64_passes_through_halfopen_compute_unsound): the closed"
echo "# witness reflected (x negated) to a bottom-LEFT tangency so the half-open"
echo "# strict midpoint checks pass while the exact geometry still misses."
emit_ho -0x1p+0 -0x1.0000000000002p+1   -0x1.ffffffffffffp-2 -0x1.4000000000002p+1   0x0p+0 -0x1p+1   "sub-ulp tangency, bottom-left corner"
echo "# Half-open agreement sanity:"
emit_ho 0.0 0.0   2.0 0.0   1.0 0.0   "segment through centre -- pass"
