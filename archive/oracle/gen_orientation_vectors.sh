#!/bin/sh
# Generate certified orientation proof vectors for the Rocq <-> JTS bridge
# (locationtech/jts#1106 / PR #1197 orientation_proof_vectors.txt slot).
#
# Each EXPECTED sign is computed by the oracle's ORIENT_EXACT mode -- the
# runnable form of the Qed-proven b64_orient2d_exact_sound (exact over ALL
# finite binary64; no DD [2^-511, 2^511] band limit).
#
# Coordinate encoding (all EXACT, round-trip-safe in OCaml + Java):
#   * integers with |c| <= 2^53           -> decimal (exact)
#   * pure powers of two outside that band -> hex float (e.g. 0x1p+512)
# Format (one vector per non-comment line):  x0 y0 x1 y1 x2 y2 EXPECTED
#   EXPECTED in { POS, NEG, ZERO }.
# Regenerate: sh oracle/gen_orientation_vectors.sh > oracle/orientation_proof_vectors.txt
BIN=./oracle/oracle_bin
emit() {
  s=$(printf 'ORIENT_EXACT\n%s %s\n%s %s\n%s %s\n' "$1" "$2" "$3" "$4" "$5" "$6" | "$BIN")
  printf '%s %s %s %s %s %s %s        # %s\n' "$1" "$2" "$3" "$4" "$5" "$6" "$s" "$7"
}
echo "# Rocq-certified orientation proof vectors (oracle ORIENT_EXACT)."
echo "# Provenance: theories-flocq/Orient_b64_exact_full.v : b64_orient2d_exact_sound."
echo "# x0 y0 x1 y1 x2 y2 EXPECTED   (EXPECTED in {POS,NEG,ZERO})"
echo "#"
echo "# --- basic ---"
emit 0 0  1 0  0 1   "unit CCW"
emit 0 0  0 1  1 0   "unit CW"
emit 0 0  1 1  2 2   "collinear y=x"
echo "# --- adversarial near-collinear at 2^27 (exact integers; naive double det rounds to 0) ---"
emit 0 0  134217729 134217730  134217728 134217729   "P=(0,0),(2^27+1,2^27+2),(2^27,2^27+1); exact=+1, naive double=ZERO"
echo "# --- OVERFLOW band edge ~2^512: DD products -> inf -> NaN -> signum 0 (wrong ZERO) ---"
emit 0 0  0x1p+512 0  0 0x1p+512   "CCW; DD returns ZERO (overflow) -- WRONG"
emit 0 0  0 0x1p+512  0x1p+512 0   "CW; DD returns ZERO (overflow) -- WRONG"
echo "# --- UNDERFLOW band edge ~2^-540: DD products flush to 0 (wrong ZERO) ---"
emit 0 0  0x1p-540 0  0 0x1p-540   "CCW; DD returns ZERO (underflow) -- WRONG"
emit 0 0  0 0x1p-540  0x1p-540 0   "CW; DD returns ZERO (underflow) -- WRONG"
echo "# --- huge dynamic range, non-degenerate ---"
emit 0x1p-300 0x1p-300  0x1p+300 0  0 0x1p+300   "CCW across ~600 binades"
