#!/usr/bin/env bash
# Adversarial test generator driven by RocqRefRunner (oracle_bin).
#
# Sweeps known orientation / in-circle failure families and classifies each
# case against the EXACT ground truth (ORIENT_EXACT / INCIRCLE_EXACT -- the
# runnable forms of Qed-proven b64_orient2d_exact_sound and the ArcOrient.v
# inCircle sign family).  Labels:
#   NAIVE_WRONG    : the plain-double predicate gives a definite WRONG sign.
#   FILTER_UNSOUND : the Shewchuk Stage-A filter COMMITS a definite WRONG sign
#                    (POS/NEG/ZERO) -- only possible outside its proven
#                    |coord| <= 2^25 regime; here via the unguarded
#                    `Some Eq => OrientRZero` branch (float-zero det treated as
#                    collinear with no error-bound check).
#   FILTER_FLOAT_WRONG : float in-circle (INCIRCLE_SIGN) gives a wrong sign.
# `UNCERTAIN`/`NAN` from the filter are sound PUNTS, not failures, and are not
# emitted as adversarial.
#
# Run: bash oracle/gen_adversarial_tests.sh > oracle/adversarial_tests.txt
BIN=./oracle/oracle_bin
sgn(){ awk '{print $1}'; }
o()  { printf 'ORIENT\n%s\n%s\n%s\n' "$1" "$2" "$3" | "$BIN" | sgn; }
of() { printf 'ORIENT_FILTERED\n%s\n%s\n%s\n' "$1" "$2" "$3" | "$BIN" | sgn; }
ox() { printf 'ORIENT_EXACT\n%s\n%s\n%s\n' "$1" "$2" "$3" | "$BIN"; }
ic() { printf 'INCIRCLE_SIGN\n%s\n%s\n%s\n%s\n' "$1" "$2" "$3" "$4" | "$BIN" | sgn; }
ix() { printf 'INCIRCLE_EXACT\n%s\n%s\n%s\n%s\n' "$1" "$2" "$3" "$4" | "$BIN"; }
committed(){ case "$1" in POS|NEG|ZERO) return 0;; *) return 1;; esac; }

echo "# Adversarial tests via RocqRefRunner (exact oracle = ground truth)."
echo "# Emitted only when a cheap predicate is DEFINITELY WRONG vs the exact sign."
echo "# Sound punts (filter UNCERTAIN / NAN) are not failures and are omitted."
echo
echo "## A: near-collinear product-collision  P=(0,0),(2^k+1,2^k+2),(2^k,2^k+1)  (true=POS, det=1)"
nfirst=""; ffirst=""
for k in $(seq 24 52); do
  b=$((2**k)); p1="$((b+1)) $((b+2))"; p2="$b $((b+1))"
  n=$(o "0 0" "$p1" "$p2"); f=$(of "0 0" "$p1" "$p2"); x=$(ox "0 0" "$p1" "$p2")
  lbl=""
  [ "$n" != "$x" ] && lbl="NAIVE_WRONG" && [ -z "$nfirst" ] && nfirst=$k
  if committed "$f" && [ "$f" != "$x" ]; then lbl="${lbl:+$lbl,}FILTER_UNSOUND"; [ -z "$ffirst" ] && ffirst=$k; fi
  [ -n "$lbl" ] && echo "  k=$k coord=2^$k naive=$n filtered=$f EXACT=$x  <- $lbl"
done
echo "  (threshold: naive first wrong at 2^$nfirst; filter first commits-wrong at 2^$ffirst -- just past the proven |coord|<=2^25 boundary)"
echo
echo "## C: in-circle overflow  A=(2^k,0) B=(0,2^k) C=(-2^k,0) P=(0,0)  (true=POS)"
for k in 256 400 510 512 513 520 600; do
  c="0x1p+$k"; s=$(ic "$c 0" "0 $c" "-$c 0" "0 0"); x=$(ix "$c 0" "0 $c" "-$c 0" "0 0")
  [ "$s" != "$x" ] && echo "  k=$k float_incircle=$s EXACT=$x  <- FILTER_FLOAT_WRONG"
done
echo
echo "## Note (orientation overflow, non-cancelling): P=(0,0),(2^k,0),(0,2^k) gives a single"
echo "## positive product -> +inf, whose SIGN is still correct (naive=POS=EXACT); the filter"
echo "## conservatively PUNTS (UNCERTAIN).  Not adversarial -- documented for completeness."
