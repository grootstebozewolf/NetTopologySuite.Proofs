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
echo

# --- D: hot-pixel passes-through (rounded FILTER/HALFOPEN vs EXACT ground truth) -----------
ptf() { printf 'PASSES_THROUGH_FILTER\n%s\n%s\n%s\n'         "$1" "$2" "$3" | "$BIN"; }
ptx() { printf 'PASSES_THROUGH_EXACT\n%s\n%s\n%s\n'          "$1" "$2" "$3" | "$BIN"; }
pth() { printf 'PASSES_THROUGH_HALFOPEN\n%s\n%s\n%s\n'       "$1" "$2" "$3" | "$BIN"; }
phx() { printf 'PASSES_THROUGH_HALFOPEN_EXACT\n%s\n%s\n%s\n' "$1" "$2" "$3" | "$BIN"; }
oa=0; hoa=0; cdrop=0; hdrop=0; brk=0; exbrk=0; nseen=0
rep_oa=""; rep_hoa=""; rep_hdrop=""; rep_cdrop=""
ptcheck() {  # $1=P0 $2=P1 $3=C ; silent: counts, captures one representative per class,
             # and emits IMMEDIATELY only on a proven-invariant violation ('!!' = bug).
  f=$(ptf "$1" "$2" "$3"); e=$(ptx "$1" "$2" "$3")
  h=$(pth "$1" "$2" "$3"); hx=$(phx "$1" "$2" "$3")
  nseen=$((nseen+1)); row="P0=($1) P1=($2) C=($3) FILTER=$f EXACT=$e HALFOPEN=$h HALFOPEN_EXACT=$hx"
  # PROVEN invariants -- a violation is a RocqRefRunner bug.
  [ "$h" = TRUE ]  && [ "$f" = FALSE ] && { brk=$((brk+1));   echo "  !! BRACKET_VIOLATION (HALFOPEN>FILTER, b64_..._halfopen_compute_implies_closed): $row"; }
  [ "$hx" = TRUE ] && [ "$e" = FALSE ] && { exbrk=$((exbrk+1)); echo "  !! EXACT_BRACKET_VIOLATION (HALFOPEN_EXACT>EXACT): $row"; }
  # Empirical rounded-vs-exact divergences -- the hardening signal (not bugs).
  [ "$f" = TRUE ]  && [ "$e"  = FALSE ] && { oa=$((oa+1));    [ -z "$rep_oa" ]    && rep_oa="$row"; }
  [ "$h" = TRUE ]  && [ "$hx" = FALSE ] && { hoa=$((hoa+1));  [ -z "$rep_hoa" ]   && rep_hoa="$row"; }
  [ "$e" = TRUE ]  && [ "$f"  = FALSE ] && { cdrop=$((cdrop+1)); [ -z "$rep_cdrop" ] && rep_cdrop="$row"; }
  [ "$hx" = TRUE ] && [ "$h"  = FALSE ] && { hdrop=$((hdrop+1)); [ -z "$rep_hdrop" ] && rep_hdrop="$row"; }
}
echo "## D: hot-pixel passes-through near-tangency  (rounded FILTER/HALFOPEN vs EXACT)."
echo "## EXACT = exact-rational ground truth (oracle PASSES_THROUGH_EXACT / _HALFOPEN_EXACT)."
echo "##"
echo "## PROVEN invariants (Qed) -- any '!!' line below would be a RocqRefRunner bug:"
echo "##   HALFOPEN      => FILTER       (b64_passes_through_hot_pixel_halfopen_compute_implies_closed)"
echo "##   HALFOPEN_EXACT => EXACT       (b64_liang_barsky_touches_halfopen_implies_closed)"
echo "##"
echo "## Empirical rounded-vs-exact divergences (the hardening signal, NOT bugs):"
echo "##   FILTER_OVERACCEPT  : closed filter TRUE, exact FALSE -- rounded b64_div closes a"
echo "##       sub-ulp tangency gap inward.  Conservative/SAFE for a noder; machine-checked"
echo "##       unsound vs the sharp pixel (PassesThrough_b64_compute_unsound.v)."
echo "##   HALFOPEN_DROP      : half-open filter FALSE, exact half-open TRUE -- the rounded"
echo "##       strict-midpoint check rounds a near-OPEN-edge witness onto the excluded"
echo "##       boundary and MISSES a real pass.  The half-open compute filter is NOT complete"
echo "##       (the closed filter only over-accepts; the half-open one can also under-accept)."
echo "##       NODER-RELEVANT: HALFOPEN mode can drop crossings grazing the open top/right edge."
echo
echo "# Machine-checked over-acceptance witnesses (Qed counterexamples), shown explicitly:"
W0="0x1p+0 -0x1.0000000000002p+1";  W1="0x1.ffffffffffffp-2 -0x1.4000000000002p+1";  WC="0x0p+0 -0x1p+1"
N0="-0x1p+0 -0x1.0000000000002p+1"; N1="-0x1.ffffffffffffp-2 -0x1.4000000000002p+1"
echo "  closed,   bottom-right: FILTER=$(ptf "$W0" "$W1" "$WC") EXACT=$(ptx "$W0" "$W1" "$WC")  (FILTER_OVERACCEPT)"
echo "  halfopen, bottom-left:  HALFOPEN=$(pth "$N0" "$N1" "$WC") HALFOPEN_EXACT=$(phx "$N0" "$N1" "$WC")  (HALFOPEN_OVERACCEPT)"
echo
# Validation sweep: half-integer + sub-ulp near-edge grid around C=(0,0).
G="-1 -0.5 0 0.5 1 0x1.fffffffffffffp-2 0x1.0000000000001p-1"
for x0 in $G; do for y0 in $G; do for x1 in $G; do for y1 in $G; do
  ptcheck "$x0 $y0" "$x1 $y1" "0 0"
done; done; done; done
echo "# Validation sweep over $nseen cases (C=(0,0)):"
echo "#   PROVEN invariants: BRACKET violations=$brk  EXACT_BRACKET violations=$exbrk   (both MUST be 0)"
echo "#   closed completeness: FILTER drops a real pass=$cdrop   (closed filter is a complete over-approximation)"
echo "#   divergences: FILTER_OVERACCEPT=$oa  HALFOPEN_OVERACCEPT=$hoa  HALFOPEN_DROP=$hdrop"
[ -n "$rep_oa" ]    && echo "#   e.g. FILTER_OVERACCEPT: $rep_oa"
[ -n "$rep_hdrop" ] && echo "#   e.g. HALFOPEN_DROP:     $rep_hdrop"

# Self-validation: the two PROVEN (Qed) invariants must never be violated.
# A nonzero exit here means the RocqRefRunner contradicts a machine-checked
# theorem -- a real oracle regression.  (Empirical divergences above do not
# fail.)  Lets this generator double as a CI validation gate.
if [ "$brk" -ne 0 ] || [ "$exbrk" -ne 0 ]; then
  echo "::error::RocqRefRunner violated a proven passes-through invariant (BRACKET=$brk EXACT_BRACKET=$exbrk)." >&2
  exit 1
fi
