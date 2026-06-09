#!/bin/sh
# =============================================================================
# oracle/relate_smoke.sh
# -----------------------------------------------------------------------------
# Functional smoke test for the RELATE_MATRIX oracle mode (issue #67).
#
# Drives the standalone oracle binary with the Romanschek line-line vectors in
# oracle/de9im_line_line_vectors.txt and checks that the EXACT line-line DE-9IM
# matrix the oracle emits reproduces each pinned MATRIX string byte-for-byte.
# These are the same matrices certified at the predicate level in
# theories/RelateLineLine.v (`ll_matrix_paper_test*`).
#
#   usage: sh oracle/relate_smoke.sh [path-to-oracle_bin]
#          (defaults to oracle/oracle_bin)
#
# Exit codes: 0 -- every vector reproduced; 1 -- a mismatch; 2 -- setup error.
# =============================================================================
set -eu

ROOT="$(CDPATH= cd -- "$(dirname "$0")/.." && pwd)"
BIN="${1:-$ROOT/oracle/oracle_bin}"
VEC="$ROOT/oracle/de9im_line_line_vectors.txt"

if [ ! -x "$BIN" ]; then
  echo "relate_smoke: oracle binary not found/executable: $BIN" >&2
  echo "  build it with: make -f Makefile.gen && make -C oracle" >&2
  exit 2
fi
if [ ! -r "$VEC" ]; then
  echo "relate_smoke: cannot read vectors: $VEC" >&2
  exit 2
fi

# LINESTRING(x0 y0, x1 y1) -> "x0 y0 x1 y1"
wkt_coords() {
  echo "$1" | sed -e 's/^.*LINESTRING(//' -e 's/).*$//' -e 's/,/ /g'
}

fail=0
total=0
T=""
A=""
B=""
M=""

check_stanza() {
  [ -n "$T" ] && [ -n "$A" ] && [ -n "$B" ] && [ -n "$M" ] || return 0
  # shellcheck disable=SC2046
  set -- $(wkt_coords "$A"); ax0=$1; ay0=$2; ax1=$3; ay1=$4
  # shellcheck disable=SC2046
  set -- $(wkt_coords "$B"); bx0=$1; by0=$2; bx1=$3; by1=$4
  got=$(printf 'RELATE_MATRIX\n%s %s\n%s %s\n%s %s\n%s %s\n' \
          "$ax0" "$ay0" "$ax1" "$ay1" "$bx0" "$by0" "$bx1" "$by1" | "$BIN")
  total=$((total + 1))
  if [ "$got" = "$M" ]; then
    echo "  TEST $T: $got  OK"
  else
    echo "  TEST $T: got '$got' expected '$M'  FAIL" >&2
    fail=1
  fi
}

while IFS= read -r line; do
  case "$line" in
    "TEST "*)   check_stanza; T=${line#TEST }; A=""; B=""; M="" ;;
    "WKT_A "*)  A=${line#WKT_A } ;;
    "WKT_B "*)  B=${line#WKT_B } ;;
    "MATRIX "*) M=${line#MATRIX } ;;
  esac
done < "$VEC"
check_stanza  # flush the final stanza

if [ "$fail" -eq 0 ]; then
  echo "relate_smoke: all $total RELATE_MATRIX vectors reproduce their pinned DE-9IM matrix."
else
  echo "relate_smoke: FAILURES above." >&2
fi
exit "$fail"
