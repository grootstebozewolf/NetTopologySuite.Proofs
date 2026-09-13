#!/usr/bin/env bash
# Thin smoke: ANTLR visitor → bag | named Decline. Mirrors IntakeWalker.v.
# Not an oracle keyword (ADR-0006). Engines later test the bag, not the string.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
JAR="${ANTLR_JAR:-$ROOT/.antlr/antlr-4.13.2-complete.jar}"
OUT="$ROOT/.build"
bash "$ROOT/generate.sh"
mkdir -p "$OUT"
find "$ROOT/java" -name '*.java' > "$OUT/sources.list"
javac -cp "$JAR" -d "$OUT" @"$OUT/sources.list"

run() {
  java -cp "$OUT:$JAR" org.nts.proofs.intake.Main "$@"
}

fail=0
check() {
  local want="$1"; shift
  local got
  got="$(run "$@" || true)"
  if [ "$got" != "$want" ]; then
    echo "FAIL expected: $want"
    echo "         got: $got"
    fail=1
  else
    echo "OK $want"
  fi
}

check "BAG hens=0 pts=0 0 chickens=" "POINT (0 0)"
check "BAG hens=0,1 pts=0 0;2 0 chickens=0-1:MkChord" "LINESTRING (0 0, 2 0)"
check "BAG hens=0,1,2 pts=0 0;2 0;0 0 chickens=0-1:MkChord,1-2:MkChord" \
  "LINESTRING (0 0, 2 0, 0 0)"
check "BAG hens=0,1 pts=5 0;0 5 chickens=0-1:MkCirc:quarter" \
  "CIRCULARSTRING (5 0, 3 4, 0 5)"
check "BAG hens=0,1 pts=5 0;5 0 chickens=0-1:MkCirc:full" \
  "CIRCULARSTRING (5 0, 0 5, 5 0)"
check "BAG hens=0,1 pts=5 0;-5 0 chickens=0-1:MkCirc:full" \
  "CIRCLE (5 0, 0 5, -5 0)"
check "BAG hens=0,1,2,3 pts=0 0;5 0;5 0;0 5 chickens=0-1:MkChord,2-3:MkCirc:quarter" \
  "COMPOUNDCURVE ((0 0, 5 0), CIRCULARSTRING (5 0, 3 4, 0 5))"
check "BAG hens=0,1 pts=0 0;3 1 chickens=0-1:MkCirc" \
  "CIRCULARSTRING (0 0, 2 0, 3 1)"
check "BAG hens=0,1 pts=0 0;3 1 chickens=0-1:MkCirc" \
  "CIRCLE (0 0, 2 0, 3 1)"
check "BAG hens=0,1,2 pts=0 0;2 0;4 0 chickens=0-1:MkCirc,1-2:MkCirc" \
  "CIRCULARSTRING (0 0, 1 1, 2 0, 3 1, 4 0)"
check "DECLINE ID_Collinear" "CIRCULARSTRING (0 0, 1 0, 2 0)"
check "DECLINE ID_DuplicateControl" "CIRCULARSTRING (0 0, 0 0, 1 1)"
check "DECLINE ID_BadPointCount" "CIRCULARSTRING (0 0, 1 0)"
check "DECLINE ID_Empty" "CIRCULARSTRING EMPTY"
check "BAG hens=0,1 pts=0 0;2 0 chickens=0-1:MkChord" "GEODESICSTRING (0 0, 2 0)"
check "DECLINE ID_Empty" "GEODESICSTRING EMPTY"
check "DECLINE ID_BadPointCount" "GEODESICSTRING (0 0)"
check "BAG hens=0,1,2,3 pts=0 0;5 0;5 0;7 0 chickens=0-1:MkChord,2-3:MkChord" \
  "COMPOUNDCURVE ((0 0, 5 0), GEODESICSTRING (5 0, 7 0))"

# Famous Science/arXiv 1804.07389 fixtures (claimId 0007-famous-geodesicstring).
# Bag-string of GEODESICSTRING equals LINESTRING on the same two points.
# Not an Earth-length / ETOPO1 / ellipsoid / WKB-13 claim.
check_same_ls_bag() {
  local label="$1" wkt_g="$2" wkt_ls="$3"
  local got_g got_ls
  got_g="$(run "$wkt_g" || true)"
  got_ls="$(run "$wkt_ls" || true)"
  if [ "$got_g" != "$got_ls" ]; then
    echo "FAIL $label bags differ"
    echo "  GEODESICSTRING: $got_g"
    echo "  LINESTRING:     $got_ls"
    fail=1
  elif [[ "$got_g" != BAG*"chickens=0-1:MkChord" ]]; then
    echo "FAIL $label expected BAG ... chickens=0-1:MkChord"
    echo "         got: $got_g"
    fail=1
  else
    echo "OK $label $got_g"
  fi
}
check "BAG hens=0,1 pts=66.6666666667 25.2833333333;162.2333333333 58.6166666667 chickens=0-1:MkChord" \
  "GEODESICSTRING (66.6666666667 25.2833333333, 162.2333333333 58.6166666667)"
check "BAG hens=0,1 pts=118.6333333333 24.55;-8.9166666667 37.0333333333 chickens=0-1:MkChord" \
  "GEODESICSTRING (118.6333333333 24.55, -8.9166666667 37.0333333333)"
check_same_ls_bag "famous-water" \
  "GEODESICSTRING (66.6666666667 25.2833333333, 162.2333333333 58.6166666667)" \
  "LINESTRING (66.6666666667 25.2833333333, 162.2333333333 58.6166666667)"
check_same_ls_bag "famous-land" \
  "GEODESICSTRING (118.6333333333 24.55, -8.9166666667 37.0333333333)" \
  "LINESTRING (118.6333333333 24.55, -8.9166666667 37.0333333333)"

check "DECLINE ID_SpiralCurve" "SPIRALCURVE EMPTY"
check "BAG hens=0,1 pts=0 0;80 5.333333333333333 chickens=0-1:MkClothoid" "CLOTHOID (0, 0.005, 80)"
check "BAG hens=0,1 pts=0 0;80 5.333333333333333 chickens=0-1:MkClothoid" \
  "CLOTHOID (REFERENCELOCATION AFFINEPLACEMENT (LOCATION (0 0), REFERENCEDIRECTIONS (VECTOR (1 0), VECTOR (0 1))), SCALEFACTOR 100, STARTDISTANCE 0, ENDDISTANCE 50)"
check "BAG hens=0,1,2,3,4,5 pts=0 0;100 0;0 0;80 5.333333333333333;0 0;80 5.333333333333333 chickens=0-1:MkChord,2-3:MkClothoid,4-5:MkClothoid" \
  "COMPOUNDCURVE ((0 0, 100 0), CLOTHOID (0, 0.005, 80), CLOTHOID (REFERENCELOCATION AFFINEPLACEMENT EMPTY, SCALEFACTOR 100, STARTDISTANCE 0, ENDDISTANCE 50))"

if [ "$fail" -ne 0 ]; then
  echo "intake walker smoke FAILED"
  exit 1
fi
echo "intake walker smoke OK"
