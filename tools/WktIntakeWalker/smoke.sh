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
check "DECLINE ID_GeodesicString" "GEODESICSTRING (0 0, 1 0)"
check "DECLINE ID_SpiralCurve" "SPIRALCURVE EMPTY"
check "BAG hens=0,1 pts=0 0;1 0 chickens=0-1:MkClothoid" "CLOTHOID (0, 0.005, 80)"
check "BAG hens=0,1 pts=0 0;1 0 chickens=0-1:MkClothoid" \
  "CLOTHOID (REFERENCELOCATION AFFINEPLACEMENT (LOCATION (0 0), REFERENCEDIRECTIONS (VECTOR (1 0), VECTOR (0 1))), SCALEFACTOR 100, STARTDISTANCE 0, ENDDISTANCE 50)"
check "BAG hens=0,1,2,3,4,5 pts=0 0;100 0;0 0;1 0;0 0;1 0 chickens=0-1:MkChord,2-3:MkClothoid,4-5:MkClothoid" \
  "COMPOUNDCURVE ((0 0, 100 0), CLOTHOID (0, 0.005, 80), CLOTHOID (REFERENCELOCATION AFFINEPLACEMENT EMPTY, SCALEFACTOR 100, STARTDISTANCE 0, ENDDISTANCE 50))"

if [ "$fail" -ne 0 ]; then
  echo "intake walker smoke FAILED"
  exit 1
fi
echo "intake walker smoke OK"
