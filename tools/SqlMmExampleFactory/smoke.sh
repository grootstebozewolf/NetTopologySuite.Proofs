#!/usr/bin/env bash
# Factory smoke: bag → WKT / WKB hex, then intake parse-back.
# Engines still test the bag. No new ADR-0006 oracle keyword.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$ROOT/../.." && pwd)"
INTAKE="$REPO/tools/WktIntakeWalker"
LIB="$ROOT/.lib"
OUT="$ROOT/.build"
ST4_VER="${ST4_VER:-4.3.4}"
A3_VER="${ANTLR3_RUNTIME_VER:-3.5.3}"
CP="$LIB/ST4-${ST4_VER}.jar:$LIB/antlr-runtime-${A3_VER}.jar"

find_pwsh() {
  if command -v pwsh >/dev/null 2>&1; then command -v pwsh; return; fi
  for c in "$HOME/.local/pwsh/pwsh" /usr/bin/pwsh; do
    if [ -x "$c" ]; then echo "$c"; return; fi
  done
  echo "pwsh not found (needed for tools/WktIntakeWalker/generate.ps1)" >&2
  exit 1
}

find_dotnet() {
  if command -v dotnet >/dev/null 2>&1; then command -v dotnet; return; fi
  for c in "$HOME/.dotnet/dotnet" /usr/share/dotnet/dotnet; do
    if [ -x "$c" ]; then
      export DOTNET_ROOT="$(dirname "$c")"
      export PATH="$DOTNET_ROOT:$PATH"
      echo "$c"
      return
    fi
  done
  echo "dotnet not found (needed for C# WktIntakeWalker)" >&2
  exit 1
}

PWSH="$(find_pwsh)"
DOTNET="$(find_dotnet)"

bash "$ROOT/generate.sh"
mkdir -p "$OUT"
find "$ROOT/java" -name '*.java' > "$OUT/sources.list"
javac -cp "$CP" -d "$OUT" @"$OUT/sources.list"

# Intake walker for μ parse-back (C# house style; pinned grammar unchanged).
"$PWSH" -NoProfile -File "$INTAKE/generate.ps1"
"$DOTNET" build "$INTAKE/WktIntakeWalker.csproj" --nologo
INTAKE_DLL="$INTAKE/bin/Debug/net10.0/WktIntakeWalker.dll"

export SQLMM_FACTORY_TEMPLATES="$ROOT/templates"

factory() {
  java -cp "$OUT:$CP" org.nts.proofs.factory.Main "$1"
}

field() {
  local key="$1"
  sed -n "s/^${key}=//p" | head -n 1
}

intake() {
  "$DOTNET" "$INTAKE_DLL" "$@"
}

fail=0
check_eq() {
  local label="$1" want="$2" got="$3"
  if [ "$got" != "$want" ]; then
    echo "FAIL $label"
    echo "  expected: $want"
    echo "       got: $got"
    fail=1
  else
    echo "OK $label"
  fi
}

# --- locked LINESTRING / chord bag → WKT + μ bag equals input ---
ls_out="$(factory linestring-02)"
ls_wkt="$(printf '%s\n' "$ls_out" | field WKT)"
ls_bag="$(printf '%s\n' "$ls_out" | field BAG)"
want_ls_bag="BAG hens=0,1 pts=0 0;2 0 chickens=0-1:MkChord"
check_eq "linestring-02 WKT" "LINESTRING (0 0, 2 0)" "$ls_wkt"
check_eq "linestring-02 factory bag" "$want_ls_bag" "$ls_bag"
got_intake="$(intake "$ls_wkt" || true)"
check_eq "linestring-02 intake μ bag" "$want_ls_bag" "$got_intake"

# geodesic bags MkChord; emit LINESTRING (τ=TagLineString), not GEODESICSTRING / WKB 13
geo_out="$(factory geodesic-as-ls)"
geo_wkt="$(printf '%s\n' "$geo_out" | field WKT)"
geo_tau="$(printf '%s\n' "$geo_out" | field TAU)"
check_eq "geodesic-as-ls WKT is LINESTRING" "LINESTRING (0 0, 2 0)" "$geo_wkt"
check_eq "geodesic-as-ls τ" "TagLineString" "$geo_tau"
check_eq "geodesic-as-ls intake μ bag" "$want_ls_bag" "$(intake "$geo_wkt" || true)"

# --- WKB hex stable NDR + XDR (Point, LineString, CircularString, CompoundCurve 9) ---
# Locked rows also live under oracle/fixtures/sqlmm/shelf-a/ when minted.
check_hex() {
  local id="$1" endian="$2" file="$3"
  local got
  got="$(factory "$id" | field "WKB-${endian}")"
  local want
  want="$(tr -d ' \n' < "$file" | tr 'A-F' 'a-f')"
  check_eq "$id WKB-${endian}" "$want" "$got"
}

FIX="$REPO/oracle/fixtures/sqlmm/shelf-a"
check_hex point-00 NDR "$FIX/point-00.wkb-ndr.hex"
check_hex point-00 XDR "$FIX/point-00.wkb-xdr.hex"
check_hex linestring-02 NDR "$FIX/linestring-02.wkb-ndr.hex"
check_hex linestring-02 XDR "$FIX/linestring-02.wkb-xdr.hex"
check_hex circularstring-quarter NDR "$FIX/circularstring-quarter.wkb-ndr.hex"
check_hex circularstring-quarter XDR "$FIX/circularstring-quarter.wkb-xdr.hex"
check_hex compound-ls-cs NDR "$FIX/compound-ls-cs.wkb-ndr.hex"
check_hex compound-ls-cs XDR "$FIX/compound-ls-cs.wkb-xdr.hex"

# EMPTY LINESTRING: grammar accept (intake Decline) + stable WKT + WKB count=0
empty_out="$(factory linestring-empty)"
empty_wkt="$(printf '%s\n' "$empty_out" | field WKT)"
check_eq "linestring-empty WKT" "LINESTRING EMPTY" "$empty_wkt"
check_eq "linestring-empty intake" "DECLINE ID_Empty" "$(intake "$empty_wkt" || true)"
check_eq "linestring-empty WKB-NDR" "010200000000000000" "$(printf '%s\n' "$empty_out" | field WKB-NDR)"
check_eq "linestring-empty WKB-XDR" "000000000200000000" "$(printf '%s\n' "$empty_out" | field WKB-XDR)"

# POINT / CIRCULARSTRING / CIRCLE / COMPOUND / CLOTHOID WKT parse-back
check_round() {
  local id="$1" want_wkt="$2" want_bag="$3"
  local out wkt bag
  out="$(factory "$id")"
  wkt="$(printf '%s\n' "$out" | field WKT)"
  bag="$(printf '%s\n' "$out" | field BAG)"
  check_eq "$id WKT" "$want_wkt" "$wkt"
  check_eq "$id factory bag" "$want_bag" "$bag"
  check_eq "$id intake μ bag" "$want_bag" "$(intake "$wkt" || true)"
}

check_round point-00 "POINT (0 0)" "BAG hens=0 pts=0 0 chickens="
check_round circularstring-quarter "CIRCULARSTRING (5 0, 3 4, 0 5)" \
  "BAG hens=0,1 pts=5 0;0 5 chickens=0-1:MkCirc:quarter"
check_round circularstring-full "CIRCULARSTRING (5 0, 0 5, 5 0)" \
  "BAG hens=0,1 pts=5 0;0 5 chickens=0-1:MkCirc:half,1-0:MkCirc:half"
strict_out="$(factory circularstring-full-strict)"
strict_wkt="$(printf '%s\n' "$strict_out" | field WKT)"
strict_bag="$(printf '%s\n' "$strict_out" | field BAG)"
check_eq "circularstring-full-strict WKT" "CIRCULARSTRING (5 0, 0 5, 5 0)" "$strict_wkt"
check_eq "circularstring-full-strict factory bag" "DECLINE ID_CsClosedDegenerate" "$strict_bag"
check_eq "circularstring-full-strict intake" "DECLINE ID_CsClosedDegenerate" \
  "$(intake --strict "$strict_wkt" || true)"
check_round circle-full "CIRCLE (5 0, 0 5, -5 0)" \
  "BAG hens=0,1 pts=5 0;-5 0 chickens=0-1:MkCirc:half,1-0:MkCirc:half"
check_round compound-ls-cs \
  "COMPOUNDCURVE ((0 0, 5 0), CIRCULARSTRING (5 0, 3 4, 0 5))" \
  "BAG hens=0,1,2,3 pts=0 0;5 0;5 0;0 5 chickens=0-1:MkChord,2-3:MkCirc:quarter"

# Clothoid: both surface forms → same locked MkClothoid bag (intake smoke).
cloth_bag="BAG hens=0,1 pts=0 0;80 5.333333333333333 chickens=0-1:MkClothoid"
check_round clothoid-jts "CLOTHOID (0, 0.005, 80)" "$cloth_bag"
check_round clothoid-iso \
  "CLOTHOID (REFERENCELOCATION AFFINEPLACEMENT (LOCATION (0 0), REFERENCEDIRECTIONS (VECTOR (1 0), VECTOR (0 1))), SCALEFACTOR 100, STARTDISTANCE 0, ENDDISTANCE 50)" \
  "$cloth_bag"

# CIRCLE / CLOTHOID WKB is HOLD (κ=none). Not 18 / 22.
circle_ndr="$(factory circle-full | field WKB-NDR)"
case "$circle_ndr" in
  HOLD*) echo "OK circle-full WKB is HOLD (not code 18)" ;;
  *) echo "FAIL circle-full WKB should be HOLD, got: $circle_ndr"; fail=1 ;;
esac
cloth_ndr="$(factory clothoid-jts | field WKB-NDR)"
case "$cloth_ndr" in
  HOLD*) echo "OK clothoid-jts WKB is HOLD (not code 22)" ;;
  *) echo "FAIL clothoid-jts WKB should be HOLD, got: $cloth_ndr"; fail=1 ;;
esac

if [ "$fail" -ne 0 ]; then
  echo "sqlmm example factory smoke FAILED"
  exit 1
fi
echo "sqlmm example factory smoke OK"
echo "note: engines still test the bag; no new ADR-0006 oracle keyword"
