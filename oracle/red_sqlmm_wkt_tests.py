#!/usr/bin/env python3
# =============================================================================
# oracle/red_sqlmm_wkt_tests.py
# coverage: feat:sqlmm-wkt geom:clothoid,circle,geodesicstring,nurbscurve,spiralcurve
# -----------------------------------------------------------------------------
# Assert-style red tests for the SQLMM_WKT oracle mode.
# Structural I/O identity only — no length, no CurveSegment growth, no 508-*.
#
# Run (from repo root):
#   make -C oracle sqlmm-wkt-tests
#   ORACLE_BIN=oracle/oracle_bin python3 oracle/red_sqlmm_wkt_tests.py
# Exit status: 0 iff every assertion passes.
#
# Backing notes: ISO/IEC 13249-3 §4.2.1 / §4.2.7–§4.2.12 / §5.1.67 / §5.1.68.
# SPIRALTYPE lexer deviation: docs/iso13249-3-curve-type-bindings-2026-08.md §8.
# =============================================================================
import os
import subprocess
import sys

_HERE = os.path.dirname(os.path.abspath(__file__))
_CANDIDATES = [
    os.environ.get("ORACLE_BIN"),
    os.path.join(_HERE, "oracle_bin"),
    os.path.join(_HERE, "sqlmm_wkt_bin"),
]
BIN = next((p for p in _CANDIDATES if p and os.path.isfile(p) and os.access(p, os.X_OK)), None)
failures = 0


def sqlmm(wkt):
    if BIN is None:
        raise SystemExit("!! no SQLMM_WKT binary (oracle_bin or sqlmm_wkt_bin)")
    inp = f"SQLMM_WKT\n{wkt}\n"
    proc = subprocess.run([BIN], input=inp, capture_output=True, text=True)
    if proc.returncode != 0:
        return f"EXIT {proc.returncode}: {proc.stderr.strip()}"
    return proc.stdout.strip().splitlines()[-1] if proc.stdout.strip() else ""


def assert_eq(name, got, expected):
    global failures
    status = "PASS" if got == expected else "FAIL"
    print(f"  [{status}] {name}: got {got!r} expected {expected!r}")
    if got != expected:
        failures += 1


def assert_true(name, cond, detail=""):
    global failures
    status = "PASS" if cond else "FAIL"
    print(f"  [{status}] {name}{': ' + detail if detail else ''}")
    if not cond:
        failures += 1


print("SQLMM_WKT — §4.2.1 instantiable types")
for typ in ("CLOTHOID", "CIRCLE", "GEODESICSTRING", "NURBSCURVE", "SPIRALCURVE"):
    assert_eq(f"{typ} EMPTY", sqlmm(f"{typ} EMPTY"), f"OK {typ} XY EMPTY")

assert_eq(
    "CIRCLE three points",
    sqlmm("CIRCLE (0 0, 1 0, 0 1)"),
    "OK CIRCLE XY POINTS 3",
)
assert_true("CIRCLE arity 2 refuses", sqlmm("CIRCLE (0 0, 1 0)").startswith("REFUSE"))
assert_eq(
    "CIRCLE Z three points",
    sqlmm("CIRCLE Z (0 0 1, 1 0 1, 0 1 1)"),
    "OK CIRCLE Z POINTS 3",
)
assert_true(
    "CIRCLE Z with XY points refuses",
    sqlmm("CIRCLE Z (0 0, 1 0, 0 1)").startswith("REFUSE"),
)

assert_eq(
    "GEODESICSTRING three points",
    sqlmm("GEODESICSTRING (0 0, 1 1, 2 0)"),
    "OK GEODESICSTRING XY POINTS 3",
)
assert_true(
    "GEODESICSTRING one point refuses",
    sqlmm("GEODESICSTRING (0 0)").startswith("REFUSE"),
)

assert_eq(
    "CLOTHOID keyword form",
    sqlmm(
        "CLOTHOID (AFFINEPLACEMENT (LOCATION (0 0), REFERENCEDIRECTIONS (1 0)), "
        "SCALEFACTOR 1, STARTDISTANCE 0, ENDDISTANCE 2)"
    ),
    "OK CLOTHOID XY SCALEFACTOR 1 STARTDISTANCE 0 ENDDISTANCE 2",
)
assert_true(
    "CLOTHOID missing SCALEFACTOR refuses",
    sqlmm(
        "CLOTHOID (AFFINEPLACEMENT (LOCATION (0 0), REFERENCEDIRECTIONS (1 0)), "
        "STARTDISTANCE 0, ENDDISTANCE 2)"
    ).startswith("REFUSE"),
)

assert_eq(
    "NURBSCURVE single-span",
    sqlmm(
        "NURBSCURVE (DEGREE 2, KNOTS (0, 0, 0, 1, 1, 1), "
        "CONTROLPOINTS ((0 0, 1), (1 1, 1), (2 0, 1)))"
    ),
    "OK NURBSCURVE XY DEGREE 2 CONTROLPOINTS 3 KNOTS 6",
)

print("SQLMM_WKT — SPIRALTYPE initial set and open-set extension")
for name in ("clothoid", "bloss", "biquadratic", "sine", "cosine"):
    assert_eq(
        f"SPIRALTYPE {name} INITIAL",
        sqlmm(f"SPIRALCURVE (SPIRALTYPE {name})"),
        f"OK SPIRALCURVE XY SPIRALTYPE {name} INITIAL",
    )

assert_eq(
    "SPIRALTYPE Wiener Bogen preserves interior space",
    sqlmm("SPIRALCURVE (SPIRALTYPE Wiener Bogen)"),
    "OK SPIRALCURVE XY SPIRALTYPE Wiener Bogen EXTENSION",
)
assert_eq(
    "SPIRALTYPE Wiener Bogen with LENGTH",
    sqlmm("SPIRALCURVE (SPIRALTYPE Wiener Bogen, LENGTH 10)"),
    "OK SPIRALCURVE XY SPIRALTYPE Wiener Bogen EXTENSION LENGTH 10",
)

print("SQLMM_WKT — deviations from the standard")
# A name containing a comma cannot be represented: the lexer ends at the comma.
got = sqlmm("SPIRALCURVE (SPIRALTYPE Wiener, Bogen)")
assert_true(
    "comma in SPIRALTYPE is unrepresentable (does not parse as 'Wiener, Bogen')",
    (not got.startswith("OK ")) or "Wiener, Bogen" not in got,
    got,
)
assert_true(
    "comma in SPIRALTYPE refuses the leftover field",
    got.startswith("REFUSE"),
    got,
)

# A name containing a parenthesis cannot be represented.
got = sqlmm("SPIRALCURVE (SPIRALTYPE foo(bar))")
assert_true(
    "parenthesis in SPIRALTYPE is unrepresentable",
    (not got.startswith("OK ")) or "foo(bar)" not in got,
    got,
)
assert_true(
    "parenthesis in SPIRALTYPE refuses",
    got.startswith("REFUSE"),
    got,
)

assert_eq(
    "empty SPIRALTYPE refuses",
    sqlmm("SPIRALCURVE (SPIRALTYPE )"),
    "REFUSE EMPTY_SPIRALTYPE",
)

assert_eq(
    "lowercase type keyword is CASEFOLD deviation",
    sqlmm("circle (0 0, 1 0, 0 1)"),
    "OK CIRCLE XY POINTS 3 CASEFOLD",
)

assert_eq(
    "tagged LINESTRING in COMPOUNDCURVE is documented deviation",
    sqlmm("COMPOUNDCURVE (LINESTRING (0 0, 1 0), CIRCULARSTRING (1 0, 2 1, 3 0))"),
    "OK COMPOUNDCURVE XY MEMBERS 2 [LINESTRING,CIRCULARSTRING] DEVIATION TAGGED_LINESTRING",
)

print("SQLMM_WKT — named vs unknown; compound members")
assert_eq("unknown token stays UNKNOWN", sqlmm("FOOBAR (0 0)"), "UNKNOWN FOOBAR")
assert_eq(
    "ELLIPTICALCURVE is instantiable §4.2.9, not UNKNOWN",
    sqlmm("ELLIPTICALCURVE EMPTY"),
    "OK ELLIPTICALCURVE XY EMPTY",
)
assert_eq(
    "COMPOUNDCURVE may carry CIRCLE + bare linestring",
    sqlmm("COMPOUNDCURVE (CIRCLE (0 0, 1 0, 0 1), (1 0, 2 0))"),
    "OK COMPOUNDCURVE XY MEMBERS 2 [CIRCLE,LINESTRING_BARE]",
)
assert_eq(
    "COMPOUNDCURVE may carry CLOTHOID + GEODESICSTRING",
    sqlmm("COMPOUNDCURVE (CLOTHOID EMPTY, GEODESICSTRING (0 0, 1 0))"),
    "OK COMPOUNDCURVE XY MEMBERS 2 [CLOTHOID,GEODESICSTRING]",
)

print()
if failures:
    print(f"!! {failures} test(s) FAILED", file=sys.stderr)
    sys.exit(1)
print("SQLMM_WKT red tests: all passed")
