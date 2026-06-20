#!/usr/bin/env python3
# =============================================================================
# oracle/test_cp_boundary_simplify.py
# -----------------------------------------------------------------------------
# Oracle-backed test for the CurvePolygon exterior-ring boundary (F-CP Option A,
# issue #849): builds sample CurvePolygons via oracle/curve_polygon.py and
# asserts the CP_BOUNDARY_SIMPLIFY output -- V (simplified ring) + O (per-corner
# orientation) lines, with the INTSAFE / APPROX certificate tagging.
#
#   INTSAFE corners (integer coords, |coord| <= 2^25) are certified by
#     b64_orient_sign_filtered_sound_small_int (Orient_b64_exact.v:990);
#   APPROX corners (irrational densified arc vertices) are interface-only.
#
# Run from repo root (after `make -C oracle`):
#   python3 oracle/test_cp_boundary_simplify.py
# Exit status: nonzero iff any assertion fails.
# =============================================================================
import sys

from curve_polygon import CurvePolygon  # noqa: E402  (run from oracle/ or repo root)

failures = 0


def check(cond, msg):
    global failures
    status = "ok" if cond else "FAIL"
    print(f"  [{status}] {msg}")
    if not cond:
        failures += 1


# --- Sample A: integer square shell with a collinear midpoint on the bottom
# edge.  GetExteriorRing must drop the collinear point (greedy perp simplify);
# the 4 survivors are INTSAFE and CCW, so every corner is POS INTSAFE -- the
# CERTIFIED path.  Coordinates are exact powers/multiples -> exact hex. ------
square = CurvePolygon([
    ("C", (0, 0), (500, 0)),
    ("C", (500, 0), (1000, 0)),       # (500,0) is collinear -> dropped
    ("C", (1000, 0), (1000, 1000)),
    ("C", (1000, 1000), (0, 1000)),
    ("C", (0, 1000), (0, 0)),
])
verts, corners = square.run_boundary(eps=0.5, n=1)
print("Sample A -- integer square, collinear midpoint (certified path):")
check(len(verts) == 4, "exterior ring simplifies to 4 vertices (collinear midpoint dropped)")
check(
    verts == [(0.0, 0.0), (1000.0, 0.0), (1000.0, 1000.0), (0.0, 1000.0)],
    "V lines match the expected square corners",
)
check(corners == [("POS", "INTSAFE")] * 4, "O lines: 4x POS INTSAFE (certified)")

# --- Sample B: a CurvePolygon with a true quarter-circle arc.  The densified
# arc vertices are irrational, so every corner is tagged APPROX (interface-only,
# NOT certified by the int-safe theorem).  We assert the TAG, not the exact
# irrational coordinates. --------------------------------------------------
arc_poly = CurvePolygon([
    ("A", (1, 0), (0.7071067811865476, 0.7071067811865476), (0, 1)),
    ("C", (0, 1), (1, 0)),
])
vertsB, cornersB = arc_poly.run_boundary(eps=1e-9, n=4)
print("Sample B -- quarter-circle arc (interface path):")
check(len(vertsB) >= 3, "arc densifies to a ring of >= 3 vertices")
check(len(cornersB) == len(vertsB), "one O line per vertex")
check(all(flag == "APPROX" for _, flag in cornersB),
      "every arc corner is tagged APPROX (irrational vertices, uncertified)")
check(all(sign in ("POS", "NEG", "ZERO", "UNCERTAIN", "NAN")
          for sign, _ in cornersB), "arc corner signs are valid orient_sign_robust values")

if failures:
    sys.stderr.write(f"test_cp_boundary_simplify: {failures} assertion(s) failed\n")
    sys.exit(1)
print("test_cp_boundary_simplify: all assertions passed.")
