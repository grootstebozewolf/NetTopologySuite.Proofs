#!/usr/bin/env python3
# =============================================================================
# oracle/red_winding_tests.py
# coverage: feat:winding-number geom:polygon,star,triangle
# -----------------------------------------------------------------------------
# Assert-style red tests for the WINDING_NUMBER oracle mode.
# Each test calls oracle_bin and verifies the result or a derived invariant.
# Exit nonzero on any failure.
#
# Backing proof: theories/WindingNumber.v (winding_decides_membership, Qed).
# These tests are the empirical complement of:
#   edge_winding_triple  — each edge ∈ {0, +1, -1}
#   winding_decides_membership — Z.odd(w) = true ↔ point_in_ring (Qed)
# =============================================================================
import math
import os
import subprocess
import sys

BIN = os.environ.get("ORACLE_BIN", "oracle/oracle_bin")
failures = 0


def winding(ring, q):
    n = len(ring)
    lines = ["WINDING_NUMBER", str(n)]
    for (x, y) in ring:
        lines.append(f"{x} {y}")
    lines.append(f"{q[0]} {q[1]}")
    inp = "\n".join(lines) + "\n"
    out = subprocess.run([BIN], input=inp, capture_output=True, text=True).stdout.strip()
    return int(out)


def pip(ring, q):
    n = len(ring)
    segs = [f"C {ring[i][0]} {ring[i][1]} {ring[(i+1)%n][0]} {ring[(i+1)%n][1]}"
            for i in range(n)]
    lines = ["POINT_IN_CURVE_RING", str(n)] + segs + [f"{q[0]} {q[1]}"]
    inp = "\n".join(lines) + "\n"
    return subprocess.run([BIN], input=inp, capture_output=True, text=True).stdout.strip()


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


# ---------------------------------------------------------------------------
# Ring definitions (same as gen_winding_number_tests.py for consistency).
# ---------------------------------------------------------------------------
SQUARE_CCW = [(0, 0), (1, 0), (1, 1), (0, 1)]
SQUARE_CW  = list(reversed(SQUARE_CCW))

TRIANGLE_CCW = [(0, 0), (2, 0), (1, 2)]

HEXAGON = [(math.cos(math.pi/6 + math.pi*k/3),
            math.sin(math.pi/6 + math.pi*k/3)) for k in range(6)]

def pentagram():
    r = 2.0
    vs = [(r * math.sin(2*math.pi*k/5), r * math.cos(2*math.pi*k/5)) for k in range(5)]
    return [vs[0], vs[2], vs[4], vs[1], vs[3]]

STAR = pentagram()

# ---------------------------------------------------------------------------
# Tests
# ---------------------------------------------------------------------------
print("# red_winding_tests: WINDING_NUMBER oracle assertions")
print("# backing: theories/WindingNumber.v (winding_decides_membership, Qed)")
print()

print("## TestWindingNumber_CCW_Square_Interior")
assert_eq("CCW_Square_Interior", winding(SQUARE_CCW, (0.5, 0.5)), 1)

print("## TestWindingNumber_CCW_Square_Exterior")
assert_eq("CCW_Square_Exterior", winding(SQUARE_CCW, (2.0, 0.5)), 0)

print("## TestWindingNumber_CW_Square_Interior")
assert_eq("CW_Square_Interior", winding(SQUARE_CW, (0.5, 0.5)), -1)

print("## TestWindingNumber_CW_Square_Exterior")
assert_eq("CW_Square_Exterior", winding(SQUARE_CW, (2.0, 0.5)), 0)

print("## TestWindingNumber_Triangle_Interior")
assert_eq("Triangle_Interior", winding(TRIANGLE_CCW, (1.0, 0.667)), 1)

print("## TestWindingNumber_Triangle_Exterior")
assert_eq("Triangle_Exterior", winding(TRIANGLE_CCW, (3.0, 0.5)), 0)

# Non-simple: star polygon with CW orientation (inner winding = -2)
print("## TestWindingNumber_Star_DoubleWound")
assert_eq("Star_DoubleWound", winding(STAR, (0.0, 0.3)), -2)

print("## TestWindingNumber_Star_SingleWound")
assert_eq("Star_SingleWound", winding(STAR, (0.0, 1.5)), -1)

print("## TestWindingNumber_Star_Exterior")
assert_eq("Star_Exterior", winding(STAR, (3.0, 0.0)), 0)

print("## TestWindingNumber_Reversal_Parity")
for (rname, ring, q) in [
    ("square",   SQUARE_CCW,   (0.5, 0.5)),
    ("triangle", TRIANGLE_CCW, (1.0, 0.667)),
    ("hexagon",  HEXAGON,      (0.0, 0.0)),
]:
    w_fwd = winding(ring, q)
    w_rev = winding(list(reversed(ring)), q)
    assert_true(f"Reversal_{rname}_negates",
                w_fwd == -w_rev,
                f"fwd={w_fwd} rev={w_rev}")

print("## TestWindingNumber_Parity_Agrees_PIP")
for (rname, ring, q) in [
    ("square-interior",  SQUARE_CCW,   (0.5, 0.5)),
    ("square-exterior",  SQUARE_CCW,   (2.0, 0.5)),
    ("triangle-interior",TRIANGLE_CCW, (1.0, 0.667)),
    ("triangle-exterior",TRIANGLE_CCW, (3.0, 0.5)),
    ("hexagon-centre",   HEXAGON,      (0.0, 0.0)),
    ("hexagon-exterior", HEXAGON,      (2.0, 0.0)),
    ("star-inner",       STAR,         (0.0, 0.3)),
    ("star-outer",       STAR,         (0.0, 1.5)),
    ("star-exterior",    STAR,         (3.0, 0.0)),
]:
    w = winding(ring, q)
    p = pip(ring, q)
    parity_in  = (w % 2 != 0)
    pip_in     = (p == "IN")
    assert_true(f"Parity_PIP_{rname}",
                parity_in == pip_in,
                f"winding={w} pip={p}")

print()
if failures:
    print(f"!! {failures} test(s) FAILED", file=sys.stderr)
    sys.exit(1)
else:
    print(f"All tests passed.")
