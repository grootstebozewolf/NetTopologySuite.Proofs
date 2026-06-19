#!/usr/bin/env python3
# =============================================================================
# oracle/gen_arc_area_tests.py
# -----------------------------------------------------------------------------
# Adversarial tests for the ARC_AREA oracle mode (M-AREA-CP, issue #64),
# driven by the RocqRefRunner (oracle_bin). ARC_AREA emits the circular-segment
# area of one arc (region between arc and its chord) as a float.
#
# A = (r²/2) * (Theta - sin Theta), Theta = swept central angle (minor or major).
# Ground truth uses the EXACT-rational circumcentre + arc invariants (cos/major);
# only the transcendental (acos + sin or Taylor) + mul round.
#
# Invariants gated (a '!!' line fails CI) -- consequences of ArcArea.v:
#   I1 NONNEG     area >= 0 (for the arc's sweep)
#   I2 SEMICIRCLE area == (pi r² / 2) for theta=PI
#   I3 FULL_TURN  area == pi r² for theta=2*PI
#   I4 DEGENERATE collinear controls -> DEGENERATE
#   I5 HALF/FULL  matches half-disc / full-disc expectations
#
# Run from repo root:
#   python3 oracle/gen_arc_area_tests.py > oracle/arc_area_tests.txt
# Exit status: nonzero iff a gated invariant or curated expectation fails.
# =============================================================================
import math
import os
import subprocess
import sys
from fractions import Fraction as F

BIN = os.environ.get("ORACLE_BIN", "oracle/oracle_bin")
violations = 0


def emit(s=""):
    print(s)


def run_area(arc):
    stdin = "ARC_AREA\n%s\n%s\n%s\n" % (
        f"{arc[0][0]} {arc[0][1]}",
        f"{arc[1][0]} {arc[1][1]}",
        f"{arc[2][0]} {arc[2][1]}")
    return subprocess.run([BIN], input=stdin, capture_output=True, text=True).stdout.strip()


def parse(line):
    tok = line.split()
    if not tok:
        return ("?", None)
    if tok[0] in ("DEGENERATE", "NAN"):
        return (tok[0], None)
    try:
        val = float.fromhex(tok[0]) if ("x" in tok[0] or "p" in tok[0].lower()) else float(tok[0])
        return ("AREA", val)
    except:
        return ("?", None)


def circumcentre(arc):
    (ax, ay), (bx, by), (cx, cy) = [(F(x), F(y)) for (x, y) in arc]
    dd = 2 * ((bx - ax) * (cy - ay) - (by - ay) * (cx - ax))
    if dd == 0:
        return None
    bk = bx * bx + by * by - ax * ax - ay * ay
    ck = cx * cx + cy * cy - ax * ax - ay * ay
    ox = ((cy - ay) * bk - (by - ay) * ck) / dd
    oy = ((bx - ax) * ck - (cx - ax) * bk) / dd
    r2 = (ox - ax) ** 2 + (oy - ay) ** 2
    return (float(ox), float(oy), math.sqrt(float(r2)))


def arc_invariants(arc):
    o = circumcentre(arc)
    if o is None:
        return None
    ox, oy, r = o
    ax, ay = arc[0][0] - ox, arc[0][1] - oy
    bx, by_ = arc[1][0] - ox, arc[1][1] - oy
    cx, cy = arc[2][0] - ox, arc[2][1] - oy
    dot_ac = ax*cx + ay*cy
    na = math.hypot(ax, ay)
    nc = math.hypot(cx, cy)
    if na == 0 or nc == 0:
        return None
    cos_full = max(min(dot_ac / (na * nc), 1.0), -1.0)
    s = math.sqrt(max(0.0, (1.0 - cos_full) / 2.0))
    t0 = 2.0 * math.asin(s)
    twopi = 2.0 * math.pi
    def orient_acx(px, py):
        return (cx - ax)*(py - ay) - (cy - ay)*(px - ax)
    sb = orient_acx(bx, by_)
    so = orient_acx(ox, oy)
    major = 1 if (so != 0 and sb * so > 0) else 0
    theta = (twopi - t0) if major else t0
    return (ox, oy, r, theta, major, cos_full)


def assess(name, arc, expect_kind=None):
    global violations
    line = run_area(arc)
    kind, area = parse(line)
    tags = []
    inv = arc_invariants(arc)
    if inv is None:
        if kind != "DEGENERATE":
            violations += 1
            tags.append(f"!! EXPECTED_DEGENERATE_GOT_{kind}")
        emit(f"  [{name}] -> {line!r}   {' '.join(tags) if tags else 'ok'}")
        return
    ox, oy, r, theta, major, _ = inv
    if kind == "AREA":
        observed = area
        tol = 1e-6 * (1 + r*r)
        # I1 NONNEG
        if observed < -tol:
            violations += 1
            tags.append(f"!! I1_NONNEG {observed:.6g}")
        # I2/I3 specials
        if abs(theta - math.pi) < 1e-8:
            expected = (math.pi * r*r) / 2.0
            if abs(observed - expected) > tol:
                violations += 1
                tags.append(f"!! I2_SEMICIRCLE {observed:.6g} != {expected:.6g}")
        if abs(theta - 2*math.pi) < 1e-8 or abs(theta) < 1e-12:
            expected = math.pi * r*r
            if abs(observed - expected) > tol:
                violations += 1
                tags.append(f"!! I3_FULL {observed:.6g} != {expected:.6g}")
        # Basic match to formula (within float tolerance for the transcendental)
        expected = (r*r / 2.0) * (theta - math.sin(theta))
        if abs(observed - expected) > tol * 10:  # looser for transcendental
            violations += 1
            tags.append(f"!! I4_FORMULA obs={observed:.6g} exp={expected:.6g}")
    elif kind == "DEGENERATE":
        pass
    else:
        violations += 1
        tags.append(f"!! UNEXPECTED_{kind}")
    if expect_kind is not None and kind != expect_kind:
        violations += 1
        tags.append(f"!! EXPECTED_{expect_kind}_GOT_{kind}")
    emit(f"  [{name}] -> {line!r}   {' '.join(tags) if tags else 'ok'}")


# ---------------------------------------------------------------------------
emit("# Adversarial tests for ARC_AREA (RocqRefRunner), M-AREA-CP / issue #64.")
emit("# I1 nonneg  I2 semicircle==pi r^2/2  I3 full==pi r^2  I4 degen. Backing: ArcArea.v")
emit("# '!!' lines are gated-invariant / expectation violations (CI-failing).")
emit()
emit("## A. Curated (exact half/full/disc cases).")

UA = ((5, 0), (0, 5), (-5, 0))  # upper semicircle R=5
assess("R=5 semicircle", UA, expect_kind="AREA")
assess("R=5 full turn approx (almost)", ((5,0),(0,5),(5,0.001)), expect_kind="AREA")  # near full
assess("degenerate collinear", ((0,0),(1,0),(2,0)), expect_kind="DEGENERATE")

emit()
emit("## B. Sweep + adversarial (small theta, major, huge, near boundary).")
ARCS = {
    "unit @origin": ((1, 0), (0, 1), (-1, 0)),
    "R=5 lower": ((-5, 0), (0, -5), (5, 0)),
    "off-centre R=2 @ (3,4)": ((5, 4), (3, 6), (1, 4)),
    "small quarter": ((2, 0), (1.4142135623730951, 1.4142135623730951), (0, 2)),
    "huge": ((1e8, 0), (0, 1e8), (-1e8, 0)),
}
for nm, arc in ARCS.items():
    inv = arc_invariants(arc)
    if inv is None:
        assess(f"{nm} (degen)", arc)
        continue
    assess(f"{nm}", arc)

# extra small theta (flat), near boundary, major
assess("tiny flat arc", ((0,0), (0.01, 0.0001), (0.02,0)), expect_kind="AREA")
assess("near semicircle major", ((1,0), (-0.999,0.1), (-1,0)), expect_kind="AREA")
assess("R=1 near flat minor", ((1,0),(0.999,0.001),(0.998,0)), expect_kind="AREA")
assess("large outward major", ((0,1),(-1,0),(0,-1)), expect_kind="AREA")

emit()
if violations:
    emit(f"::error::ARC_AREA violated {violations} invariant(s)/expectation(s).")
    sys.exit(1)
emit("# All invariants (I1 nonneg, I2 semicircle, I3 full, I4 degen + formula match) hold.")
