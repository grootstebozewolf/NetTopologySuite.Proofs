#!/usr/bin/env python3
# =============================================================================
# oracle/gen_arc_offset_tests.py
# -----------------------------------------------------------------------------
# Adversarial tests for the ARC_OFFSET_XY oracle mode (OFF / BUF-1 / BUF-NEG,
# JTS #1195 §7), driven by the RocqRefRunner (oracle_bin).  ARC_OFFSET_XY emits
# the offset (buffer boundary) of a circular arc at signed distance d: the
# concentric arc of radius r+d.  Ground truth is the EXACT-rational circumcentre
# (fractions.Fraction); only the radius sqrt rounds.
#
# Invariants gated (a '!!' line fails CI) -- each is a coordinate-level
# consequence of the merged proof backing:
#   I1  RADIAL-DIST   each emitted control is at distance |d| from its input
#                     control (ArcOffsetThreePoint.radial_offset_dist).
#   I2  SAME-CIRCLE   each emitted control is at distance |r+d| from the (exact)
#                     circumcentre O (arc_offset_preserves_arc: same centre,
#                     radius r+d).
#   I3  RADIAL-RAY    O, P, P' are collinear with P' on the OUTWARD ray
#                     (homothety O ((r+d)/r) -- positive scale).
#   I4  EMPTY         output is EMPTY iff r + d <= 0 (the parallel-curve property
#                     fails past the centre; inner_offset_past_center_not_at_distance).
#   I5  IDENTITY      d = 0 reproduces the input controls.
#
# Full slice adds coverage for: signed d (pos/neg), EMPTY collapse boundary,
# 3pt preservation on extremes, huge coords, major sweeps, tiny arcs, near-singularity.
#
# Run from repo root:
#   python3 oracle/gen_arc_offset_tests.py > oracle/arc_offset_tests.txt
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


def run(arc, d):
    stdin = "ARC_OFFSET_XY\n%s\n%s\n%s\n%s\n" % (
        f"{arc[0][0]} {arc[0][1]}", f"{arc[1][0]} {arc[1][1]}",
        f"{arc[2][0]} {arc[2][1]}", str(d))
    return subprocess.run([BIN], input=stdin, capture_output=True, text=True).stdout.strip()


def parse(line):
    tok = line.split()
    if not tok:
        return ("EMPTY_OUT", None)
    if tok[0] in ("EMPTY", "DEGENERATE", "NAN"):
        return (tok[0], None)
    vals = [float.fromhex(t) if ("x" in t or "p" in t.lower()) else float(t) for t in tok]
    if len(vals) != 6:
        return ("?", None)
    return ("XY", [(vals[0], vals[1]), (vals[2], vals[3]), (vals[4], vals[5])])


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


def assess(name, arc, d, expect=None):
    global violations
    line = run(arc, d)
    kind, pts = parse(line)
    tags = []
    o = circumcentre(arc)
    if o is None:
        # collinear controls -> must be DEGENERATE
        if kind != "DEGENERATE":
            violations += 1
            tags.append(f"!! EXPECTED_DEGENERATE_GOT_{kind}")
        emit(f"  [{name}] -> {line!r}   {' '.join(tags) if tags else 'ok'}")
        return
    ox, oy, r = o
    # I4 EMPTY iff r + d <= 0
    if r + d < -1e-9 * (1 + r):
        if kind != "EMPTY":
            violations += 1
            tags.append(f"!! I4_EXPECTED_EMPTY_GOT_{kind} (r+d={r+d:.4g})")
    elif r + d > 1e-9 * (1 + r):
        if kind != "XY":
            violations += 1
            tags.append(f"!! I4_EXPECTED_XY_GOT_{kind} (r+d={r+d:.4g})")
    if kind == "XY":
        tol = 1e-6 * (1 + r + abs(d))
        for i, (px, py) in enumerate(arc):
            qx, qy = pts[i]
            # I1 radial distance |d|
            if abs(math.hypot(qx - px, qy - py) - abs(d)) > tol:
                violations += 1
                tags.append(f"!! I1_DIST_ctrl{i}")
            # I2 distance |r+d| from centre
            if abs(math.hypot(qx - ox, qy - oy) - abs(r + d)) > tol:
                violations += 1
                tags.append(f"!! I2_RADIUS_ctrl{i}")
            # I3 radial ray (O,P,P' collinear; P' = O + k(P-O), k=(r+d)/r > 0)
            cross = (px - ox) * (qy - oy) - (py - oy) * (qx - ox)
            if abs(cross) > tol * (1 + r):
                violations += 1
                tags.append(f"!! I3_NOT_RADIAL_ctrl{i}")
            k = (r + d) / r
            if abs((qx - ox) - k * (px - ox)) > tol or abs((qy - oy) - k * (py - oy)) > tol:
                violations += 1
                tags.append(f"!! I3_SCALE_ctrl{i}")
        # I5 identity at d = 0
        if d == 0:
            for i, (px, py) in enumerate(arc):
                if math.hypot(pts[i][0] - px, pts[i][1] - py) > tol:
                    violations += 1
                    tags.append(f"!! I5_IDENTITY_ctrl{i}")
    if expect is not None and kind != expect:
        violations += 1
        tags.append(f"!! EXPECTED_{expect}_GOT_{kind}")
    emit(f"  [{name}] -> {line!r}   {' '.join(tags) if tags else 'ok'}")


# ---------------------------------------------------------------------------
emit("# Adversarial tests for ARC_OFFSET_XY (RocqRefRunner), OFF/BUF / JTS #1195 §7.")
emit("# I1 radial-dist |d|  I2 distance |r+d| from centre  I3 radial ray (homothety)")
emit("# I4 EMPTY iff r+d<=0  I5 identity at d=0.  Backing: ArcOffsetThreePoint")
emit("# arc_offset_preserves_arc / radial_offset_dist_exact + the EMPTY witness.")
emit("# Full: signed/collapse/3pt/EMPTY/huge/major/tiny. '!!' lines fail CI.")
emit()
emit("## A. Curated (offset radii hand-verified).")

UA = ((5, 0), (0, 5), (-5, 0))    # upper semicircle R=5
assess("R=5 arc, d=+2 (radius 7)", UA, 2, expect="XY")
assess("R=5 arc, d=-2 (radius 3)", UA, -2, expect="XY")
assess("R=5 arc, d=0 (identity)", UA, 0, expect="XY")
assess("R=5 arc, d=-5 (r+d=0, EMPTY)", UA, -5, expect="EMPTY")
assess("R=5 arc, d=-6 (r+d<0, EMPTY)", UA, -6, expect="EMPTY")
assess("R=5 arc, large outward d=+50", UA, 50, expect="XY")
assess("degenerate arc (collinear)", ((0, 0), (1, 0), (2, 0)), 2, expect="DEGENERATE")

# Collapse / 3pt / signed extremes (full slice)
assess("R=5 arc, d=-4.999 (near collapse from out)", UA, -4.999, expect="XY")
assess("R=5 arc, d=-5.001 (past collapse)", UA, -5.001, expect="EMPTY")
assess("tiny arc, d=+0.1", ((0,0),(0.001,0),(0,0.001)), 0.1, expect="XY")
assess("tiny arc, d=-0.0005 (r~0.0007, still XY)", ((0,0),(0.001,0),(0,0.001)), -0.0005, expect="XY")

emit()
emit("## B. Sweep over arcs and offsets (gating I1-I5).")
ARCS = {
    "unit @origin": ((1, 0), (0, 1), (-1, 0)),
    "R=5 lower": ((-5, 0), (0, -5), (5, 0)),
    "off-centre R=2 @ (3,4)": ((5, 4), (3, 6), (1, 4)),
    "small quarter": ((2, 0), (1.4142135623730951, 1.4142135623730951), (0, 2)),
}
for nm, arc in ARCS.items():
    r = circumcentre(arc)[2]
    for d in (-0.9 * r, -0.5 * r, -0.01 * r, 0.0, 0.5 * r, 3 * r, -r, -1.5 * r):
        assess(f"{nm} d={d:.3g} (r={r:.3g})", arc, round(d, 12))

emit()
emit("## C. Adversarial huge / major-ish / extreme signed (full collapse/3pt/EMPTY/huge coverage).")
HUGE = ((1e8, 0.0), (0.0, 1e8), (-1e8, 0.0))
rh = circumcentre(HUGE)[2]
for d in (1e6, -0.5*rh, -rh, -rh-1e4, 1e10):
    assess(f"huge d={d:.3g}", HUGE, d)

# Major-ish (long sweep controls)
MAJ = ((1,0), (-1,0.1), (-1,-0.1))  # roughly major around
assess("major-ish d=+1", MAJ, 1.0)
assess("major-ish d=-0.5", MAJ, -0.5)

emit()
if violations:
    emit(f"::error::ARC_OFFSET_XY violated {violations} invariant(s)/expectation(s).")
    sys.exit(1)
emit("# All invariants (I1 radial-dist, I2 same-circle, I3 radial-ray, I4 EMPTY, I5 identity) hold.")
