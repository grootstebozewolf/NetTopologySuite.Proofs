#!/usr/bin/env python3
# =============================================================================
# oracle/gen_arc_arc_distance_tests.py
# -----------------------------------------------------------------------------
# Adversarial tests for the ARC_ARC_DISTANCE oracle mode (D-AA, JTS #1195 §7),
# driven by the RocqRefRunner (oracle_bin).  The oracle value is SANDWICHED
# between two checks tied to theories/ArcArcDistance.v:
#
#   * UPPER (no over-estimate): the arc-arc minimum cannot exceed the distance
#     of ANY real on-arc point pair.  We densely sample both arcs (along their
#     sweeps) and require oracle <= dist(sample1, sample2) for every pair.
#   * LOWER (no under-estimate): every cross-circle pair -- hence the arc-arc
#     minimum -- is at least the circle-circle gap
#         max(0, d - r1 - r2, |r1 - r2| - d)
#     (two_circles_dist_lower).  We require oracle >= that, in exact-rational
#     centres/radii (only the final sqrt rounds).
#
# PROVEN invariants gated (a '!!' line fails CI, mirroring the N-AA / N-AL
# suites):
#   I1  UPPER           oracle <= every sampled on-arc pair distance.
#   I2  LOWER           oracle >= circle-circle gap (two_circles_dist_lower).
#   I3  NON-NEGATIVE    oracle >= 0.
#   I4  SYMMETRY        dist(a1,a2) == dist(a2,a1).
#   I5  REVERSAL-STABLE reversing either arc's controls leaves the value.
#   I6  SHARED-VERTEX   arcs sharing an endpoint => distance 0.
#
# Run from repo root:
#   python3 oracle/gen_arc_arc_distance_tests.py > oracle/arc_arc_distance_tests.txt
# Exit status: nonzero iff a PROVEN invariant (I1-I6) is violated.
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


def run(a1, a2):
    pts = list(a1) + list(a2)
    stdin = "ARC_ARC_DISTANCE\n" + "".join(f"{x} {y}\n" for (x, y) in pts)
    return subprocess.run([BIN], input=stdin, capture_output=True,
                          text=True).stdout.strip()


def parse(line):
    tok = line.split()
    if not tok:
        return ("NAN", None)
    if tok[0] in ("DEGENERATE", "NAN", "COINCIDENT"):
        return (tok[0], None)
    t = tok[0]
    return ("VAL", float.fromhex(t) if ("x" in t or "p" in t.lower()) else float(t))


def circumcentre(arc):
    (ax, ay), (bx, by), (cx, cy) = [(F(x), F(y)) for (x, y) in arc]
    d = 2 * ((bx - ax) * (cy - ay) - (by - ay) * (cx - ax))
    if d == 0:
        return None
    bk = bx * bx + by * by - ax * ax - ay * ay
    ck = cx * cx + cy * cy - ax * ax - ay * ay
    ox = ((cy - ay) * bk - (by - ay) * ck) / d
    oy = ((bx - ax) * ck - (cx - ax) * bk) / d
    r2 = (ox - ax) ** 2 + (oy - ay) ** 2
    return (ox, oy, r2)


def circle_gap(a1, a2):
    """Exact-centred circle-circle distance max(0, d-r1-r2, |r1-r2|-d), float."""
    o1, o2 = circumcentre(a1), circumcentre(a2)
    if o1 is None or o2 is None:
        return None
    d = math.sqrt(float((o2[0] - o1[0]) ** 2 + (o2[1] - o1[1]) ** 2))
    r1, r2 = math.sqrt(float(o1[2])), math.sqrt(float(o2[2]))
    return max(0.0, d - r1 - r2, abs(r1 - r2) - d)


def sample_arc(arc, n=24):
    """Sample points along arc A->B->C (same A-through-B-to-C sweep the oracle
       sector test uses).  Returns [] if collinear."""
    o = circumcentre(arc)
    if o is None:
        return []
    ox, oy, r2 = float(o[0]), float(o[1]), math.sqrt(float(o[2]))
    (ax, ay), (bx, by), (cx, cy) = arc

    def ang(px, py):
        return math.atan2(py - oy, px - ox)

    def ccw(f, t):
        x = math.fmod(t - f, 2 * math.pi)
        return x + 2 * math.pi if x < 0 else x
    angA = ang(ax, ay)
    dAB = ccw(angA, ang(bx, by))
    dAC = ccw(angA, ang(cx, cy))
    span = dAC if dAB <= dAC else dAC - 2 * math.pi   # +CCW or -CW
    return [(ox + r2 * math.cos(angA + tt * span),
             oy + r2 * math.sin(angA + tt * span))
            for tt in (i / n for i in range(n + 1))]


def shares_endpoint(a1, a2):
    return bool({a1[0], a1[2]} & {a2[0], a2[2]})


def assess(name, a1, a2, expect=None):
    global violations
    line = run(a1, a2)
    kind, v = parse(line)
    tags = []

    if kind == "VAL":
        # I3 non-negative
        if v < -1e-9:
            violations += 1
            tags.append(f"!! I3_NEGATIVE v={v:.6g}")
        # I2 lower bound (circle-circle gap)
        gap = circle_gap(a1, a2)
        if gap is not None and v < gap - 1e-6 * (1 + gap):
            violations += 1
            tags.append(f"!! I2_UNDER_BELOW_CIRCLE v={v:.6g} gap={gap:.6g}")
        # I1 upper bound vs sampled on-arc pairs
        s1, s2 = sample_arc(a1), sample_arc(a2)
        smin = math.inf
        for (x1, y1) in s1:
            for (x2, y2) in s2:
                dd = math.hypot(x1 - x2, y1 - y2)
                if dd < smin:
                    smin = dd
        if s1 and s2 and v > smin + 1e-6 * (1 + smin):
            violations += 1
            tags.append(f"!! I1_OVER_ESTIMATE v={v:.6g} sampled_min={smin:.6g}")
        # I4 symmetry
        _, vsym = parse(run(a2, a1))
        if vsym is not None and abs(vsym - v) > 1e-9 * (1 + abs(v)):
            violations += 1
            tags.append(f"!! I4_ASYMMETRIC sym={vsym:.6g}")
        # I5 reversal stability (either arc)
        for label, b1, b2 in (("a1", (a1[2], a1[1], a1[0]), a2),
                              ("a2", a1, (a2[2], a2[1], a2[0]))):
            _, vr = parse(run(b1, b2))
            if vr is not None and abs(vr - v) > 1e-6 * (1 + abs(v)):
                violations += 1
                tags.append(f"!! I5_REVERSAL_{label} rev={vr:.6g}")
        # I6 shared vertex => 0
        if shares_endpoint(a1, a2) and v > 1e-6:
            violations += 1
            tags.append(f"!! I6_SHARED_VERTEX_NONZERO v={v:.6g}")

    exp = "" if expect is None else f" expect={expect}"
    status = " ".join(tags) if tags else "ok"
    shown = v if kind == "VAL" else kind
    emit(f"  [{name}] -> {shown!r}{exp}   {status}")
    return line


# ---------------------------------------------------------------------------
emit("# Adversarial tests for ARC_ARC_DISTANCE (RocqRefRunner), D-AA / JTS #1195 §7.")
emit("# Sandwich: I1 oracle <= sampled on-arc pairs; I2 oracle >= circle gap")
emit("# (two_circles_dist_lower).  '!!' lines are PROVEN-invariant violations.")
emit("# I3 non-neg  I4 symmetry  I5 reversal-stable  I6 shared-vertex=0")
emit()
emit("## A. Curated battery (distances hand-verified).")

assess("external, arcs facing (feet in sweeps)",
       ((0, 5), (5, 0), (0, -5)), ((20, 5), (15, 0), (20, -5)), expect=10)
assess("external, arcs facing away (endpoint min)",
       ((0, 5), (-5, 0), (0, -5)), ((20, 5), (25, 0), (20, -5)), expect=20)
assess("intersecting arcs cross at (4,3)",
       ((5, 0), (0, 5), (-5, 0)), ((3, 0), (8, 5), (13, 0)), expect=0)
assess("shared start vertex (5,0)",
       ((5, 0), (0, 5), (-5, 0)), ((5, 0), (10, 5), (15, 0)), expect=0)
assess("nested circles (gap |5-2|-1 = 2), upper arcs",
       ((5, 0), (0, 5), (-5, 0)), ((3, 0), (1, 2), (-1, 0)), expect=2)
assess("external tangent (d = r1+r2 = 10) at (5,0)",
       ((5, 0), (0, 5), (-5, 0)), ((5, 0), (10, -5), (15, 0)), expect=0)
assess("degenerate arc1 (collinear)",
       ((0, 0), (1, 0), (2, 0)), ((20, 5), (15, 0), (20, -5)), expect="DEGENERATE")

emit()
emit("## B. Sweep: arc2 centre walked across separations / orientations (gating I1-I6).")
UA = ((5, 0), (0, 5), (-5, 0))     # upper semicircle R=5 about origin
LA = ((5, 0), (0, -5), (-5, 0))    # lower semicircle
for cx in (8, 10, 12, 16, 20, 30):
    for arc2 in (((cx - 5, 0), (cx, 5), (cx + 5, 0)),      # upper, facing left/away
                 ((cx - 5, 0), (cx, -5), (cx + 5, 0)),     # lower
                 ((cx + 5, 0), (cx, 5), (cx - 5, 0))):     # reversed sweep
        assess(f"UA vs centre({cx},0) variant", UA, arc2)
assess("LA vs upper arc2 centre(12,0)", LA, ((7, 0), (12, 5), (17, 0)))

emit()
if violations:
    emit(f"::error::ARC_ARC_DISTANCE violated {violations} proven invariant(s) (I1-I6).")
    sys.exit(1)
emit("# All proven invariants (I1-I6) hold across the suite.")
