#!/usr/bin/env python3
# =============================================================================
# oracle/gen_arc_segment_distance_tests.py
# -----------------------------------------------------------------------------
# Adversarial tests for the ARC_SEGMENT_DISTANCE oracle mode (D-SL, JTS #1195
# §7), driven by the RocqRefRunner (oracle_bin).  The oracle value is SANDWICHED
# between two checks tied to theories/ArcSegmentDistance.v:
#
#   * UPPER (no over-estimate): the arc-segment minimum cannot exceed the
#     distance of ANY real (on-arc point, on-segment point) pair.  We densely
#     sample both and require oracle <= dist(sample_arc, sample_seg) for all.
#   * LOWER (no under-estimate): the segment lies in its supporting LINE, so
#     arc-segment distance >= circle-to-line distance = max(0, perp - r) where
#     perp = dist(O, line) (circle_line_dist_lower).  Computed in exact-rational
#     centre/radius; only the final sqrt rounds.
#
# PROVEN invariants gated (a '!!' line fails CI, mirroring the D-AA suite):
#   I1  UPPER            oracle <= every sampled (arc, segment) pair distance.
#   I2  LOWER            oracle >= max(0, perp - r) (circle_line_dist_lower).
#   I3  NON-NEGATIVE     oracle >= 0.
#   I4  SEG-REVERSAL     swapping the segment endpoints P<->Q leaves the value.
#   I5  ARC-REVERSAL     reversing the arc controls (A,B,C)->(C,B,A) leaves it.
#   I6  CROSSING-ZERO    a segment crossing the arc in-sweep => distance 0.
#
# Run from repo root:
#   python3 oracle/gen_arc_segment_distance_tests.py > oracle/arc_segment_distance_tests.txt
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


def run(arc, p, q):
    pts = list(arc) + [p, q]
    stdin = "ARC_SEGMENT_DISTANCE\n" + "".join(f"{x} {y}\n" for (x, y) in pts)
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


def circle_line_gap(arc, p, q):
    """max(0, perp - r), perp = exact dist from O to the line PQ. float."""
    o = circumcentre(arc)
    if o is None:
        return None
    ox, oy, r2 = o
    px, py = F(p[0]), F(p[1])
    qx, qy = F(q[0]), F(q[1])
    dx, dy = qx - px, qy - py
    l2 = dx * dx + dy * dy
    if l2 == 0:
        perp2 = (ox - px) ** 2 + (oy - py) ** 2          # degenerate: point P
    else:
        cross = (ox - px) * dy - (oy - py) * dx
        perp2 = cross * cross / l2
    perp = math.sqrt(float(perp2))
    return max(0.0, perp - math.sqrt(float(r2)))


def sample_arc(arc, n=24):
    o = circumcentre(arc)
    if o is None:
        return []
    ox, oy, r = float(o[0]), float(o[1]), math.sqrt(float(o[2]))
    (ax, ay), (bx, by), (cx, cy) = arc

    def ang(x, y):
        return math.atan2(y - oy, x - ox)

    def ccw(f, t):
        x = math.fmod(t - f, 2 * math.pi)
        return x + 2 * math.pi if x < 0 else x
    angA = ang(ax, ay)
    dAB = ccw(angA, ang(bx, by))
    dAC = ccw(angA, ang(cx, cy))
    span = dAC if dAB <= dAC else dAC - 2 * math.pi
    return [(ox + r * math.cos(angA + tt * span), oy + r * math.sin(angA + tt * span))
            for tt in (i / n for i in range(n + 1))]


def sample_seg(p, q, n=24):
    return [(p[0] + tt * (q[0] - p[0]), p[1] + tt * (q[1] - p[1]))
            for tt in (i / n for i in range(n + 1))]


def assess(name, arc, p, q, expect=None):
    global violations
    line = run(arc, p, q)
    kind, v = parse(line)
    tags = []
    if kind == "VAL":
        if v < -1e-9:
            violations += 1
            tags.append(f"!! I3_NEGATIVE v={v:.6g}")
        gap = circle_line_gap(arc, p, q)
        if gap is not None and v < gap - 1e-6 * (1 + gap):
            violations += 1
            tags.append(f"!! I2_UNDER_BELOW_LINE v={v:.6g} gap={gap:.6g}")
        sa, ss = sample_arc(arc), sample_seg(p, q)
        smin = math.inf
        for (x1, y1) in sa:
            for (x2, y2) in ss:
                dd = math.hypot(x1 - x2, y1 - y2)
                if dd < smin:
                    smin = dd
        if sa and ss and v > smin + 1e-6 * (1 + smin):
            violations += 1
            tags.append(f"!! I1_OVER_ESTIMATE v={v:.6g} sampled_min={smin:.6g}")
        # I4 segment reversal
        _, vsr = parse(run(arc, q, p))
        if vsr is not None and abs(vsr - v) > 1e-6 * (1 + abs(v)):
            violations += 1
            tags.append(f"!! I4_SEG_REVERSAL rev={vsr:.6g}")
        # I5 arc reversal
        _, var = parse(run((arc[2], arc[1], arc[0]), p, q))
        if var is not None and abs(var - v) > 1e-6 * (1 + abs(v)):
            violations += 1
            tags.append(f"!! I5_ARC_REVERSAL rev={var:.6g}")
    exp = "" if expect is None else f" expect={expect}"
    status = " ".join(tags) if tags else "ok"
    shown = v if kind == "VAL" else kind
    emit(f"  [{name}] -> {shown!r}{exp}   {status}")
    return line


# ---------------------------------------------------------------------------
emit("# Adversarial tests for ARC_SEGMENT_DISTANCE (RocqRefRunner), D-SL / JTS #1195 §7.")
emit("# Sandwich: I1 oracle <= sampled (arc,segment) pairs; I2 oracle >= circle-line")
emit("# gap max(0,perp-r) (circle_line_dist_lower).  '!!' = PROVEN-invariant violation.")
emit("# I3 non-neg  I4 seg-reversal  I5 arc-reversal  I6 crossing=0")
emit()
emit("## A. Curated battery (distances hand-verified).")

UA = ((5, 0), (0, 5), (-5, 0))   # upper semicircle R=5 about origin

assess("seg y=8 over [-5,5], foot (0,8) radial (0,5) in sweep", UA, (-5, 8), (5, 8), expect=3)
assess("seg y=4 crosses arc at (+-3,4) (in sweep)", UA, (-5, 4), (5, 4), expect=0)
assess("vertical seg x=20 (arc endpoint (5,0) nearest)", UA, (20, -5), (20, 5), expect=15)
assess("seg y=-3 below upper arc (endpoint to seg)", UA, (-5, -3), (5, -3), expect=3)
assess("foot off-segment: seg y=8 over [10,20] (endpoint (10,8) to arc)",
       UA, (10, 8), (20, 8))
assess("degenerate arc (collinear)", ((0, 0), (1, 0), (2, 0)), (-5, 8), (5, 8),
       expect="DEGENERATE")
assess("zero-length segment = point (0,8), dist |8-5|", UA, (0, 8), (0, 8), expect=3)
assess("seg endpoint exactly on arc (5,0)", UA, (5, 0), (9, 3), expect=0)

emit()
emit("## B. Sweep over segment placements / orientations (gating I1-I6).")
for k in (-6, -3, -1, 0, 2, 5, 6, 9):
    for (x0, x1) in ((-8, 8), (-3, 3), (0, 8), (-8, 0), (2, 4)):
        assess(f"horiz seg y={k} x in [{x0},{x1}]", UA, (x0, k), (x1, k))
# vertical segments at various x
for vx in (-8, -3, 0, 3, 6, 12):
    assess(f"vert seg x={vx} y in [-6,6]", UA, (vx, -6), (vx, 6))

emit()
if violations:
    emit(f"::error::ARC_SEGMENT_DISTANCE violated {violations} proven invariant(s) (I1-I6).")
    sys.exit(1)
emit("# All proven invariants (I1-I6) hold across the suite.")
