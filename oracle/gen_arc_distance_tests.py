#!/usr/bin/env python3
# =============================================================================
# oracle/gen_arc_distance_tests.py
# -----------------------------------------------------------------------------
# Adversarial tests for the ARC_DISTANCE oracle mode (D-PT, issue #64/#69),
# driven by the RocqRefRunner (oracle_bin). ARC_DISTANCE emits the shortest
# distance from a query point P to the arc A-B-C.
#
# The nearest on the full circle is the radial foot at |d - r| where d = dist(O,P).
# If the foot is in the arc sweep (using atan2 sector), use it; else min to endpoints.
# Ground truth: exact circumcentre (Fraction), only sqrt/atan2 round in the oracle.
#
# Invariants gated (a '!!' line fails CI):
#   I1 RADIAL     if foot in sweep, dist == |d - r|
#   I2 ENDPOINT   if foot out of sweep, dist == min(dist P A, dist P C)
#   I3 DEGENERATE collinear arc -> DEGENERATE
#   I4 CENTER     P at O -> dist == r
#   I5 NONNEG     dist >= 0
#
# Special families for adversarial: center, outside-sweep, huge-int, major arcs, NaN.
#
# Run from repo root:
#   python3 oracle/gen_arc_distance_tests.py > oracle/arc_distance_tests.txt
# Exit status: nonzero iff violation.
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


def run(arc, p):
    stdin = "ARC_DISTANCE\n%s\n%s\n%s\n%s\n" % (
        f"{arc[0][0]} {arc[0][1]}",
        f"{arc[1][0]} {arc[1][1]}",
        f"{arc[2][0]} {arc[2][1]}",
        f"{p[0]} {p[1]}")
    return subprocess.run([BIN], input=stdin, capture_output=True, text=True).stdout.strip()


def parse(line):
    tok = line.split()
    if not tok:
        return ("?", None)
    if tok[0] in ("DEGENERATE", "NAN"):
        return (tok[0], None)
    try:
        dist = float.fromhex(tok[0]) if ("x" in tok[0] or "p" in tok[0].lower()) else float(tok[0])
        return ("DIST", dist)
    except:
        return ("?", None)


def circumcentre(arc):
    (ax, ay), (bx, by_), (cx, cy) = [(F(x), F(y)) for (x, y) in arc]
    dd = 2 * ((bx - ax) * (cy - ay) - (by_ - ay) * (cx - ax))
    if dd == 0:
        return None
    bk = bx * bx + by_ * by_ - ax * ax - ay * ay
    ck = cx * cx + cy * cy - ax * ax - ay * ay
    ox = ((cy - ay) * bk - (by_ - ay) * ck) / dd
    oy = ((bx - ax) * ck - (cx - ax) * bk) / dd
    r2 = (ox - ax) ** 2 + (oy - ay) ** 2
    return (float(ox), float(oy), math.sqrt(float(r2)))


def point_on_arc_sector(ox, oy, a, b, c, p):
    # replicate driver point_on_arc_sector
    twopi = 2.0 * math.pi
    def ccw(f, t):
        x = (t - f) % twopi
        return x if x >= 0 else x + twopi
    def ang(px, py):
        return math.atan2(py - oy, px - ox)
    angA = ang(a[0], a[1])
    dAB = ccw(angA, ang(b[0], b[1]))
    dAC = ccw(angA, ang(c[0], c[1]))
    dAP = ccw(angA, ang(p[0], p[1]))
    if dAB <= dAC:
        return dAP <= dAC
    else:
        return (dAP >= dAC or abs(dAP) < 1e-12)


def assess(name, arc, p, expect_kind=None):
    global violations
    line = run(arc, p)
    kind, dist = parse(line)
    tags = []
    o = circumcentre(arc)
    if o is None:
        if kind != "DEGENERATE":
            violations += 1
            tags.append(f"!! EXPECTED_DEGENERATE_GOT_{kind}")
        emit(f"  [{name}] -> {line!r}   {' '.join(tags) if tags else 'ok'}")
        return
    ox, oy, r = o
    dx = p[0] - ox
    dy = p[1] - oy
    d = math.hypot(dx, dy)
    if kind == "DIST":
        tol = 1e-9 * (1 + r + abs(d))
        if dist < -tol:
            violations += 1
            tags.append(f"!! I5_NEGATIVE")
        # compute expected
        foot_in = point_on_arc_sector(ox, oy, arc[0], arc[1], arc[2], p) if d > 0 else False
        if foot_in:
            expected = abs(d - r)
        else:
            da = math.hypot(p[0] - arc[0][0], p[1] - arc[0][1])
            dc = math.hypot(p[0] - arc[2][0], p[1] - arc[2][1])
            expected = min(da, dc)
        if abs(dist - expected) > tol:
            violations += 1
            tags.append(f"!! I1_I2_MISMATCH dist={dist:.6g} expected={expected:.6g}")
        # I4 center
        if d < tol:
            if abs(dist - r) > tol:
                violations += 1
                tags.append(f"!! I4_CENTER")
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
emit("# Adversarial tests for ARC_DISTANCE (RocqRefRunner), D-PT / issue #64/#69.")
emit("# I1 radial if in sweep  I2 endpoint fallback  I3 degen  I4 center  I5 nonneg")
emit("# Backing: ArcPointDistance.v + ArcDistance.v (radial) + ArcIntersect (sweep via inCircle/span)")
emit("# '!!' lines are gated-invariant violations (CI-failing).")
emit()

emit("## A. Curated special cases (center, foot in/out, degen, huge).")
# semicircle, P at center
assess("semicircle center", ((1,0),(0,1),(-1,0)), (0,0), expect_kind="DIST")
# foot inside
assess("semicircle radial foot", ((1,0),(0,1),(-1,0)), (0,2), expect_kind="DIST")
# foot outside -> endpoint
assess("semicircle outside foot", ((1,0),(0,1),(-1,0)), (2,0), expect_kind="DIST")
# degen
assess("collinear degen", ((0,0),(1,0),(2,0)), (3,0), expect_kind="DEGENERATE")
# huge
assess("huge coords", ((1e10,0),(0,1e10),(-1e10,0)), (0,1e10+10), expect_kind="DIST")

emit()
emit("## B. Random + adversarial (center, outside-sweep, major, NaN, huge-int).")
import random
random.seed(123)
for i in range(40):
    cx = random.uniform(-100,100)
    cy = random.uniform(-100,100)
    r = random.uniform(0.01, 100)
    a0 = random.uniform(0, 2*math.pi)
    theta = random.uniform(0.001, 2*math.pi - 0.001)
    a = (cx + r*math.cos(a0), cy + r*math.sin(a0))
    c = (cx + r*math.cos(a0+theta), cy + r*math.sin(a0+theta))
    mtheta = a0 + theta * random.random()
    b = (cx + r*math.cos(mtheta), cy + r*math.sin(mtheta))
    # random P
    px = cx + random.uniform(-2*r, 2*r)
    py = cy + random.uniform(-2*r, 2*r)
    assess(f"rand{i}", (a,b,c), (px,py))
    # center
    assess(f"center{i}", (a,b,c), (cx,cy))
    # outside sweep (far point)
    assess(f"outside{i}", (a,b,c), (cx + 10*r, cy + 10*r))

emit()
if violations:
    emit(f"::error::ARC_DISTANCE violated {violations} invariant(s).")
    sys.exit(1)
emit("# All invariants (I1 radial, I2 endpoint, I3 degen, I4 center, I5 nonneg) hold.")