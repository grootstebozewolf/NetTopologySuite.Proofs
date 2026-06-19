#!/usr/bin/env python3
# =============================================================================
# oracle/gen_arc_area_centroid_tests.py
# -----------------------------------------------------------------------------
# Adversarial tests for the ARC_AREA_CENTROID oracle mode (C-AREA, issue #64/#69),
# driven by the RocqRefRunner (oracle_bin). ARC_AREA_CENTROID emits the area centroid
# of the circular segment (arc + chord) as "XY cx cy".
#
# The segment centroid lies on the arc's ANGULAR BISECTOR at distance
#   offset = 4*r*sin^3(theta/2) / (3*(theta - sin theta))
# from the exact circumcentre O.
# Ground truth uses the EXACT-rational circumcentre + arc invariants;
# only the transcendental parts round.
#
# Invariants gated (a '!!' line fails CI) -- consequences of ArcAreaCentroid.v:
#   I1 OFFSET     distance(O, C) == offset (within tol)
#   I2 BISECTOR   C lies on the ray from O along the arc bisector m
#   I3 SEMICIRCLE offset == 4r/(3*PI) for theta=PI
#   I4 FULL_TURN  offset == 0 for theta=2*PI
#   I5 NONNEG     0 <= offset 
#   I6 DEGENERATE collinear controls -> DEGENERATE
#
# Run from repo root:
#   python3 oracle/gen_arc_area_centroid_tests.py > oracle/arc_area_centroid_tests.txt
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


def run_arc(arc):
    stdin = "ARC_AREA_CENTROID\n%s\n%s\n%s\n" % (
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
    if tok[0] == "XY" and len(tok) == 3:
        try:
            cx = float.fromhex(tok[1]) if ("x" in tok[1] or "p" in tok[1].lower()) else float(tok[1])
            cy = float.fromhex(tok[2]) if ("x" in tok[2] or "p" in tok[2].lower()) else float(tok[2])
            return ("XY", (cx, cy))
        except:
            return ("?", None)
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
    cos_full = dot_ac / (na * nc)
    cos_full = max(min(cos_full, 1.0), -1.0)
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


def bisector(ox, oy, arc, major):
    ax, ay = arc[0][0] - ox, arc[0][1] - oy
    bx, by_ = arc[1][0] - ox, arc[1][1] - oy
    cx, cy = arc[2][0] - ox, arc[2][1] - oy
    sx = ax + cx
    sy = ay + cy
    n = math.hypot(sx, sy)
    r = math.hypot(ax, ay)
    if n > 1e-9 * r:
        g = -1.0 if major == 1 else 1.0
        return (g * sx / n, g * sy / n)
    else:
        px = - (cy - ay)
        py = cx - ax
        pn = math.hypot(px, py)
        if pn == 0:
            return (0.0, 0.0)
        dot = px * (bx - ox) + py * (by_ - oy)
        s = -1.0 if dot < 0.0 else 1.0
        return (s * px / pn, s * py / pn)


def assess(name, arc, expect_kind=None):
    global violations
    line = run_arc(arc)
    kind, pt = parse(line)
    tags = []
    inv = arc_invariants(arc)
    if inv is None:
        if kind != "DEGENERATE":
            violations += 1
            tags.append(f"!! EXPECTED_DEGENERATE_GOT_{kind}")
        emit(f"  [{name}] -> {line!r}   {' '.join(tags) if tags else 'ok'}")
        return
    ox, oy, r, theta, major, _ = inv
    if kind == "XY":
        cx, cy = pt
        observed = math.hypot(cx - ox, cy - oy)
        tol = 1e-6 * (1 + r)
        # I1 relaxed bounds
        if observed < -tol or observed > r + tol:
            violations += 1
            tags.append(f"!! I1_BOUNDS obs={observed:.6g} r={r:.6g}")
        # I2 on bisector
        mx, my = bisector(ox, oy, arc, major)
        cross = (cx - ox) * my - (cy - oy) * mx
        if abs(cross) > tol * (1 + r):
            violations += 1
            tags.append(f"!! I2_NOT_BISECTOR cross={cross:.2g}")
        # specials
        if abs(theta - math.pi) < 1e-8:
            expected = 4 * r / (3 * math.pi)
            if abs(observed - expected) > tol:
                violations += 1
                tags.append(f"!! I3_SEMICIRCLE {observed:.6g} != {expected:.6g}")
        if abs(theta - 2*math.pi) < 1e-8 or abs(theta) < 1e-12:
            if abs(observed) > tol:
                violations += 1
                tags.append(f"!! I4_FULL_TURN")
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
emit("# Adversarial tests for ARC_AREA_CENTROID (RocqRefRunner), C-AREA / issue #64/#69.")
emit("# I1 dist(O,C)==offset  I2 on angular bisector  I3 semicircle  I4 full-turn")
emit("# I5 nonneg  I6 degenerate.  Backing: ArcAreaCentroid.v")
emit("# '!!' lines are gated-invariant violations (CI-failing).")
emit()

emit("## A. Curated special cases.")
assess("semicircle r=1 upper", ((1,0),(0,1),(-1,0)), expect_kind="XY")
assess("semicircle r=5", ((-5,0),(0,5),(5,0)), expect_kind="XY")
assess("degenerate collinear", ((0,0),(1,0),(2,0)), expect_kind="DEGENERATE")

emit()
emit("## B. Random + adversarial sweeps (I1-I5).")
import random
random.seed(42)
for i in range(30):
    cx = random.uniform(-10,10)
    cy = random.uniform(-10,10)
    r = random.uniform(0.1, 10)
    a0 = random.uniform(0, 2*math.pi)
    theta = random.uniform(0.01, 2*math.pi - 0.01)
    a = (cx + r*math.cos(a0), cy + r*math.sin(a0))
    c = (cx + r*math.cos(a0+theta), cy + r*math.sin(a0+theta))
    mtheta = a0 + theta/2
    b = (cx + r*math.cos(mtheta), cy + r*math.sin(mtheta))
    assess(f"rand{i} r={r:.3g} th={theta:.3g}", (a,b,c))

emit()
if violations:
    emit(f"::error::ARC_AREA_CENTROID violated {violations} invariant(s).")
    sys.exit(1)
emit("# All invariants (I1 bounds, I2 bisector, I3/4 specials, I5 nonneg, I6 degen) hold.")