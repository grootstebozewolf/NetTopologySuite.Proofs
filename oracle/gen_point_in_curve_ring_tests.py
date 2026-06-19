#!/usr/bin/env python3
# =============================================================================
# oracle/gen_point_in_curve_ring_tests.py
# -----------------------------------------------------------------------------
# Adversarial tests for the POINT_IN_CURVE_RING oracle mode (V-CP / CP_VALID
# holes-inside-shell, JTS #1195 §7).  The oracle decides point-in-TRUE-curved-
# region by ARC-AWARE ray casting (ray vs actual arcs via circle-horizontal-line
# intersection in-sweep, + chords).
#
# Invariants gated (a '!!' line fails CI):
#   I1  TRUE-REGION    for rings whose exact region is known in closed form, the
#                      oracle's IN/OUT == that independent criterion -- the real
#                      soundness gate (catches the chord-approx bulge bug):
#                        * upper-semicircle ring  -> upper half-disk {x^2+y^2<25, y>0}
#                        * full circle (two arcs)  -> disk {x^2+y^2<25}
#   I2  AGREEMENT      oracle == an independent Python arc-aware ray cast (same
#                      algorithm, separate implementation) over a query grid on
#                      curated rings (catches implementation divergence).
#   I3  HOLES-INSIDE   donut: hole vertices read IN the shell; shell corners read
#                      OUT the hole.
#
# Boundary/degenerate queries (on the circle, on y=0, tangent rays) are skipped
# -- the strict generic-position convention, as in Overlay.edge_crosses_ray.
#
# Run from repo root:
#   python3 oracle/gen_point_in_curve_ring_tests.py > oracle/point_in_curve_ring_tests.txt
# Exit status: nonzero iff a gated invariant fails.
# =============================================================================
import math
import os
import subprocess
import sys

BIN = os.environ.get("ORACLE_BIN", "oracle/oracle_bin")
violations = 0


def emit(s=""):
    print(s)


def seg_line(s):
    if s[0] == "C":
        return f"C {s[1][0]} {s[1][1]} {s[2][0]} {s[2][1]}"
    if s[0] == "A":
        return f"A {s[1][0]} {s[1][1]} {s[2][0]} {s[2][1]} {s[3][0]} {s[3][1]}"
    if s[0] == "E":
        # CurveType=1
        return " ".join(map(str, s))
    if s[0] == "B":
        # CurveType=2
        return " ".join(map(str, s))
    return " ".join(map(str, s))


def oracle(ring, p):
    stdin = "POINT_IN_CURVE_RING\n%d\n%s\n%s %s\n" % (
        len(ring), "\n".join(seg_line(s) for s in ring), p[0], p[1])
    return subprocess.run([BIN], input=stdin, capture_output=True, text=True).stdout.strip()


def circumcentre(a, b, c):
    (ax, ay), (bx, by), (cx, cy) = a, b, c
    d = 2 * ((bx - ax) * (cy - ay) - (by - ay) * (cx - ax))
    if d == 0:
        return None
    bk = bx * bx + by * by - ax * ax - ay * ay
    ck = cx * cx + cy * cy - ax * ax - ay * ay
    ox = ((cy - ay) * bk - (by - ay) * ck) / d
    oy = ((bx - ax) * ck - (cx - ax) * bk) / d
    return (ox, oy, math.hypot(ox - ax, oy - ay))


def on_arc_sector(ox, oy, a, b, c, x, y):
    def ang(px, py):
        return math.atan2(py - oy, px - ox)

    def ccw(f, t):
        v = math.fmod(t - f, 2 * math.pi)
        return v + 2 * math.pi if v < 0 else v
    angA = ang(a[0], a[1])
    dAB = ccw(angA, ang(b[0], b[1]))
    dAC = ccw(angA, ang(c[0], c[1]))
    dAQ = ccw(angA, ang(x, y))
    return dAQ <= dAC + 1e-12 if dAB <= dAC else (dAQ >= dAC - 1e-12 or dAQ <= 1e-12)


def raycast_in(ring, p):
    """Independent Python arc-aware ray cast (mirrors the oracle's rule)."""
    px, py = p
    cnt = 0

    def edge_cross(a, b):
        ax, ay = a
        bx, by = b
        if ay < py < by:
            return px < ax + (bx - ax) * (py - ay) / (by - ay)
        if by < py < ay:
            return px < bx + (ax - bx) * (py - by) / (ay - by)
        return False
    for s in ring:
        if s[0] == "C":
            if edge_cross(s[1], s[2]):
                cnt += 1
        else:
            o = circumcentre(s[1], s[2], s[3])
            if o is None:
                cnt += edge_cross(s[1], s[2]) + edge_cross(s[2], s[3])
                continue
            ox, oy, r = o
            disc = r * r - (py - oy) ** 2
            if disc > 0:
                sq = math.sqrt(disc)
                for x in (ox + sq, ox - sq):
                    if x > px and on_arc_sector(ox, oy, s[1], s[2], s[3], x, py):
                        cnt += 1
    return cnt % 2 == 1


# --- curated rings ---------------------------------------------------------
SEMI = [("A", (5, 0), (0, 5), (-5, 0)), ("C", (-5, 0), (5, 0))]          # upper half-disk
CIRCLE = [("A", (5, 0), (0, 5), (-5, 0)), ("A", (-5, 0), (0, -5), (5, 0))]  # full disk R=5
ARC_SHELL = [("A", (0, 0), (-1, 5), (0, 10)), ("A", (0, 10), (5, 11), (10, 10)),
             ("A", (10, 10), (11, 5), (10, 0)), ("A", (10, 0), (5, -1), (0, 0))]
SQUARE = [("C", (0, 0), (10, 0)), ("C", (10, 0), (10, 10)),
          ("C", (10, 10), (0, 10)), ("C", (0, 10), (0, 0))]
INNER = [("C", (3, 3), (7, 3)), ("C", (7, 3), (7, 7)),
         ("C", (7, 7), (3, 7)), ("C", (3, 7), (3, 3))]

# query grid: offset to avoid integer / circle-boundary alignment
GRID = [(round(x + 0.25, 4), round(y + 0.25, 4))
        for x in range(-7, 8) for y in range(-7, 8)]


def truth_semi(x, y):
    return x * x + y * y < 25 and y > 0


def truth_disk(x, y):
    return x * x + y * y < 25


def near_circle(x, y):
    return abs(x * x + y * y - 25) < 0.2


# ---------------------------------------------------------------------------
emit("# Adversarial tests for POINT_IN_CURVE_RING (RocqRefRunner), V-CP / JTS #1195 §7.")
emit("# Arc-aware ray casting -> TRUE point-in-curved-region.  I1 vs independent")
emit("# closed-form region (half-disk / disk), I2 vs independent ray cast, I3 holes.")
emit("# '!!' lines are gated-invariant violations (CI-failing).")
emit()
emit("## I1 TRUE-REGION: oracle == closed-form membership (the soundness gate).")


def gate_truth(name, ring, truth):
    global violations
    bad = 0
    n = 0
    for (x, y) in GRID:
        if near_circle(x, y) or abs(y) < 1e-6:
            continue
        n += 1
        got = oracle(ring, (x, y)) == "IN"
        if got != truth(x, y):
            bad += 1
            if bad <= 3:
                emit(f"    !! I1_WRONG ({x},{y}) oracle={'IN' if got else 'OUT'} truth={'IN' if truth(x,y) else 'OUT'}")
    if bad:
        violations += 1
    emit(f"  [{name}] {n} pts, {bad} wrong   {'ok' if bad == 0 else '!! FAIL'}")


gate_truth("upper-semicircle ring vs half-disk", SEMI, truth_semi)
gate_truth("full circle (2 arcs) vs disk", CIRCLE, truth_disk)

emit()
emit("## I2 AGREEMENT: oracle == independent Python arc-aware ray cast.")
for nm, ring in (("semicircle", SEMI), ("circle", CIRCLE), ("arc-shell", ARC_SHELL),
                 ("square", SQUARE), ("inner square", INNER)):
    bad = sum(1 for q in GRID if (oracle(ring, q) == "IN") != raycast_in(ring, q))
    if bad:
        violations += 1
    emit(f"  [{nm}] {len(GRID)} queries, {bad} disagree   {'ok' if bad == 0 else '!! I2_DISAGREE'}")

emit()
emit("## Curated bulge points (the bug repro: now correctly IN).")
for q in [(4.125, 1.321), (1.521, 3.907), (4.9, 0.5)]:
    got = oracle(SEMI, q)
    ok = got == "IN"
    if not ok:
        violations += 1
    emit(f"  bulge {q} -> {got}   {'ok' if ok else '!! BULGE_NOT_IN'}")

emit()
emit("## I3 HOLES-INSIDE-SHELL (donut: arc-rounded shell + inner square hole).")
for v in [(3, 3), (7, 3), (7, 7), (3, 7)]:
    got = oracle(ARC_SHELL, v)
    ok = got == "IN"
    if not ok:
        violations += 1
    emit(f"  hole vertex {v} IN arc-shell -> {got}   {'ok' if ok else '!! I3_HOLE_NOT_IN'}")

emit()
if violations:
    emit(f"::error::POINT_IN_CURVE_RING violated {violations} invariant(s).")
    sys.exit(1)
emit("# All invariants (I1 true-region, I2 agreement, I3 holes-inside) hold.")
