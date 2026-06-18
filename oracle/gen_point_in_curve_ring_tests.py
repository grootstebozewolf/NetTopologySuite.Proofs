#!/usr/bin/env python3
# =============================================================================
# oracle/gen_point_in_curve_ring_tests.py
# -----------------------------------------------------------------------------
# Adversarial tests for the POINT_IN_CURVE_RING oracle mode (V-CP / CP_VALID
# holes-inside-shell, JTS #1195 §7), driven by the RocqRefRunner (oracle_bin).
#
# POINT_IN_CURVE_RING decides whether a query point is inside a curve ring, via
# the EXACT densified control polygon (CurveGeometry.chord_approx_ring: arc ->
# [start;mid;end], chord -> [p;q]) and Overlay.point_in_ring (rightward-ray
# crossing-number parity).  Ground truth here re-implements the SAME predicate
# bit-for-bit with fractions.Fraction -- Overlay.ring_edges (consecutive vertex
# pairs) + Overlay.edge_crosses_ray (STRICT y-straddle + x-intersection strictly
# right, the generic-position convention) -- so the oracle (also exact-Q) must
# AGREE on every input.
#
# Invariants gated (a '!!' line fails CI):
#   I1  AGREEMENT      oracle IN/OUT == exact ray-parity on the control polygon,
#                      for a grid of query points over curated rings (= the
#                      Coq Overlay.point_in_ring definition the oracle pins).
#   I2  HOLES-INSIDE   donut: every hole vertex is IN the shell (the
#                      hole_inside_outer / valid_curve_polygon_cp_hole_witness
#                      composition) and shell vertices are OUT the hole.
#
# Run from repo root:
#   python3 oracle/gen_point_in_curve_ring_tests.py > oracle/point_in_curve_ring_tests.txt
# Exit status: nonzero iff a gated invariant fails.
# =============================================================================
import os
import subprocess
import sys
from fractions import Fraction as F

BIN = os.environ.get("ORACLE_BIN", "oracle/oracle_bin")
violations = 0


def emit(s=""):
    print(s)


def seg_line(s):
    if s[0] == "C":
        return f"C {s[1][0]} {s[1][1]} {s[2][0]} {s[2][1]}"
    return f"A {s[1][0]} {s[1][1]} {s[2][0]} {s[2][1]} {s[3][0]} {s[3][1]}"


def run(ring, p):
    stdin = "POINT_IN_CURVE_RING\n%d\n%s\n%s %s\n" % (
        len(ring), "\n".join(seg_line(s) for s in ring), p[0], p[1])
    return subprocess.run([BIN], input=stdin, capture_output=True, text=True).stdout.strip()


def densify(ring):
    """chord_approx_ring: arc -> [start;mid;end], chord -> [p;q].  Exact Fraction."""
    pts = []
    for s in ring:
        if s[0] == "C":
            pts += [s[1], s[2]]
        else:
            pts += [s[1], s[2], s[3]]
    return [(F(x), F(y)) for (x, y) in pts]


def edge_crosses_ray(p, a, b):
    """Overlay.edge_crosses_ray, exact (strict inequalities)."""
    px, py = p
    ax, ay = a
    bx, by = b
    if ay < py < by:
        return px < ax + (bx - ax) * (py - ay) / (by - ay)
    if by < py < ay:
        return px < bx + (ax - bx) * (py - by) / (ay - by)
    return False


def point_in_ring_exact(p, pts):
    """Overlay.point_in_ring: parity of ring_edges (consecutive pairs) crossings."""
    cnt = 0
    for i in range(len(pts) - 1):
        if edge_crosses_ray(p, pts[i], pts[i + 1]):
            cnt += 1
    return cnt % 2 == 1


def oracle_in(ring, p):
    out = run(ring, p).strip()
    return out  # "IN" / "OUT" / "NAN"


def assess(name, ring, queries):
    global violations
    pts = densify(ring)
    tags = []
    for q in queries:
        want = "IN" if point_in_ring_exact((F(q[0]), F(q[1])), pts) else "OUT"
        got = oracle_in(ring, q)
        if got != want:
            violations += 1
            tags.append(f"!! I1_DISAGREE q={q} oracle={got} exact={want}")
    status = " ".join(tags) if tags else f"ok ({len(queries)} queries agree)"
    emit(f"  [{name}] {status}")


# --- shapes ----------------------------------------------------------------
SQUARE = [("C", (0, 0), (10, 0)), ("C", (10, 0), (10, 10)),
          ("C", (10, 10), (0, 10)), ("C", (0, 10), (0, 0))]
INNER = [("C", (3, 3), (7, 3)), ("C", (7, 3), (7, 7)),
         ("C", (7, 7), (3, 7)), ("C", (3, 7), (3, 3))]
ARC_SHELL = [("A", (0, 0), (-1, 5), (0, 10)), ("A", (0, 10), (5, 11), (10, 10)),
             ("A", (10, 10), (11, 5), (10, 0)), ("A", (10, 0), (5, -1), (0, 0))]
# a ring with a CONCAVE arc (control mid pulled inward) -> non-convex control polygon
CONCAVE = [("A", (0, 0), (5, 3), (10, 0)), ("C", (10, 0), (10, 10)),
           ("C", (10, 10), (0, 10)), ("C", (0, 10), (0, 0))]

# a query grid of DYADIC (half-integer) coords: exactly representable in binary64
# so F(q) (ground truth) == qf(q) (oracle), and half-integer y never equals an
# integer-y control vertex -> no ray-vertex grazing.
GRID = [(x + 0.5, y + 0.5) for x in range(-2, 13, 2) for y in range(-2, 13, 2)]

# ---------------------------------------------------------------------------
emit("# Adversarial tests for POINT_IN_CURVE_RING (RocqRefRunner), V-CP / JTS #1195 §7.")
emit("# I1 AGREEMENT: oracle IN/OUT == exact ray-parity (Overlay.point_in_ring) on")
emit("# the densified control polygon, over a query grid.  I2 holes-inside-shell.")
emit("# '!!' lines are gated-invariant violations (CI-failing).")
emit()
emit("## A. Agreement over a query grid (curated rings).")
assess("square", SQUARE, GRID)
assess("arc-rounded shell", ARC_SHELL, GRID)
assess("concave-arc ring", CONCAVE, GRID)
assess("inner square (hole shape)", INNER, GRID)

emit()
emit("## B. Curated interior/exterior points.")
assess("square: clearly in/out", SQUARE,
       [(5, 5), (5, 0.5), (1, 9), (15, 5), (-3, 5), (5, 15), (5, -3)])
assess("arc-shell: non-grazing in/out", ARC_SHELL,
       [(5, 4.5), (1, 1), (9, 9), (-5, 5), (20, 5)])

emit()
emit("## C. I2 holes-inside-shell composition (donut: shell SQUARE, hole INNER).")
hole_verts = [(3, 3), (7, 3), (7, 7), (3, 7)]
for v in hole_verts:
    got = oracle_in(SQUARE, v)
    ok = got == "IN"
    if not ok:
        violations += 1
    emit(f"  hole vertex {v} IN shell -> {got}   {'ok' if ok else '!! I2_HOLE_VERTEX_NOT_IN_SHELL'}")
shell_verts = [(0, 0), (10, 0), (10, 10), (0, 10)]
for v in shell_verts:
    # shell corners are OUTSIDE the inner hole [3,7]^2
    got = oracle_in(INNER, v)
    ok = got == "OUT"
    if not ok:
        violations += 1
    emit(f"  shell vertex {v} OUT hole -> {got}   {'ok' if ok else '!! I2_SHELL_VERTEX_IN_HOLE'}")

emit()
if violations:
    emit(f"::error::POINT_IN_CURVE_RING violated {violations} invariant(s).")
    sys.exit(1)
emit("# All invariants (I1 agreement, I2 holes-inside-shell) hold.")
