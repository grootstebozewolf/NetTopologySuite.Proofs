#!/usr/bin/env python3
# =============================================================================
# oracle/gen_cp_ring_simple_tests.py
# -----------------------------------------------------------------------------
# Adversarial tests for the V-CP RING-SIMPLICITY component (JTS #1195 §7): a
# CurvePolygon's shell + hole rings are each simple.  There is NO new oracle
# mode -- this COMPOSES the existing RING_SIMPLE mode by running it on every
# ring of the polygon, which is exactly what theories/CurvePolygonSimple.v
# states: simple_curve_polygon = simple_curve_ring (outer) AND every hole is
# simple_curve_ring (simple_curve_polygon_{outer,hole}_simple projections).
#
# Invariants gated (a '!!' line fails CI):
#   I1  COMPOSITION    the polygon is ring-simple IFF RING_SIMPLE returns SIMPLE
#                      on the shell AND on every hole (matches the Forall in
#                      simple_curve_polygon).
#   I2  WITNESS-SOUND  for any ring returning NOT_SIMPLE i j x y, the witness
#                      (x,y) lies on BOTH segments i,j of that ring
#                      (= curve_polygon_{outer,hole}_not_simple_of_witness, which
#                      reuses curve_ring_not_simple_of_witness).
#   I3  HOLE-REUSE     a self-crossing HOLE is detected by the same RING_SIMPLE
#                      as a self-crossing shell (holes are not special-cased).
#
# Run from repo root:
#   python3 oracle/gen_cp_ring_simple_tests.py > oracle/cp_ring_simple_tests.txt
# Exit status: nonzero iff a gated invariant or curated expectation fails.
# =============================================================================
import math
import os
import subprocess
import sys
from fractions import Fraction as F

BIN = os.environ.get("ORACLE_BIN", "oracle/oracle_bin")
violations = 0

# A segment is ("C", p, q) or ("A", a, b, c); points are (x, y) pairs.
# A ring is a list of segments; a polygon is (shell_ring, [hole_ring, ...]).


def emit(s=""):
    print(s)


def seg_line(s):
    if s[0] == "C":
        return f"C {s[1][0]} {s[1][1]} {s[2][0]} {s[2][1]}"
    return f"A {s[1][0]} {s[1][1]} {s[2][0]} {s[2][1]} {s[3][0]} {s[3][1]}"


def run_ring(ring):
    stdin = "RING_SIMPLE\n%d\n%s\n" % (len(ring), "\n".join(seg_line(s) for s in ring))
    return subprocess.run([BIN], input=stdin, capture_output=True, text=True).stdout.strip()


def parse(line):
    tok = line.split()
    if not tok:
        return ("EMPTY", None)
    if tok[0] in ("SIMPLE", "DEGENERATE", "NAN"):
        return (tok[0], None)
    if tok[0] == "NOT_SIMPLE":
        i, j = int(tok[1]), int(tok[2])
        x = float.fromhex(tok[3]) if ("x" in tok[3] or "p" in tok[3].lower()) else float(tok[3])
        y = float.fromhex(tok[4]) if ("x" in tok[4] or "p" in tok[4].lower()) else float(tok[4])
        return ("NOT_SIMPLE", (i, j, x, y))
    return ("?", None)


def circumcentre(a, b, c):
    (ax, ay), (bx, by), (cx, cy) = [(F(p[0]), F(p[1])) for p in (a, b, c)]
    d = 2 * ((bx - ax) * (cy - ay) - (by - ay) * (cx - ax))
    if d == 0:
        return None
    bk = bx * bx + by * by - ax * ax - ay * ay
    ck = cx * cx + cy * cy - ax * ax - ay * ay
    ox = ((cy - ay) * bk - (by - ay) * ck) / d
    oy = ((bx - ax) * ck - (cx - ax) * bk) / d
    return (float(ox), float(oy), math.sqrt(float((ox - ax) ** 2 + (oy - ay) ** 2)))


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
    return dAQ <= dAC + 1e-9 if dAB <= dAC else (dAQ >= dAC - 1e-9 or dAQ <= 1e-9)


def on_segment(s, x, y):
    if s[0] == "C":
        (px, py), (qx, qy) = s[1], s[2]
        dx, dy = qx - px, qy - py
        l2 = dx * dx + dy * dy
        cross = (qx - px) * (y - py) - (qy - py) * (x - px)
        if abs(cross) > 1e-6 * (1 + l2):
            return False
        dot = (x - px) * dx + (y - py) * dy
        return -1e-6 <= dot <= l2 + 1e-6
    o = circumcentre(s[1], s[2], s[3])
    if o is None:
        return False
    ox, oy, r = o
    if abs(math.hypot(x - ox, y - oy) - r) > 1e-6 * (1 + r):
        return False
    return on_arc_sector(ox, oy, s[1], s[2], s[3], x, y)


def assess(name, shell, holes, expect=None):
    """expect: 'SIMPLE' (every ring simple) or 'NOT_SIMPLE' (some ring not)."""
    global violations
    rings = [("shell", shell)] + [(f"hole{k}", h) for k, h in enumerate(holes)]
    tags = []
    all_simple = True
    detail = []
    for label, ring in rings:
        line = run_ring(ring)
        kind, data = parse(line)
        detail.append(f"{label}={kind}")
        if kind == "NOT_SIMPLE":
            all_simple = False
            i, j, x, y = data
            # I2 witness soundness for this ring
            if not on_segment(ring[i], x, y):
                violations += 1
                tags.append(f"!! I2_WITNESS_OFF_{label}_seg{i}")
            if not on_segment(ring[j], x, y):
                violations += 1
                tags.append(f"!! I2_WITNESS_OFF_{label}_seg{j}")
        elif kind != "SIMPLE":
            all_simple = False  # DEGENERATE / NAN -> not a simple polygon
    got = "SIMPLE" if all_simple else "NOT_SIMPLE"
    # I1 composition / curated expectation
    if expect is not None and got != expect:
        violations += 1
        tags.append(f"!! I1_EXPECTED_{expect}_GOT_{got}")
    status = " ".join(tags) if tags else "ok"
    emit(f"  [{name}] -> polygon={got} ({', '.join(detail)})   {status}")


# --- shared shapes ---------------------------------------------------------
SQUARE = [("C", (0, 0), (10, 0)), ("C", (10, 0), (10, 10)),
          ("C", (10, 10), (0, 10)), ("C", (0, 10), (0, 0))]
INNER = [("C", (3, 3), (7, 3)), ("C", (7, 3), (7, 7)),
         ("C", (7, 7), (3, 7)), ("C", (3, 7), (3, 3))]
BOWTIE = [("C", (0, 0), (10, 10)), ("C", (10, 10), (10, 0)),
          ("C", (10, 0), (0, 10)), ("C", (0, 10), (0, 0))]
# rounded shell: four quarter-ish arcs bulging OUTWARD, simple
ARC_SHELL = [("A", (0, 0), (-1, 5), (0, 10)), ("A", (0, 10), (5, 11), (10, 10)),
             ("A", (10, 10), (11, 5), (10, 0)), ("A", (10, 0), (5, -1), (0, 0))]

# ---------------------------------------------------------------------------
emit("# Adversarial tests for the V-CP ring-simplicity component (RING_SIMPLE per ring).")
emit("# I1 composition (polygon simple IFF shell + every hole SIMPLE),")
emit("# I2 witness-soundness per ring (curve_polygon_*_not_simple_of_witness),")
emit("# I3 hole-reuse (a self-crossing hole is caught like a self-crossing shell).")
emit("# '!!' lines are gated-invariant / expectation violations (CI-failing).")
emit()
emit("## Curated CurvePolygons (verdict hand-verified).")

assess("donut: square shell + square hole (both simple)", SQUARE, [INNER], expect="SIMPLE")
assess("no-hole simple square", SQUARE, [], expect="SIMPLE")
assess("two disjoint simple holes", SQUARE,
       [[("C", (1, 1), (3, 1)), ("C", (3, 1), (3, 3)), ("C", (3, 3), (1, 3)), ("C", (1, 3), (1, 1))],
        [("C", (6, 6), (8, 6)), ("C", (8, 6), (8, 8)), ("C", (8, 8), (6, 8)), ("C", (6, 8), (6, 6))]],
       expect="SIMPLE")
assess("shell is a bowtie (shell ring not simple)", BOWTIE, [INNER], expect="NOT_SIMPLE")
assess("hole self-crosses (I3: hole bowtie)", SQUARE, [BOWTIE], expect="NOT_SIMPLE")
assess("arc-rounded shell + square hole (simple)", ARC_SHELL, [INNER], expect="SIMPLE")
assess("arc-rounded shell, hole self-crosses", ARC_SHELL, [BOWTIE], expect="NOT_SIMPLE")

emit()
if violations:
    emit(f"::error::V-CP ring-simplicity violated {violations} invariant(s)/expectation(s).")
    sys.exit(1)
emit("# All invariants (I1 composition, I2 witness-sound, I3 hole-reuse) hold.")
