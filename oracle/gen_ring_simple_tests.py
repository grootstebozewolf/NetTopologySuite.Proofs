#!/usr/bin/env python3
# =============================================================================
# oracle/gen_ring_simple_tests.py
# -----------------------------------------------------------------------------
# Adversarial tests for the RING_SIMPLE oracle mode (V-CS / V-CP, JTS #1195 §7),
# driven by the RocqRefRunner (oracle_bin).
#
# PROVEN invariant gated (a '!!' line fails CI):
#   I1  WITNESS-SOUND  every NOT_SIMPLE verdict "NOT_SIMPLE i j x y" must exhibit
#       a genuine crossing: the witness (x,y) lies on BOTH segment i and segment
#       j, and (i,j) are non-adjacent (or, if adjacent, the witness is not a
#       permitted shared vertex).  This is exactly
#       theories/CurveRingSimple.v : curve_ring_not_simple_of_witness -- a
#       crossing witness of two non-adjacent segments refutes curve_ring_simple.
#
# Also checked:
#   I2  EXPECTED       curated rings match their hand-verified SIMPLE/NOT_SIMPLE
#                      class.
#   I3  ROTATION       a ring is a cyclic sequence: rotating the segment list
#                      (which re-indexes adjacency) preserves the verdict class.
#
# The completeness direction (SIMPLE => genuinely no crossing) is the oracle's
# all-pairs computation, not a proof obligation; reflex-arc (sweep >= pi) span
# membership is the deferred atan2 layer.
#
# Run from repo root:
#   python3 oracle/gen_ring_simple_tests.py > oracle/ring_simple_tests.txt
# Exit status: nonzero iff a PROVEN invariant (I1) or a curated expectation fails.
# =============================================================================
import math
import os
import subprocess
import sys
from fractions import Fraction as F

BIN = os.environ.get("ORACLE_BIN", "oracle/oracle_bin")
violations = 0

# A segment is ("C", p, q) or ("A", a, b, c); points are (x, y) number pairs.


def seg_line(s):
    if s[0] == "C":
        return f"C {s[1][0]} {s[1][1]} {s[2][0]} {s[2][1]}"
    return f"A {s[1][0]} {s[1][1]} {s[2][0]} {s[2][1]} {s[3][0]} {s[3][1]}"


def run(ring):
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


def verdict_class(line):
    k, _ = parse(line)
    return k


def circumcentre(a, b, c):
    (ax, ay), (bx, by), (cx, cy) = [(F(p[0]), F(p[1])) for p in (a, b, c)]
    d = 2 * ((bx - ax) * (cy - ay) - (by - ay) * (cx - ax))
    if d == 0:
        return None
    bk = bx * bx + by * by - ax * ax - ay * ay
    ck = cx * cx + cy * cy - ax * ax - ay * ay
    ox = ((cy - ay) * bk - (by - ay) * ck) / d
    oy = ((bx - ax) * ck - (cx - ax) * bk) / d
    r2 = (ox - ax) ** 2 + (oy - ay) ** 2
    return (float(ox), float(oy), math.sqrt(float(r2)))


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
        tol = 1e-6 * (1 + l2)
        cross = (qx - px) * (y - py) - (qy - py) * (x - px)
        if abs(cross) > tol:
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


def assess(name, ring, expect=None):
    global violations
    line = run(ring)
    kind, data = parse(line)
    tags = []
    if kind == "NOT_SIMPLE":
        i, j, x, y = data
        n = len(ring)
        # I1: witness on both reported segments
        if not on_segment(ring[i], x, y):
            violations += 1
            tags.append(f"!! I1_WITNESS_OFF_SEG{i}")
        if not on_segment(ring[j], x, y):
            violations += 1
            tags.append(f"!! I1_WITNESS_OFF_SEG{j}")
        # I1: must be a genuine (non-adjacent, or non-vertex) crossing
        adjacent = (j == i + 1) or (i == 0 and j == n - 1)
        if adjacent:
            # permitted shared vertices
            verts = []
            if j == i + 1:
                verts.append(ring[i][-1])
            if i == 0 and j == n - 1:
                verts.append(ring[0][1])
            if any(math.hypot(x - v[0], y - v[1]) <= 1e-6 * (1 + abs(v[0]) + abs(v[1]))
                   for v in verts):
                violations += 1
                tags.append("!! I1_WITNESS_IS_PERMITTED_VERTEX")
    # I3: rotation invariance of the verdict class
    if kind in ("SIMPLE", "NOT_SIMPLE") and len(ring) > 1:
        rot = ring[1:] + ring[:1]
        if verdict_class(run(rot)) != kind:
            violations += 1
            tags.append("!! I3_ROTATION_CHANGED_VERDICT")
    # I2: curated expectation
    if expect is not None and kind != expect:
        violations += 1
        tags.append(f"!! I2_EXPECTED_{expect}_GOT_{kind}")
    status = " ".join(tags) if tags else "ok"
    emit(f"  [{name}] -> {line!r}   {status}")
    return line


def emit(s=""):
    print(s)


# ---------------------------------------------------------------------------
emit("# Adversarial tests for RING_SIMPLE (RocqRefRunner), V-CS/V-CP / JTS #1195 §7.")
emit("# I1 WITNESS-SOUND (curve_ring_not_simple_of_witness): a NOT_SIMPLE witness")
emit("# lies on both reported non-adjacent segments.  I2 curated class.  I3 rotation.")
emit("# '!!' lines are PROVEN-invariant / expectation violations (CI-failing).")
emit()
emit("## Curated rings (verdict hand-verified).")

SQUARE = [("C", (0, 0), (10, 0)), ("C", (10, 0), (10, 10)),
          ("C", (10, 10), (0, 10)), ("C", (0, 10), (0, 0))]
BOWTIE = [("C", (0, 0), (10, 10)), ("C", (10, 10), (10, 0)),
          ("C", (10, 0), (0, 10)), ("C", (0, 10), (0, 0))]
LENS = [("A", (0, 0), (5, 5), (10, 0)), ("A", (0, 0), (5, -5), (10, 0))]
TRI = [("C", (0, 0), (10, 0)), ("C", (10, 0), (5, 8)), ("C", (5, 8), (0, 0))]
PENT = [("C", (0, 0), (10, 0)), ("C", (10, 0), (10, 10)), ("C", (10, 10), (5, 15)),
        ("C", (5, 15), (0, 10)), ("C", (0, 10), (0, 0))]
ARC_CHORD_CROSS = [("A", (0, 0), (5, 3), (10, 0)), ("C", (10, 0), (10, 1.5)),
                   ("C", (10, 1.5), (0, 1.5)), ("C", (0, 1.5), (0, 0))]
ARC_ARC_CROSS = [("A", (0, 0), (5, 8), (10, 0)), ("C", (10, 0), (10, 2)),
                 ("A", (10, 2), (5, -6), (0, 2)), ("C", (0, 2), (0, 0))]
# A wide tall arc whose circle re-enters: the chord at y=5 is OUTSIDE its x-range
TALL_ARC_OK = [("A", (0, 0), (5, 20), (10, 0)), ("C", (10, 0), (10, 5)),
               ("C", (10, 5), (0, 5)), ("C", (0, 5), (0, 0))]

assess("square (4 chords)", SQUARE, expect="SIMPLE")
assess("bowtie (diag x anti-diag)", BOWTIE, expect="NOT_SIMPLE")
assess("lens (2 arcs, shared ends)", LENS, expect="SIMPLE")
assess("triangle (3 chords, all adjacent)", TRI, expect="SIMPLE")
assess("pentagon", PENT, expect="SIMPLE")
assess("arc over non-adjacent chord (shallow, crosses)", ARC_CHORD_CROSS, expect="NOT_SIMPLE")
assess("arc-arc non-adjacent crossing", ARC_ARC_CROSS, expect="NOT_SIMPLE")
assess("tall arc, chord outside its x-range (simple)", TALL_ARC_OK, expect="SIMPLE")
assess("degenerate arc (collinear)",
       [("A", (0, 0), (1, 0), (2, 0)), ("C", (2, 0), (0, 1)), ("C", (0, 1), (0, 0))],
       expect="DEGENERATE")

emit()
emit("## Rotation sweep (I3): each ring rotated through all offsets keeps its class.")
for nm, ring in (("square", SQUARE), ("bowtie", BOWTIE), ("pentagon", PENT),
                 ("arc-chord-cross", ARC_CHORD_CROSS)):
    base = verdict_class(run(ring))
    ok = all(verdict_class(run(ring[k:] + ring[:k])) == base for k in range(len(ring)))
    emit(f"  [{nm}] base={base} rotation-stable={ok}")
    if not ok:
        violations += 1
        emit("    !! I3_ROTATION_CHANGED_VERDICT")

emit()
if violations:
    emit(f"::error::RING_SIMPLE violated {violations} invariant(s)/expectation(s).")
    sys.exit(1)
emit("# All invariants (I1 witness-sound, I2 curated, I3 rotation) hold.")
