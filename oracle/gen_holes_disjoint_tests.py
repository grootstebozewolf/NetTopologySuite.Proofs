#!/usr/bin/env python3
# =============================================================================
# oracle/gen_holes_disjoint_tests.py
# -----------------------------------------------------------------------------
# Adversarial tests for the HOLES_DISJOINT oracle mode (V-CP / CP_VALID
# holes-mutually-disjoint, JTS #1195 §7) -- the final CP_VALID slice.  Two hole
# rings are disjoint unless their BOUNDARIES meet or one is NESTED in the other.
#
# Invariants gated (a '!!' line fails CI):
#   I1  WITNESS-SOUND : a NOT_DISJOINT CROSS i j x y verdict exhibits a real
#       shared boundary point -- (x,y) lies on segment i of A AND segment j of
#       B (= CurvePolygonDisjoint.holes_not_disjoint_of_meet).
#   I2  CURATED       : hand-verified DISJOINT / CROSS / A_IN_B / B_IN_A cases
#       (separate squares, overlapping squares, nested square, far-apart arcs,
#       arc-ring touching a square).
#   I3  SYMMETRY      : disjointness is symmetric -- swapping the two rings keeps
#       DISJOINT, and flips A_IN_B <-> B_IN_A.
#
# Run from repo root:
#   python3 oracle/gen_holes_disjoint_tests.py > oracle/holes_disjoint_tests.txt
# Exit status: nonzero iff a gated invariant / curated expectation fails.
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


def seg_line(s):
    if s[0] == "C":
        return f"C {s[1][0]} {s[1][1]} {s[2][0]} {s[2][1]}"
    return f"A {s[1][0]} {s[1][1]} {s[2][0]} {s[2][1]} {s[3][0]} {s[3][1]}"


def run(ra, rb):
    stdin = "HOLES_DISJOINT\n%d\n%s\n%d\n%s\n" % (
        len(ra), "\n".join(seg_line(s) for s in ra),
        len(rb), "\n".join(seg_line(s) for s in rb))
    return subprocess.run([BIN], input=stdin, capture_output=True, text=True).stdout.strip()


def parse(line):
    t = line.split()
    if not t:
        return ("EMPTY", None)
    if t[0] == "DISJOINT":
        return ("DISJOINT", None)
    if t[0] == "NAN":
        return ("NAN", None)
    if t[0] == "NOT_DISJOINT":
        if t[1] == "CROSS":
            x = float.fromhex(t[4]) if ("x" in t[4] or "p" in t[4].lower()) else float(t[4])
            y = float.fromhex(t[5]) if ("x" in t[5] or "p" in t[5].lower()) else float(t[5])
            return ("CROSS", (int(t[2]), int(t[3]), x, y))
        return (t[1], None)   # A_IN_B / B_IN_A
    return ("?", None)


def cls(line):
    k, _ = parse(line)
    return "DISJOINT" if k == "DISJOINT" else ("NOT_DISJOINT" if k in ("CROSS", "A_IN_B", "B_IN_A") else k)


def circumcentre(a, b, c):
    (ax, ay), (bx, by), (cx, cy) = [(F(p[0]), F(p[1])) for p in (a, b, c)]
    d = 2 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by))
    if d == 0:
        return None
    na, nb, nc = ax * ax + ay * ay, bx * bx + by * by, cx * cx + cy * cy
    ox = (na * (by - cy) + nb * (cy - ay) + nc * (ay - by)) / d
    oy = (na * (cx - bx) + nb * (ax - cx) + nc * (bx - ax)) / d
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


def assess(name, ra, rb, expect):
    global violations
    line = run(ra, rb)
    k, data = parse(line)
    c = cls(line)
    tags = []
    if c != expect:
        violations += 1
        tags.append(f"!! I2_EXPECTED_{expect}_GOT_{c}")
    # I1 witness soundness for CROSS
    if k == "CROSS":
        i, j, x, y = data
        if not on_segment(ra[i], x, y):
            violations += 1
            tags.append(f"!! I1_WITNESS_OFF_A_seg{i}")
        if not on_segment(rb[j], x, y):
            violations += 1
            tags.append(f"!! I1_WITNESS_OFF_B_seg{j}")
    # I3 symmetry: swapping rings keeps DISJOINT / flips A_IN_B<->B_IN_A
    ksym, _ = parse(run(rb, ra))
    if c == "DISJOINT" and ksym != "DISJOINT":
        violations += 1
        tags.append(f"!! I3_ASYM swap={ksym}")
    if k == "A_IN_B" and ksym != "B_IN_A":
        violations += 1
        tags.append(f"!! I3_NEST_NOT_FLIPPED swap={ksym}")
    if k == "B_IN_A" and ksym != "A_IN_B":
        violations += 1
        tags.append(f"!! I3_NEST_NOT_FLIPPED swap={ksym}")
    emit(f"  [{name}] -> {line!r}   {' '.join(tags) if tags else 'ok'}")


# --- shapes ----------------------------------------------------------------
def sq(x0, y0, x1, y1):
    return [("C", (x0, y0), (x1, y0)), ("C", (x1, y0), (x1, y1)),
            ("C", (x1, y1), (x0, y1)), ("C", (x0, y1), (x0, y0))]


# arc-capped lens region (upper arc + chord), CCW
def lens(cx, r):
    return [("A", (cx + r, 0), (cx, r), (cx - r, 0)), ("C", (cx - r, 0), (cx + r, 0))]


# ---------------------------------------------------------------------------
emit("# Adversarial tests for HOLES_DISJOINT (RocqRefRunner), V-CP / JTS #1195 §7.")
emit("# Two hole rings disjoint unless boundaries meet or one is nested.")
emit("# I1 CROSS witness-sound, I2 curated, I3 symmetry.  '!!' = violation.")
emit()
assess("two separate squares", sq(0, 0, 2, 2), sq(5, 5, 7, 7), "DISJOINT")
assess("overlapping squares (boundaries cross)", sq(0, 0, 4, 4), sq(2, 2, 6, 6), "NOT_DISJOINT")
assess("small square nested in big", sq(3, 3, 4, 4), sq(0, 0, 10, 10), "NOT_DISJOINT")
assess("big square contains small (B_IN_A)", sq(0, 0, 10, 10), sq(3, 3, 4, 4), "NOT_DISJOINT")
assess("two far-apart arc lenses", lens(0, 2), lens(10, 2), "DISJOINT")
assess("arc lens overlapping a square", lens(0, 3), sq(-1, -1, 1, 4), "NOT_DISJOINT")
assess("arc lens nested in big square", lens(5, 1), sq(0, -2, 10, 5), "NOT_DISJOINT")
assess("two stacked squares sharing an edge line but apart", sq(0, 0, 2, 2), sq(0, 5, 2, 7), "DISJOINT")

emit()
if violations:
    emit(f"::error::HOLES_DISJOINT violated {violations} invariant(s)/expectation(s).")
    sys.exit(1)
emit("# All invariants (I1 witness-sound, I2 curated, I3 symmetry) hold.")
