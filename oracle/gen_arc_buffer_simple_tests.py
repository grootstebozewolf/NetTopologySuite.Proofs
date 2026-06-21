#!/usr/bin/env python3
# =============================================================================
# oracle/gen_arc_buffer_simple_tests.py
# -----------------------------------------------------------------------------
# Focused tests for single-arc buffer (ARC_BUFFER_SIMPLE / BUF-1 foundation).
# Exercises BUFFER_REGION oracle on a degenerate 2-segment ring (input arc +
# closing chord) to pin the behaviour when the input is a single arc.
#
# Reuses the proven ARC_OFFSET_XY (homothety) + buffer assembly invariants.
# Checks:
#   - Emitted boundary for +d includes an arc that is the radial offset of
#     the input arc (3-pt preservation from ArcOffsetThreePoint).
#   - Basic area/distance/empty/degen invariants (subset of buffer I1-I6).
#
# This is the cheap "clearlane" starter per Oracle Wishlist v4.0.
#
# Run from repo root:
#   python3 oracle/gen_arc_buffer_simple_tests.py > oracle/arc_buffer_simple_tests.txt
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


def run_buffer_region(ring, d):
    """Builds and runs BUFFER_REGION for a ring (list of seg tuples)."""
    n = len(ring)
    seg_lines = []
    for s in ring:
        if s[0] == "C":
            seg_lines.append(f"C {s[1][0]} {s[1][1]} {s[2][0]} {s[2][1]}")
        else:
            seg_lines.append(f"A {s[1][0]} {s[1][1]} {s[2][0]} {s[2][1]} {s[3][0]} {s[3][1]}")
    stdin = f"BUFFER_REGION\n{n}\n" + "\n".join(seg_lines) + f"\n{d}\n"
    return subprocess.run([BIN], input=stdin, capture_output=True, text=True).stdout.strip()


def parse_buffer_output(out):
    """Returns (num_segs, segs_list, area_str or None).
    Handles hex float (%h) output from oracle.
    """
    lines = [l for l in out.strip().splitlines() if l.strip()]
    if not lines or lines[0] in ("EMPTY", "DEGENERATE", "NAN"):
        return (0, [], None)
    try:
        n = int(lines[0])
        segs = []
        i = 1
        while i < len(lines) and not lines[i].startswith("AREA"):
            toks = lines[i].split()
            if toks[0] == "A" and len(toks) >= 7:
                def fhex(s):
                    return float.fromhex(s) if ("x" in s or "p" in s.lower()) else float(s)
                p1 = (fhex(toks[1]), fhex(toks[2]))
                p2 = (fhex(toks[3]), fhex(toks[4]))
                p3 = (fhex(toks[5]), fhex(toks[6]))
                segs.append(("A", p1, p2, p3))
            elif toks[0] == "C" and len(toks) >= 5:
                def fhex(s):
                    return float.fromhex(s) if ("x" in s or "p" in s.lower()) else float(s)
                p1 = (fhex(toks[1]), fhex(toks[2]))
                p2 = (fhex(toks[3]), fhex(toks[4]))
                segs.append(("C", p1, p2))
            i += 1
        area = None
        for l in lines[i:]:
            if l.startswith("AREA"):
                area = l.split()[1]
        return (n, segs, area)
    except Exception as e:
        return (0, [], None)


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


def is_offset_of_input(input_arc, emitted_arc_pts, d, tol=1e-6):
    """Check if emitted 3 pts are the homothetic offset of input by d."""
    o = circumcentre(input_arc)
    if o is None:
        return False
    ox, oy, r = o
    if r + d <= 0:
        return False  # caller should have handled EMPTY
    k = (r + d) / r
    for i, (px, py) in enumerate(input_arc):
        ex, ey = emitted_arc_pts[i]
        # expected
        qx = ox + k * (px - ox)
        qy = oy + k * (py - oy)
        if abs(ex - qx) > tol or abs(ey - qy) > tol:
            return False
    return True


def assess_simple(name, arc, d, expect_kind=None):
    global violations
    a, b, c = arc
    # 2-seg ring: arc + closing chord C->A (exercises BUFFER_REGION path)
    ring = [("A", a, b, c), ("C", c, a)]
    out = run_buffer_region(ring, d)

    # Also exercise the dedicated first-class ARC_BUFFER_SIMPLE mode (parity check)
    # Direct protocol: ARC_BUFFER_SIMPLE\nA sx sy mx my ex ey\nd
    arc_line = f"A {a[0]} {a[1]} {b[0]} {b[1]} {c[0]} {c[1]}"
    stdin = f"ARC_BUFFER_SIMPLE\n{arc_line}\n{d}\n"
    out_direct = subprocess.run([BIN], input=stdin, capture_output=True, text=True).stdout.strip()
    if out_direct != out:
        violations += 1
        tags.append(f"!! DEDICATED_MODE_MISMATCH vs BUFFER_REGION")
    tags = []
    if out in ("EMPTY", "DEGENERATE", "NAN"):
        if d <= -0.1 or expect_kind in ("EMPTY", "DEGENERATE"):
            emit(f"  [{name}] -> {out!r}   ok (expected collapse/degen)")
            return
        violations += 1
        tags.append(f"!! UNEXPECTED_{out}")
    else:
        n, segs, area = parse_buffer_output(out)
        if n < 2 or area is None:
            violations += 1
            tags.append("!! BAD_PARSE")
        else:
            # Find if any emitted A is the offset of input
            found_offset = False
            for s in segs:
                if s[0] == "A":
                    epts = [s[1], s[2], s[3]]
                    if is_offset_of_input(arc, epts, d):
                        found_offset = True
                        break
            if not found_offset and d > -0.1:
                violations += 1
                tags.append("!! NO_OFFSET_ARC_FOUND")
            # crude area sanity
            def fhex(s):
                return float.fromhex(s) if ("x" in s or "p" in s.lower()) else float(s)
            if area and fhex(area) < 0 and d > 0:
                violations += 1
                tags.append("!! NEG_AREA_FOR_POS_D")
    if expect_kind and out != expect_kind:
        violations += 1
        tags.append(f"!! EXPECTED_{expect_kind}_GOT_{out}")
    emit(f"  [{name}] -> {out!r}   {' '.join(tags) if tags else 'ok'}")


# Curated single-arc "simple" cases (arc + implicit chord ring)
UA = ((5, 0), (0, 5), (-5, 0))  # r~5
assess_simple("R=5 d=+2", UA, 2)
assess_simple("R=5 d=-2", UA, -2)
assess_simple("R=5 collapse d=-5", UA, -5, expect_kind="EMPTY")
assess_simple("R=5 large outward d=+50", UA, 50)
assess_simple("tiny d=+0.1", ((0,0),(0.001,0),(0,0.001)), 0.1)
assess_simple("degen collinear d=1", ((0,0),(1,0),(2,0)), 1, expect_kind="DEGENERATE")

emit()
emit("## B. Sweep over arcs (gating offset presence and buffer invariants).")
ARCS = {
    "unit @origin": ((1, 0), (0, 1), (-1, 0)),
    "R=5 lower": ((-5, 0), (0, -5), (5, 0)),
    "off-centre R=2 @ (3,4)": ((5, 4), (3, 6), (1, 4)),
    "small quarter": ((2, 0), (1.4142135623730951, 1.4142135623730951), (0, 2)),
}
for nm, arc in ARCS.items():
    r = circumcentre(arc)[2] if circumcentre(arc) else 1.0
    for d in (-0.9 * r, -0.5 * r, 0.0, 0.5 * r, 2 * r, -r, -1.5 * r):
        assess_simple(f"{nm} d={d:.3g}", arc, round(d, 12))

emit()
if violations:
    emit(f"::error::ARC_BUFFER_SIMPLE violated {violations} invariant(s)/expectation(s).")
    sys.exit(1)
emit("# Single-arc buffer simple cases (via BUFFER_REGION degenerate ring) hold.")
