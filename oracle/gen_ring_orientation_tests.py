#!/usr/bin/env python3
# =============================================================================
# oracle/gen_ring_orientation_tests.py
# -----------------------------------------------------------------------------
# Adversarial tests for the RING_ORIENTATION oracle mode (V-CP / CP_VALID sector
# orientation, JTS #1195 §7).  The oracle emits the TRUE signed area of a curve
# ring (chord shoelace + per-arc signed circular-segment area) -> CCW / CW.
#
# Invariants gated (a '!!' line fails CI):
#   I1  KNOWN-ORIENTATION : oracle CCW/CW == hand-derived orientation for curated
#       rings (square, upper-semicircle region, full circle, an arc-dominated
#       ring) -- the soundness gate; the semicircle/arc-dominated cases are where
#       the inscribed chord polygon is degenerate/wrong but the true sign holds.
#   I2  REVERSAL          : reversing the ring (segment order + each segment's
#       endpoints) flips CCW<->CW.
#   I3  AGREEMENT         : oracle CCW/CW == sign of an independent Python
#       recompute of the same true signed area.
#   I4  TRUE-vs-INSCRIBED : on the semicircle the inscribed (connection-polygon)
#       signed area is ~0 (cannot decide), while the true/oracle sign is CCW --
#       documents the bug class arc-awareness fixes.
#
# Run from repo root:
#   python3 oracle/gen_ring_orientation_tests.py > oracle/ring_orientation_tests.txt
# Exit status: nonzero iff a gated invariant fails.
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


def oracle(ring):
    stdin = "RING_ORIENTATION\n%d\n%s\n" % (len(ring), "\n".join(seg_line(s) for s in ring))
    return subprocess.run([BIN], input=stdin, capture_output=True, text=True).stdout.strip().split()[0]


def circumcentre(a, b, c):
    (ax, ay), (bx, by), (cx, cy) = [(F(p[0]), F(p[1])) for p in (a, b, c)]
    d = 2 * (ax * (by - cy) + bx * (cy - ay) + cx * (ay - by))
    if d == 0:
        return None
    na = ax * ax + ay * ay
    nb = bx * bx + by * by
    nc = cx * cx + cy * cy
    ox = (na * (by - cy) + nb * (cy - ay) + nc * (ay - by)) / d
    oy = (na * (cx - bx) + nb * (ax - cx) + nc * (bx - ax)) / d
    r2 = (ax - ox) ** 2 + (ay - oy) ** 2
    return (ox, oy, r2)


def true_signed_area2(ring):
    """Independent recompute matching the oracle: chord shoelace + arc bulges."""
    s2 = 0.0
    for seg in ring:
        if seg[0] == "C":
            (px, py), (qx, qy) = seg[1], seg[2]
            s2 += px * qy - py * qx
            continue
        a, b, c = seg[1], seg[2], seg[3]
        s2 += a[0] * c[1] - a[1] * c[0]      # chord a->c shoelace term
        o = circumcentre(a, b, c)
        if o is None:
            continue                          # degenerate arc = its chord, zero bulge
        ox, oy, r2 = o
        ax, ay = F(a[0]), F(a[1])
        cx, cy = F(c[0]), F(c[1])
        cos_full = ((ax - ox) * (cx - ox) + (ay - oy) * (cy - oy)) / r2
        s = math.sqrt(max(0.0, float((1 - cos_full) / 2)))
        t0 = 2 * math.asin(min(1.0, s))
        # major flag (arc_invariants_q): b and O on the same side of chord a->c
        def orient_ac(X):
            return (cx - ax) * (F(X[1]) - ay) - (cy - ay) * (F(X[0]) - ax)
        sob = 1 if orient_ac(b) > 0 else (-1 if orient_ac(b) < 0 else 0)
        soo = 1 if orient_ac((ox, oy)) > 0 else (-1 if orient_ac((ox, oy)) < 0 else 0)
        major = 1 if (soo != 0 and sob == soo) else 0
        theta = 2 * math.pi - t0 if major == 1 else t0
        # sweep sign = orientation of control points (a,b,c)
        orient_abc = (F(b[0]) - ax) * (cy - ay) - (F(b[1]) - ay) * (cx - ax)
        sb = 1.0 if orient_abc > 0 else (-1.0 if orient_abc < 0 else 0.0)
        s2 += sb * float(r2) * (theta - math.sin(theta))
    return s2


def inscribed_signed_area2(ring):
    """Connection-polygon shoelace only (no bulge) -- the inscribed proxy."""
    s2 = 0.0
    for seg in ring:
        p = seg[1]
        q = seg[2] if seg[0] == "C" else seg[3]
        s2 += p[0] * q[1] - p[1] * q[0]
    return s2


def reverse_ring(ring):
    out = []
    for seg in reversed(ring):
        if seg[0] == "C":
            out.append(("C", seg[2], seg[1]))
        else:
            out.append(("A", seg[3], seg[2], seg[1]))
    return out


# --- curated rings ---------------------------------------------------------
SQUARE_CCW = [("C", (0, 0), (10, 0)), ("C", (10, 0), (10, 10)),
              ("C", (10, 10), (0, 10)), ("C", (0, 10), (0, 0))]
SEMI = [("A", (5, 0), (0, 5), (-5, 0)), ("C", (-5, 0), (5, 0))]            # CCW half-disk
CIRCLE = [("A", (5, 0), (0, 5), (-5, 0)), ("A", (-5, 0), (0, -5), (5, 0))]  # CCW disk
# arc-dominated: a chord then a big arc bulging down -> inscribed polygon ~0
DOWN_BULGE = [("C", (0, 0), (10, 0)), ("A", (10, 0), (5, -4), (0, 0))]


def assess(name, ring, expect):
    global violations
    got = oracle(ring)
    tags = []
    if got != expect:
        violations += 1
        tags.append(f"!! I1_EXPECTED_{expect}_GOT_{got}")
    # I3 agreement with independent recompute
    s2 = true_signed_area2(ring)
    recompute = "CCW" if s2 > 1e-9 else ("CW" if s2 < -1e-9 else "DEGENERATE")
    if got != recompute:
        violations += 1
        tags.append(f"!! I3_DISAGREE oracle={got} recompute={recompute} (S2={s2:.4g})")
    # I2 reversal flips
    rev = oracle(reverse_ring(ring))
    flip = {"CCW": "CW", "CW": "CCW", "DEGENERATE": "DEGENERATE"}
    if rev != flip.get(got, "?"):
        violations += 1
        tags.append(f"!! I2_REVERSAL got={got} rev={rev}")
    emit(f"  [{name}] -> {got} (S2={s2:.4g})   {' '.join(tags) if tags else 'ok'}")


# ---------------------------------------------------------------------------
emit("# Adversarial tests for RING_ORIENTATION (RocqRefRunner), V-CP / JTS #1195 §7.")
emit("# TRUE signed area (chord shoelace + arc sector areas) -> CCW/CW.  I1 known")
emit("# orientation, I2 reversal flips, I3 agreement vs independent recompute,")
emit("# I4 true-vs-inscribed.  '!!' lines are gated-invariant violations.")
emit()
emit("## I1/I2/I3 curated rings.")
assess("square CCW", SQUARE_CCW, "CCW")
assess("square CW (reversed)", reverse_ring(SQUARE_CCW), "CW")
assess("upper-semicircle region (arc+chord) CCW", SEMI, "CCW")
assess("full circle (2 arcs) CCW", CIRCLE, "CCW")
assess("arc-dominated down-bulge ring CW (region below x-axis)", DOWN_BULGE, "CW")

emit()
emit("## I4 TRUE-vs-INSCRIBED (arc-awareness matters):")
for nm, ring in (("semicircle", SEMI), ("down-bulge", DOWN_BULGE)):
    insc = inscribed_signed_area2(ring)
    tru = true_signed_area2(ring)
    o = oracle(ring)
    note = "inscribed≈0/undecidable, true decides" if abs(insc) < 1e-9 else "differ"
    emit(f"  [{nm}] inscribed_S2={insc:.4g}  true_S2={tru:.4g}  oracle={o}   ({note})")
    if (tru > 0) != (o == "CCW"):
        violations += 1
        emit("    !! I4_ORACLE_NOT_TRUE")

emit()
if violations:
    emit(f"::error::RING_ORIENTATION violated {violations} invariant(s).")
    sys.exit(1)
emit("# All invariants (I1 known, I2 reversal, I3 agreement, I4 true-vs-inscribed) hold.")
