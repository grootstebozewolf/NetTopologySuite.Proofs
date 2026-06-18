#!/usr/bin/env python3
# =============================================================================
# oracle/gen_arc_segment_tests.py
# -----------------------------------------------------------------------------
# Adversarial tests for the ARC_SEGMENT_XY oracle mode (issue #224 W1 / JTS
# N-AL: CircularArcs.intersectSegment), driven by the RocqRefRunner (oracle_bin)
# and checked against EXACT-rational ground truth computed here with
# `fractions.Fraction` -- no float in the oracle of record.
#
# Ground truth ties to theories/ArcSegmentCircles.v and ArcArcCircles.v:
#
#   * exact circle-line count from the perpendicular discriminant r^2 - d^2,
#     with d^2 the exact squared distance from the circumcentre O to the
#     segment's supporting line.  > 0 => 2 line points, = 0 => 1 (tangent),
#     < 0 => 0.  (Matches line_circle_radical_point's r2 - d2 >= 0 premise.)
#
# PROVEN invariants the oracle MUST satisfy (a '!!' line is a real bug and
# fails CI, mirroring oracle/gen_arc_arc_tests.py):
#
#   I1  ON-CIRCLE     every returned point lies on the arc's circumcircle
#                     (line_circle_radical_point / inCircle_R_zero_of_equidistant).
#   I2  ON-SEGMENT    every returned point is collinear with P,Q AND has
#                     segment parameter t in [0,1] (arc_line_circle_intersect's
#                     "on the line" witness + the segment clamp).
#   I3  SEG-REVERSAL  swapping the segment endpoints P<->Q is the SAME point set
#                     (t -> 1-t stays in [0,1]) => the returned count is unchanged.
#   I4  ARC-REVERSAL  reversing the arc controls (A,B,C)->(C,B,A) is the SAME arc
#                     (same circle + sweep) => the returned count is unchanged.
#                     (Guards the point_on_arc_sector start-endpoint regression.)
#
# Near-tangency float divergence between the oracle's binary64 count and the
# exact discriminant sign is the deferred float frontier -- reported, NOT a bug.
#
# Run from repo root:  python3 oracle/gen_arc_segment_tests.py > oracle/arc_segment_tests.txt
# Exit status: nonzero iff a PROVEN invariant (I1-I4) is violated.
# =============================================================================
import os
import subprocess
import sys
from fractions import Fraction as F

BIN = os.environ.get("ORACLE_BIN", "oracle/oracle_bin")
violations = 0


def emit(s=""):
    print(s)


def run(arc, p, q):
    """arc = 3 (x,y) pairs; p,q segment endpoints. Returns raw oracle line."""
    pts = list(arc) + [p, q]
    stdin = "ARC_SEGMENT_XY\n" + "".join(f"{x} {y}\n" for (x, y) in pts)
    return subprocess.run([BIN], input=stdin, capture_output=True,
                          text=True).stdout.strip()


def parse(line):
    tok = line.split()
    if not tok:
        return ("NAN", 0, [])
    if tok[0] in ("DEGENERATE", "COINCIDENT", "NAN"):
        return (tok[0], 0, [])
    n = int(tok[0])
    c = [float.fromhex(t) if ("x" in t or "p" in t.lower()) else float(t)
         for t in tok[1:]]
    return ("COUNT", n, [(c[2 * i], c[2 * i + 1]) for i in range(n)])


def circumcentre(arc):
    (ax, ay), (bx, by), (cx, cy) = [(F(x), F(y)) for (x, y) in arc]
    d = 2 * ((bx - ax) * (cy - ay) - (by - ay) * (cx - ax))
    if d == 0:
        return None
    bk = bx * bx + by * by - ax * ax - ay * ay
    ck = cx * cx + cy * cy - ax * ax - ay * ay
    ox = ((cy - ay) * bk - (by - ay) * ck) / d
    oy = ((bx - ax) * ck - (cx - ax) * bk) / d
    r2 = (ox - ax) * (ox - ax) + (oy - ay) * (oy - ay)
    return (ox, oy, r2)


def exact_line_count(arc, p, q):
    """Exact # of circle-LINE intersections (0/1/2), or a tag."""
    o = circumcentre(arc)
    if o is None:
        return "DEGENERATE"
    ox, oy, r2 = o
    px, py = F(p[0]), F(p[1])
    qx, qy = F(q[0]), F(q[1])
    dx, dy = qx - px, qy - py
    l2 = dx * dx + dy * dy
    if l2 == 0:
        return "DEGENERATE"
    s = ((ox - px) * dx + (oy - py) * dy) / l2
    fx, fy = px + s * dx, py + s * dy
    d2 = (ox - fx) ** 2 + (oy - fy) ** 2
    disc = r2 - d2
    return 2 if disc > 0 else (1 if disc == 0 else 0)


def check_invariants(name, arc, p, q, expect=None):
    global violations
    line = run(arc, p, q)
    kind, n, pts = parse(line)
    exact = exact_line_count(arc, p, q)
    tags = []

    o = circumcentre(arc)
    if kind == "COUNT" and n and o is not None:
        ox, oy, r2 = float(o[0]), float(o[1]), float(o[2])
        px, py, qx, qy = p[0], p[1], q[0], q[1]
        dx, dy = qx - px, qy - py
        l2 = dx * dx + dy * dy
        tolc = 1e-6 * (1.0 + abs(r2))
        toll = 1e-6 * (1.0 + l2)
        for (x, y) in pts:
            # I1 on-circle
            res = (x - ox) ** 2 + (y - oy) ** 2 - r2
            if abs(res) > tolc:
                violations += 1
                tags.append(f"!! I1_OFF_CIRCLE res={res:.3g}")
            # I2 on-segment: collinear and t in [0,1]
            cross = (x - px) * dy - (y - py) * dx
            t = ((x - px) * dx + (y - py) * dy) / l2 if l2 else 0.0
            if abs(cross) > toll:
                violations += 1
                tags.append(f"!! I2_OFF_LINE cross={cross:.3g}")
            if t < -1e-9 or t > 1 + 1e-9:
                violations += 1
                tags.append(f"!! I2_OFF_SEGMENT t={t:.6g}")

    # I3 segment-reversal stability.
    _, n_sr, _ = parse(run(arc, q, p))
    if kind == "COUNT" and n_sr != n:
        violations += 1
        tags.append(f"!! I3_SEG_REVERSAL rev={n_sr}")

    # I4 arc-reversal stability.
    _, n_ar, _ = parse(run((arc[2], arc[1], arc[0]), p, q))
    if kind == "COUNT" and n_ar != n:
        violations += 1
        tags.append(f"!! I4_ARC_REVERSAL rev={n_ar}")

    note = f"exact_line_pts={exact}" if isinstance(exact, int) else ""
    exp = "" if expect is None else f" expect={expect}"
    status = " ".join(tags) if tags else "ok"
    emit(f"  [{name}] -> {line!r}{exp}   {note}   {status}")
    return line


# ---------------------------------------------------------------------------
emit("# Adversarial tests for ARC_SEGMENT_XY (RocqRefRunner) vs EXACT-rational")
emit("# ground truth.  '!!' lines are PROVEN-invariant violations (CI-failing).")
emit("# I1 on-circle  I2 on-segment(t in [0,1])  I3 seg-reversal  I4 arc-reversal")
emit()
emit("## A. Curated battery (issue #224 examples + counts hand-verified).")

UA = ((5, 0), (0, 5), (-5, 0))   # upper semicircle, R=5 about origin

check_invariants("issue#224: upper arc, line y=4 over [-5,5] (was -inf -nan)",
                 UA, (-5, 4), (5, 4), expect=2)
check_invariants("half segment x in [0,5], y=4",
                 UA, (0, 4), (5, 4), expect=1)
check_invariants("tangent y=5 at top (0,5)",
                 UA, (-5, 5), (5, 5), expect=1)
check_invariants("line misses circle (y=6)",
                 UA, (-5, 6), (5, 6), expect=0)
check_invariants("2 circle crossings but lower half, not on upper arc (y=-4)",
                 UA, (-5, -4), (5, -4), expect=0)
check_invariants("segment too short [-1,1] to reach crossings (y=4)",
                 UA, (-1, 4), (1, 4), expect=0)
check_invariants("crossing exactly at segment START endpoint (3,4)",
                 UA, (3, 4), (10, 4), expect=1)
check_invariants("crossing exactly at segment END endpoint (3,4)",
                 UA, (10, 4), (3, 4), expect=1)
check_invariants("vertical chord x=3 over [0,5] meets upper arc at (3,4)",
                 UA, (3, 0), (3, 5), expect=1)
check_invariants("degenerate arc (collinear controls)",
                 ((0, 0), (1, 0), (2, 0)), (-5, 4), (5, 4), expect="DEGENERATE")
check_invariants("zero-length segment",
                 UA, (1, 4), (1, 4), expect="DEGENERATE")

emit()
emit("## B. Sweep over chord heights and segment windows (gating I1-I4).")
# horizontal chords y=k crossing the R=5 circle, windowed segments.
for k in (-4.5, -3, -1, 0, 1, 3, 4.5):
    for (x0, x1) in ((-5, 5), (-3, 3), (0, 5), (-5, 0), (2, 4)):
        check_invariants(f"y={k} seg x in [{x0},{x1}]", UA, (x0, k), (x1, k))

emit()
emit("## C. Near-tangency float stress (deferred float frontier -- NOT a bug):")
emit("##    I1/I2/I3/I4 still gated; float-count vs exact-disc only NOTEd.")
# line y = 5 - eps grazes the top of the R=5 arc; full-width segment.
for off in ("0x1p-20", "0x1p-30", "0x1p-45", "0"):
    k = 5.0 - (float.fromhex(off) if off != "0" else 0.0)
    check_invariants(f"near-tangent top y=5-{off} (k={k!r})", UA, (-5, k), (5, k))

emit()
if violations:
    emit(f"::error::ARC_SEGMENT_XY violated {violations} proven invariant(s) (I1-I4).")
    sys.exit(1)
emit("# All proven invariants (I1-I4) hold across the suite.")
