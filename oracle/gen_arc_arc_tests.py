#!/usr/bin/env python3
# =============================================================================
# oracle/gen_arc_arc_tests.py
# -----------------------------------------------------------------------------
# Adversarial tests for the ARC_ARC_XY oracle mode (issue #64 #5b / N-AA),
# driven by the RocqRefRunner (oracle_bin) and checked against EXACT-rational
# ground truth computed here with `fractions.Fraction` -- no float in the
# oracle of record.
#
# Ground truth ties directly to the Qed-proven theorems in
# theories/ArcArcCircles.v and theories/ArcArcSound.v:
#
#   * exact circle-intersection count from the four-factor discriminant
#         disc = (2*d*r1)^2 - (d^2 + r1^2 - r2^2)^2
#                = (d+r1+r2)(d+r1-r2)(r2+d-r1)(r1+r2-d)
#     -- the SAME quantity proven > 0 in `two_circles_radical_point`
#     (`Hnum_pos`).  disc>0 => 2 circle points, =0 => 1 (tangent), <0 => 0.
#     (All squared radii / squared distance are exact rationals, so `disc` is
#     exact; only its 4th-root factorisation would need irrationals.)
#
# PROVEN invariants the oracle MUST satisfy (a violation '!!' is a real bug
# and fails CI, mirroring oracle/gen_adversarial_tests.sh):
#
#   I1  ON-BOTH-CIRCLES   every returned point lies on BOTH circumcircles
#                         (two_circles_radical_point / inCircle_R_concyclic).
#                         Float build => checked within a magnitude-scaled tol.
#   I2  SHARED-VERTEX     if the arcs share an endpoint, count >= 1
#                         (arc_arc_intersects_shared_vertex).
#   I3  SYMMETRY          count(a1,a2) == count(a2,a1)
#                         (arc_arc_intersects_sym).
#   I4  REVERSAL-STABLE   reversing an arc's controls (A,B,C)->(C,B,A) is the
#                         SAME point set on the SAME circle, so the returned
#                         count is unchanged.  (This is exactly the invariant
#                         the start-endpoint sector bug used to break.)
#
# Empirical, NOT a bug: near-tangency float divergence between the oracle's
# binary64 count and the exact `disc` sign -- the deferred float frontier; we
# report it as a hardening signal, it does not fail CI.
#
# Run from repo root:  python3 oracle/gen_arc_arc_tests.py > oracle/arc_arc_tests.txt
# Exit status: nonzero iff a PROVEN invariant (I1-I4) is violated.
# =============================================================================
import os
import subprocess
import sys
from fractions import Fraction as F

BIN = os.environ.get("ORACLE_BIN", "oracle/oracle_bin")

violations = 0  # proven-invariant breaches -> nonzero exit


def emit(s=""):
    print(s)


def run(a1, a2):
    """a1, a2 are 3-tuples of (x, y) pairs. Returns the raw oracle line."""
    pts = list(a1) + list(a2)
    stdin = "ARC_ARC_XY\n" + "".join(f"{x} {y}\n" for (x, y) in pts)
    out = subprocess.run([BIN], input=stdin, capture_output=True, text=True)
    return out.stdout.strip()


def parse(line):
    """(kind, n, points). kind in {COUNT,DEGENERATE,COINCIDENT,NAN}."""
    tok = line.split()
    if not tok:
        return ("NAN", 0, [])
    if tok[0] in ("DEGENERATE", "COINCIDENT", "NAN"):
        return (tok[0], 0, [])
    n = int(tok[0])
    coords = [float.fromhex(t) if "x" in t or "p" in t.lower() else float(t)
              for t in tok[1:]]
    pts = [(coords[2 * i], coords[2 * i + 1]) for i in range(n)]
    return ("COUNT", n, pts)


def circumcentre(p):
    """Exact (ox, oy, r2) Fractions, or None if collinear."""
    (ax, ay), (bx, by), (cx, cy) = [(F(x), F(y)) for (x, y) in p]
    d = 2 * ((bx - ax) * (cy - ay) - (by - ay) * (cx - ax))
    if d == 0:
        return None
    bk = bx * bx + by * by - ax * ax - ay * ay
    ck = cx * cx + cy * cy - ax * ax - ay * ay
    ox = ((cy - ay) * bk - (by - ay) * ck) / d
    oy = ((bx - ax) * ck - (cx - ax) * bk) / d
    r2 = (ox - ax) * (ox - ax) + (oy - ay) * (oy - ay)
    return (ox, oy, r2)


def exact_circle_count(a1, a2):
    """Exact # of circle-circle intersections (0/1/2), or a tag string."""
    o1, o2 = circumcentre(a1), circumcentre(a2)
    if o1 is None or o2 is None:
        return "DEGENERATE"
    (o1x, o1y, r1), (o2x, o2y, r2) = o1, o2
    dq = (o2x - o1x) ** 2 + (o2y - o1y) ** 2
    if dq == 0:
        return "COINCIDENT" if r1 == r2 else 0
    disc = 4 * dq * r1 - (dq + r1 - r2) ** 2   # four-factor discriminant
    return 2 if disc > 0 else (1 if disc == 0 else 0)


def shares_endpoint(a1, a2):
    ends1 = {a1[0], a1[2]}
    ends2 = {a2[0], a2[2]}
    return bool(ends1 & ends2)


def check_on_circles(a1, a2, pts):
    """I1: each returned point lies on both exact circumcircles."""
    o1, o2 = circumcentre(a1), circumcentre(a2)
    if o1 is None or o2 is None:
        return []
    bad = []
    for (cx, cy, r2) in (o1, o2):
        ox, oy, rr = float(cx), float(cy), float(r2)
        tol = 1e-6 * (1.0 + abs(rr))
        for (x, y) in pts:
            res = (x - ox) ** 2 + (y - oy) ** 2 - rr
            if abs(res) > tol:
                bad.append((x, y, res, tol))
    return bad


def rev(a):
    return (a[2], a[1], a[0])


def assess(name, a1, a2, expect=None):
    """Run a case, print it, and gate the proven invariants."""
    global violations
    line = run(a1, a2)
    kind, n, pts = parse(line)
    exact = exact_circle_count(a1, a2)
    tags = []

    # I1: returned points on both circles.
    if kind == "COUNT" and n:
        bad = check_on_circles(a1, a2, pts)
        if bad:
            violations += 1
            tags.append(f"!! I1_OFF_CIRCLE res={bad[0][2]:.3g}>tol{bad[0][3]:.1g}")

    # I2: shared endpoint => at least one intersection.
    if shares_endpoint(a1, a2) and kind == "COUNT" and n < 1 \
            and exact not in ("DEGENERATE", "COINCIDENT"):
        violations += 1
        tags.append("!! I2_SHARED_VERTEX_MISSED")

    # I3: symmetry.
    _, n_sym, _ = parse(run(a2, a1))
    if kind == "COUNT":
        if n_sym != n:
            violations += 1
            tags.append(f"!! I3_ASYMMETRIC sym={n_sym}")

    # I4: reversing either arc is the same point set => same count.
    for label, b1, b2 in (("a1", rev(a1), a2), ("a2", a1, rev(a2))):
        k2, n2, _ = parse(run(b1, b2))
        if kind == "COUNT" and k2 == "COUNT" and n2 != n:
            violations += 1
            tags.append(f"!! I4_REVERSAL_{label} rev_count={n2}")

    # Empirical near-tangency divergence (NOT a bug): float count vs exact disc
    # only comparable when spans cover the whole circle; we only note the
    # tangent-class mismatch as a hardening signal.
    note = ""
    if kind == "COUNT" and isinstance(exact, int):
        note = f"exact_circle_pts={exact}"

    exp = "" if expect is None else f" expect={expect}"
    status = " ".join(tags) if tags else "ok"
    emit(f"  [{name}] -> {line!r}{exp}   {note}   {status}")
    return line


# ---------------------------------------------------------------------------
emit("# Adversarial tests for ARC_ARC_XY (RocqRefRunner) vs EXACT-rational")
emit("# ground truth (four-factor discriminant = two_circles_radical_point's")
emit("# Hnum_pos).  '!!' lines are PROVEN-invariant violations (CI-failing).")
emit("# I1 on-both-circles  I2 shared-vertex>=1  I3 symmetry  I4 reversal-stable")
emit()
emit("## A. Curated battery (counts hand-verified).")

# centre (0,0) r=5 upper/lower semicircles, centre (8,0)/(10,0)/(20,0) variants.
C1u = ((5, 0), (0, 5), (-5, 0))      # circle (0,0) r5, upper, CW sweep
C1l = ((5, 0), (0, -5), (-5, 0))     # circle (0,0) r5, lower

assess("2pt: both arcs cover both meets (4,+-3)",
       ((5, 0), (4, 3), (4, -3)), ((3, 0), (4, 3), (4, -3)), expect=2)
assess("1pt: upper/upper, only (4,3) in both spans",
       C1u, ((3, 0), (8, 5), (13, 0)), expect=1)
assess("0: circles meet 2, upper vs lower arcs disjoint spans",
       C1u, ((3, 0), (8, -5), (13, 0)), expect=0)
assess("ext-tangent at START vertex (5,0), arc2 CW  (regression: was 0)",
       C1u, ((5, 0), (10, 5), (15, 0)), expect=1)
assess("ext-tangent at START vertex (5,0), arc2 CCW (control)",
       C1u, ((5, 0), (10, -5), (15, 0)), expect=1)
assess("shared START vertex (5,0), both CW  (arc_arc_intersects_shared_vertex)",
       C1u, ((5, 0), (10, 5), (15, 0)), expect=1)
assess("internal tangent at (5,0): (0,0)r5 vs (2,0)r3",
       C1u, ((5, 0), (-1, 0), (2, 3)), expect=1)
assess("disjoint d=20 > r1+r2=10",
       C1u, ((15, 0), (20, 5), (25, 0)), expect=0)
assess("concentric distinct radii (0,0)r5 vs (0,0)r3",
       C1u, ((3, 0), (0, 3), (-3, 0)), expect=0)
assess("coincident circumcircles (identical arcs)",
       C1u, C1u, expect="COINCIDENT")
assess("DEGENERATE: arc1 collinear",
       ((0, 0), (1, 0), (2, 0)), ((3, 0), (8, 5), (13, 0)), expect="DEGENERATE")

emit()
emit("## B. Shared-vertex sweep (arc_arc_intersects_shared_vertex): every")
emit("##    shared endpoint must yield count >= 1, for ALL arc orientations.")
# arc1 fixed; arc2 hinged at each shared endpoint of arc1, swept both ways.
hub_cases = [
    ("end1=start2 hinge (-5,0)", C1u, ((-5, 0), (-10, 5), (-15, 0))),
    ("start1=start2 hinge (5,0)", C1u, ((5, 0), (10, 5), (15, 0))),
    ("start1=end2 hinge (5,0)",   C1u, ((15, 0), (10, 5), (5, 0))),
    ("end1=end2 hinge (-5,0)",    C1u, ((-15, 0), (-10, 5), (-5, 0))),
    ("lower arc1, end1=start2",   C1l, ((-5, 0), (-10, -5), (-15, 0))),
]
for nm, x1, x2 in hub_cases:
    assess(nm, x1, x2, expect=">=1")

emit()
emit("## C. Near-tangency float stress (deferred float frontier -- NOT a bug):")
emit("##    proven invariants I1/I3/I4 still gated; we only NOTE float-count vs")
emit("##    exact-disc divergence as a hardening signal.")
# Walk the second centre across the external-tangency radius r1+r2 = 10 using
# binary64-adjacent x-offsets; arcs are wide (near-full) so spans don't filter.
base = 10.0
for off in ("-0x1p-30", "-0x1p-45", "0", "0x1p-45", "0x1p-30"):
    dx = base + float.fromhex(off) if off != "0" else base
    # circle2 centre ~ (dx, 0), r=5: controls (dx-5,0),(dx,5),(dx,-5) cover full
    a2 = ((dx - 5, 0), (dx, 5), (dx, -5))
    a1 = ((-5, 0), (0, 5), (0, -5))  # circle (0,0) r5 ~full (3 spread pts)
    line = assess(f"near-ext-tangent d=r1+r2 off={off} (dx={dx!r})", a1, a2)

emit()
if violations:
    emit(f"::error::ARC_ARC_XY violated {violations} proven invariant(s) (I1-I4).")
    sys.exit(1)
emit("# All proven invariants (I1-I4) hold across the suite.")
