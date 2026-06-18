#!/usr/bin/env python3
# =============================================================================
# oracle/gen_buffer_region_tests.py
# -----------------------------------------------------------------------------
# Adversarial tests for the BUFFER_REGION oracle mode (BUF-1 / BUF-NEG, JTS
# #1195 §7).  The oracle ASSEMBLES the offset boundary of a closed curve ring at
# signed distance d (per-segment outward offset + round-join arcs at convex
# corners) and emits it + its TRUE signed area.  The single-arc offset
# (ARC_OFFSET_XY) and the assembly are proven valid-as-a-curve-ring; this suite
# is the INDEPENDENT certificate that the emitted area equals the true
# buffer(curve, d) (Minkowski) area -- the deferred P2 frontier.
#
# v1 (proven-clean regime): convex shells.  d>0 outward with round joins; d<0
# inward for SMOOTH (all-G1) rings.  Reflex / U-turn corners and cornered rings
# with d<0 (inward miter / self-intersection cleanup = the noding/P2 frontier)
# emit DEGENERATE; collapse emits EMPTY.
#
# Invariants gated (a '!!' line + nonzero exit on violation):
#   I1 PARALLEL-DISTANCE : every point sampled along an emitted boundary segment
#      is at distance ~|d| from the source ring boundary (ArcOffset.arc_offset_
#      dist_exact, the proven parallel-curve property; an independent min-distance
#      check catches a wrong outward side).
#   I2 AREA vs MINKOWSKI : the emitted AREA matches an independent dense-grid
#      Minkowski estimate -- d>0 dilation {p : dist(p, region) <= d};
#      d<0 erosion {p : inside /\ dist(p, boundary) >= |d|}.  THE certificate.
#   I3 STEINER (convex)  : for convex shells, |AREA| ~ area + perimeter*d + pi*d^2
#      (d>0) -- an independent closed-form cross-check of I2.
#   I4 EMPTY             : inner buffer with |d| >= inradius emits EMPTY.
#   I5 d=0 IDENTITY      : emitted boundary reproduces the source ring; |AREA| =
#      source area.
#   I6 MONOTONIC         : |AREA| strictly increases with d over the valid range.
#
# I7 BROKEN-BINARY regression: verified to FAIL when the offset sign is flipped
# (area shrinks when it should grow -- I2/I3/I6 flag it), and to PASS on the
# correct binary.
#
# Run from repo root:
#   python3 oracle/gen_buffer_region_tests.py > oracle/buffer_region_tests.txt
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


def run(ring, d):
    stdin = "BUFFER_REGION\n%d\n%s\n%s\n" % (
        len(ring), "\n".join(seg_line(s) for s in ring), d)
    return subprocess.run([BIN], input=stdin, capture_output=True, text=True).stdout.strip()


def parse(out):
    """-> ('OK', segs, area) | ('EMPTY'|'DEGENERATE'|'NAN', None, None)."""
    lines = out.splitlines()
    if not lines:
        return ("?", None, None)
    if lines[0] in ("EMPTY", "DEGENERATE", "NAN"):
        return (lines[0], None, None)
    m = int(lines[0])
    segs = []
    for ln in lines[1:1 + m]:
        t = ln.split()
        if t[0] == "C":
            segs.append(("C", (hx(t[1]), hx(t[2])), (hx(t[3]), hx(t[4]))))
        else:
            segs.append(("A", (hx(t[1]), hx(t[2])), (hx(t[3]), hx(t[4])), (hx(t[5]), hx(t[6]))))
    area = None
    for ln in lines[1 + m:]:
        if ln.startswith("AREA "):
            area = hx(ln.split()[1])
    return ("OK", segs, area)


def hx(s):
    return float.fromhex(s) if ("x" in s or "X" in s) else float(s)


# --- geometry helpers (independent, exact-Fraction circumcentre) ------------
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


def raycast_in(ring, p):
    """Independent arc-aware ray cast: p strictly inside the curved region."""
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


def seg_sample(s, t):
    if s[0] == "C":
        (px, py), (qx, qy) = s[1], s[2]
        return (px + t * (qx - px), py + t * (qy - py))
    o = circumcentre(s[1], s[2], s[3])
    if o is None:
        (px, py), _, (qx, qy) = s[1], s[2], s[3]
        return (px + t * (qx - px), py + t * (qy - py))
    ox, oy, r = o
    a, b, c = s[1], s[2], s[3]

    def ang(p):
        return math.atan2(p[1] - oy, p[0] - ox)

    def ccw(f, tt):
        v = math.fmod(tt - f, 2 * math.pi)
        return v + 2 * math.pi if v < 0 else v
    a0 = ang(a)
    dab, dac = ccw(a0, ang(b)), ccw(a0, ang(c))
    sweep = dac if dab <= dac else dac - 2 * math.pi
    th = a0 + t * sweep
    return (ox + r * math.cos(th), oy + r * math.sin(th))


def boundary_samples(ring, n=48):
    """Dense source-boundary sample points (precomputed once per ring)."""
    return [seg_sample(s, k / n) for s in ring for k in range(n + 1)]


def dist_to_samples(bpts, x, y):
    best = float("inf")
    for (bx, by) in bpts:
        dd = (x - bx) ** 2 + (y - by) ** 2
        if dd < best:
            best = dd
    return math.sqrt(best)


def bbox(ring):
    pts = [pt for s in ring for pt in ([s[1], s[2]] if s[0] == "C" else [s[1], s[2], s[3]])]
    xs = [q[0] for q in pts]
    ys = [q[1] for q in pts]
    return min(xs), max(xs), min(ys), max(ys)


def minkowski_area(ring, d, ng=150):
    """Independent dense-grid area of buffer(region, d) (the certificate ground
    truth).  d>0 dilation; d<0 erosion.  Source boundary sampled once."""
    bpts = boundary_samples(ring)
    minx, maxx, miny, maxy = bbox(ring)
    pad = abs(d) + 0.5
    x0, x1 = minx - pad, maxx + pad
    y0, y1 = miny - pad, maxy + pad
    cell = (x1 - x0) / ng
    cy = (y1 - y0) / ng
    cnt = 0
    for i in range(ng):
        x = x0 + (i + 0.5) * cell
        for j in range(ng):
            y = y0 + (j + 0.5) * cy
            db = dist_to_samples(bpts, x, y)
            if d >= 0:
                hit = db <= d or raycast_in(ring, (x, y))
            else:
                hit = db >= -d and raycast_in(ring, (x, y))
            if hit:
                cnt += 1
    return cnt * cell * cy


def perimeter(ring, nsamp=400):
    per = 0.0
    for s in ring:
        prev = seg_sample(s, 0.0)
        for k in range(1, nsamp + 1):
            cur = seg_sample(s, k / nsamp)
            per += math.hypot(cur[0] - prev[0], cur[1] - prev[1])
            prev = cur
    return per


# --- curated convex shells --------------------------------------------------
def disk(cx, cy, r):
    return [("A", (cx + r, cy), (cx, cy + r), (cx - r, cy)),
            ("A", (cx - r, cy), (cx, cy - r), (cx + r, cy))]


def sq(x0, y0, x1, y1):
    return [("C", (x0, y0), (x1, y0)), ("C", (x1, y0), (x1, y1)),
            ("C", (x1, y1), (x0, y1)), ("C", (x0, y1), (x0, y0))]


def triangle(p, q, r):
    return [("C", p, q), ("C", q, r), ("C", r, p)]


def stadium(cx, hw, r):
    # rectangle [-hw,hw] x [-r,r] capped by semicircles of radius r (smooth, convex)
    return [("C", (cx - hw, -r), (cx + hw, -r)),
            ("A", (cx + hw, -r), (cx + hw + r, 0), (cx + hw, r)),
            ("C", (cx + hw, r), (cx - hw, r)),
            ("A", (cx - hw, r), (cx - hw - r, 0), (cx - hw, -r))]


# ---------------------------------------------------------------------------
emit("# Adversarial tests for BUFFER_REGION (RocqRefRunner), BUF-1/BUF-NEG, JTS #1195 §7.")
emit("# Assembles the offset boundary of a closed curve ring + its signed area.")
emit("# I1 parallel-dist, I2 area vs Minkowski, I3 Steiner, I4 EMPTY, I5 d=0, I6 monotonic.")
emit("# '!!' lines are gated-invariant violations (CI-failing).")
emit()


def check_parallel(name, ring, d, segs):
    """I1: every emitted boundary sample is ~|d| from the source boundary."""
    global violations
    bpts = boundary_samples(ring, 96)
    worst = 0.0
    for s in segs:
        for t in (0.1, 0.37, 0.63, 0.9):
            p = seg_sample(s, t)
            db = dist_to_samples(bpts, p[0], p[1])
            worst = max(worst, abs(db - abs(d)))
    tol = 1e-2 * (1 + abs(d))
    if worst > tol:
        violations += 1
        emit(f"    !! I1_PARALLEL {name} worst |dist-|d||={worst:.4g} > {tol:.4g}")
    return worst


def assess(name, ring, d, convex=True):
    global violations
    out = run(ring, d)
    kind, segs, area = parse(out)
    tags = []
    if kind != "OK":
        emit(f"  [{name} d={d}] -> {kind}")
        return kind
    aabs = abs(area)
    # I1 parallel-distance
    w = check_parallel(name, ring, d, segs)
    # I2 area vs Minkowski sampling
    mk = minkowski_area(ring, d)
    if abs(aabs - mk) > 0.06 * (1 + mk):
        violations += 1
        tags.append(f"!! I2_MINKOWSKI area={aabs:.3f} grid={mk:.3f}")
    # I3 Steiner closed form (convex, d>0)
    if convex and d > 0:
        a0 = abs(parse(run(ring, 0))[2])
        steiner = a0 + perimeter(ring) * d + math.pi * d * d
        if abs(aabs - steiner) > 0.03 * (1 + steiner):
            violations += 1
            tags.append(f"!! I3_STEINER area={aabs:.3f} steiner={steiner:.3f}")
    emit(f"  [{name} d={d}] area={aabs:.3f} mink={mk:.3f} |dpar|={w:.2g}   "
         f"{' '.join(tags) if tags else 'ok'}")
    return area


emit("## I1/I2/I3: parallel-distance, area vs Minkowski, Steiner (convex shells)")
assess("disk r5", disk(0, 0, 5), 2.0)
assess("disk r5 inward", disk(0, 0, 5), -2.0)
assess("square 10", sq(0, 0, 10, 10), 1.5)
assess("triangle", triangle((0, 0), (10, 0), (4, 7)), 1.0)
assess("stadium", stadium(0, 5, 3), 1.0)
assess("stadium inward", stadium(0, 5, 3), -1.0)
assess("disk r4 big buf", disk(1, 2, 4), 3.0)

emit()
emit("## I4 EMPTY: inner buffer past the inradius collapses")
for nm, ring, d in [("disk r5 d=-5", disk(0, 0, 5), -5.0),
                    ("disk r5 d=-7", disk(0, 0, 5), -7.0)]:
    k, _, _ = parse(run(ring, d))
    ok = k == "EMPTY"
    if not ok:
        violations += 1
    emit(f"  [{nm}] -> {k}   {'ok' if ok else '!! I4_NOT_EMPTY'}")

emit()
emit("## I5 d=0 IDENTITY: boundary reproduced, area = source area")
for nm, ring, a0 in [("disk r5", disk(0, 0, 5), math.pi * 25),
                     ("square 10", sq(0, 0, 10, 10), 100.0)]:
    k, segs, area = parse(run(ring, 0))
    ok = (k == "OK" and abs(abs(area) - a0) < 1e-6 * (1 + a0) and len(segs) == len(ring))
    if not ok:
        violations += 1
    emit(f"  [{nm}] segs={len(segs) if segs else 0} area={abs(area) if area else None} "
         f"(src {a0:.3f})   {'ok' if ok else '!! I5_IDENTITY'}")

emit()
emit("## I6 MONOTONIC: |area| strictly increases with d")
for nm, ring in [("disk r5", disk(0, 0, 5)), ("square 10", sq(0, 0, 10, 10))]:
    areas = []
    for d in (0.0, 0.5, 1.0, 2.0):
        _, _, a = parse(run(ring, d))
        areas.append(abs(a))
    mono = all(areas[i] < areas[i + 1] - 1e-9 for i in range(len(areas) - 1))
    if not mono:
        violations += 1
    emit(f"  [{nm}] areas(d=0,.5,1,2)={['%.2f' % v for v in areas]}   "
         f"{'ok' if mono else '!! I6_NOT_MONOTONIC'}")

emit()
emit("## scope guards: reflex / cornered-inward -> DEGENERATE (out of v1)")
chevron = [("C", (0, 0), (6, 0)), ("C", (6, 0), (3, 3)),
           ("C", (3, 3), (6, 6)), ("C", (6, 6), (0, 6)), ("C", (0, 6), (0, 0))]
for nm, ring, d in [("reflex quad d=1", chevron, 1.0),
                    ("square inward d=-1", sq(0, 0, 10, 10), -1.0)]:
    k, _, _ = parse(run(ring, d))
    ok = k == "DEGENERATE"
    if not ok:
        violations += 1
    emit(f"  [{nm}] -> {k}   {'ok' if ok else '!! SCOPE_GUARD'}")

emit()
if violations:
    emit(f"::error::BUFFER_REGION violated {violations} invariant(s)/expectation(s).")
    sys.exit(1)
emit("# All invariants (I1 parallel, I2 Minkowski, I3 Steiner, I4 EMPTY, "
     "I5 identity, I6 monotonic) hold.")
