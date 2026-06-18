#!/usr/bin/env python3
# =============================================================================
# oracle/gen_curve_relate_matrix_tests.py
# -----------------------------------------------------------------------------
# Adversarial tests for the CURVE_RELATE_MATRIX oracle mode (R-PR, JTS #1195 §7).
# The oracle COMPUTES the full 9-cell DE-9IM matrix of two curve geometries in
# the TRUE OGC convention (the existing RELATE_MATRIX / RELATE_PREDICATE modes
# only EVALUATE a supplied matrix); it generalizes HOLES_DISJOINT.
#
# Row-major cells: II IB IE / BI BB BE / EI EB EE, each F/0/1/2.  TRUE OGC:
# disjoint areal geometries -> "FF2FF1212", A-contains-B -> "212FF1FF2",
# overlap -> "212101212", equal -> "2FFF1FFF2".  (NOT the repo's older non-OGC
# "FFFFFFFFF" disjoint pin: DE9IM.v's pat_disjoint forces EI=EB=F and does not
# match a true areal disjoint matrix -- I4 therefore uses an INDEPENDENT OGC
# predicate engine, and only the OGC-robust predicates are cross-checked against
# the repo RELATE_PREDICATE mode.)
#
# Invariants gated (a '!!' line + nonzero exit on violation):
#   I1  CURATED       hand-verified TRUE-OGC matrices for named configurations
#                     (matching the Coq cm_matrix_* constants in
#                     theories/RelateCurveMatrix.v).
#   I2  TRANSPOSE     run(B,A) == transpose(run(A,B)) cell-for-cell -- pins the
#                     Coq geom_de9im_pointset_transpose law at the binary level.
#   I3  AGREEMENT     oracle == an INDEPENDENT dense-sampling DE-9IM inferred by
#                     a separate Python implementation (exact-Fraction arc-aware
#                     classification of a grid + along-boundary samples), cell by
#                     cell.  The external completeness/soundness check.
#   I4  OGC-PREDICATE the computed matrix satisfies an independent Python OGC
#                     predicate engine (disjoint => DISJOINT, contains =>
#                     CONTAINS, overlap => OVERLAPS), AND the OGC-robust
#                     predicates agree with the repo RELATE_PREDICATE mode.
#
# I5 BROKEN-BINARY regression: this suite was verified to FAIL when the oracle's
# EE cell is hard-wired to 'F' (violating the proved EE-always-2 law -- I1/I3
# flag it) and to PASS on the correct binary.
#
# Run from repo root:
#   python3 oracle/gen_curve_relate_matrix_tests.py > oracle/curve_relate_matrix_tests.txt
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


def geom_text(g):
    # g = list of rings; ring = list of segments (ring 0 = outer, rest = holes)
    out = [str(len(g))]
    for ring in g:
        out.append(str(len(ring)))
        out.extend(seg_line(s) for s in ring)
    return "\n".join(out)


def run(ga, gb):
    stdin = "CURVE_RELATE_MATRIX\n%s\n%s\n" % (geom_text(ga), geom_text(gb))
    return subprocess.run([BIN], input=stdin, capture_output=True, text=True).stdout.strip()


def predicate(matrix, name):
    stdin = "RELATE_PREDICATE\n%s\n%s\n" % (matrix, name)
    return subprocess.run([BIN], input=stdin, capture_output=True, text=True).stdout.strip()


# --- transpose of a 9-char matrix (swap IB<->BI, IE<->EI, BE<->EB) -----------
def transpose(m):
    # indices 0 1 2 / 3 4 5 / 6 7 8 ; transpose swaps (i,j)<->(j,i)
    idx = [0, 3, 6, 1, 4, 7, 2, 5, 8]
    return "".join(m[i] for i in idx)


# =============================================================================
# Independent exact-Fraction arc-aware geometry classifier (the I3 ground truth).
# Mirrors the oracle's rule with a SEPARATE implementation.
# =============================================================================
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


def raycast_ring_in(ring, p):
    """Independent arc-aware rightward-ray parity (point strictly inside ring)."""
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


def in_region(g, p):
    if not raycast_ring_in(g[0], p):
        return False
    return not any(raycast_ring_in(h, p) for h in g[1:])


def on_seg(s, x, y):
    if s[0] == "C":
        (px, py), (qx, qy) = s[1], s[2]
        dx, dy = qx - px, qy - py
        l2 = dx * dx + dy * dy
        cross = dx * (y - py) - dy * (x - px)
        if abs(cross) > 1e-7 * (1 + l2):
            return False
        dot = (x - px) * dx + (y - py) * dy
        return -1e-7 <= dot <= l2 + 1e-7
    o = circumcentre(s[1], s[2], s[3])
    if o is None:
        return on_seg(("C", s[1], s[2]), x, y) or on_seg(("C", s[2], s[3]), x, y)
    ox, oy, r = o
    if abs(math.hypot(x - ox, y - oy) - r) > 1e-7 * (1 + r):
        return False
    return on_arc_sector(ox, oy, s[1], s[2], s[3], x, y)


def on_boundary(g, p):
    return any(on_seg(s, p[0], p[1]) for ring in g for s in ring)


def classify(g, p):
    if on_boundary(g, p):
        return 1            # boundary
    return 0 if in_region(g, p) else 2   # 0 interior, 2 exterior


def seg_sample(s, t):
    if s[0] == "C":
        (px, py), (qx, qy) = s[1], s[2]
        return (px + t * (qx - px), py + t * (qy - py))
    o = circumcentre(s[1], s[2], s[3])
    if o is None:
        (px, py), (_, _), (qx, qy) = s[1], s[2], s[3]
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


def independent_matrix(ga, gb):
    """Infer the TRUE-OGC 9-cell DE-9IM by independent dense sampling."""
    # open cells II/IE/EI/EE via a grid over the joint bounding box
    pts = [pt for g in (ga, gb) for ring in g for s in ring for pt in
           ([s[1], s[2]] if s[0] == "C" else [s[1], s[2], s[3]])]
    xs = [p[0] for p in pts]
    ys = [p[1] for p in pts]
    minx, maxx, miny, maxy = min(xs), max(xs), min(ys), max(ys)
    padx = 0.05 * (maxx - minx) + 1e-3
    pady = 0.05 * (maxy - miny) + 1e-3
    ng = 90
    f_ii = f_ie = f_ei = False
    for i in range(ng):
        for j in range(ng):
            x = minx - padx + (i + 0.5) / ng * (maxx - minx + 2 * padx)
            y = miny - pady + (j + 0.5) / ng * (maxy - miny + 2 * pady)
            if on_boundary(ga, (x, y)) or on_boundary(gb, (x, y)):
                continue
            ina, inb = in_region(ga, (x, y)), in_region(gb, (x, y))
            if ina and inb:
                f_ii = True
            if ina and not inb:
                f_ie = True
            if (not ina) and inb:
                f_ei = True

    # boundary cells via along-boundary samples (run => 1, isolated => 0).
    # A transversal boundary crossing shows up as an Interior<->Exterior flip
    # between consecutive along-boundary samples (the self boundary passes
    # through the other's boundary) -> an isolated (0-dim) BB point.
    def scan(self_g, other_g):
        pt = [False, False, False]
        run = [False, False, False]
        cross = False
        nsamp = 81
        for ring in self_g:
            for s in ring:
                lab = [classify(other_g, seg_sample(s, (k + 0.5) / nsamp))
                       for k in range(nsamp)]
                for l in lab:
                    pt[l] = True
                for k in range(nsamp - 1):
                    if lab[k] == lab[k + 1]:
                        run[lab[k]] = True
                    if {lab[k], lab[k + 1]} == {0, 2}:
                        cross = True
        return pt, run, cross

    ptA, runA, crossA = scan(ga, gb)
    ptB, runB, crossB = scan(gb, ga)

    def bdim(pt, run, s):
        return 1 if run[s] else (0 if pt[s] else -1)
    bb_run = runA[1] or runB[1]
    bb_pt = ptA[1] or ptB[1] or crossA or crossB or analytic_meets(ga, gb)
    cells = [
        2 if f_ii else -1,          # II
        bdim(ptB, runB, 0),         # IB  (B-boundary interior to A)
        2 if f_ie else -1,          # IE
        bdim(ptA, runA, 0),         # BI  (A-boundary interior to B)
        (1 if bb_run else (0 if bb_pt else -1)),  # BB
        bdim(ptA, runA, 2),         # BE  (A-boundary exterior to B)
        2 if f_ei else -1,          # EI
        bdim(ptB, runB, 2),         # EB  (B-boundary exterior to A)
        2,                          # EE
    ]
    return "".join("F" if d < 0 else str(d) for d in cells)


# --- independent analytic boundary-intersection (for isolated/tangent BB) ----
# A separate Python implementation (circle-circle / circle-line / line-line) so
# the I3 ground truth catches measure-zero tangent contacts the sampling misses.
def _circle(s):
    o = circumcentre(s[1], s[2], s[3])
    return None if o is None else o  # (ox, oy, r)


def _line_line(p, q, u, v):
    d1x, d1y = q[0] - p[0], q[1] - p[1]
    d2x, d2y = v[0] - u[0], v[1] - u[1]
    den = d1x * d2y - d1y * d2x
    if abs(den) < 1e-12:
        return []
    t = ((u[0] - p[0]) * d2y - (u[1] - p[1]) * d2x) / den
    return [(p[0] + t * d1x, p[1] + t * d1y)]


def _circle_line(ox, oy, r, p, q):
    dx, dy = q[0] - p[0], q[1] - p[1]
    a = dx * dx + dy * dy
    if a < 1e-18:
        return []
    b = 2 * (dx * (p[0] - ox) + dy * (p[1] - oy))
    c = (p[0] - ox) ** 2 + (p[1] - oy) ** 2 - r * r
    disc = b * b - 4 * a * c
    if disc < 0:
        return []
    sq = math.sqrt(disc)
    return [(p[0] + t * dx, p[1] + t * dy) for t in ((-b + sq) / (2 * a), (-b - sq) / (2 * a))]


def _circle_circle(o1, o2):
    ox1, oy1, r1 = o1
    ox2, oy2, r2 = o2
    d = math.hypot(ox2 - ox1, oy2 - oy1)
    if d < 1e-12 or d > r1 + r2 + 1e-9 or d < abs(r1 - r2) - 1e-9:
        return []
    a = (d * d + r1 * r1 - r2 * r2) / (2 * d)
    h2 = r1 * r1 - a * a
    h = math.sqrt(h2) if h2 > 0 else 0.0
    ux, uy = (ox2 - ox1) / d, (oy2 - oy1) / d
    mx, my = ox1 + a * ux, oy1 + a * uy
    return [(mx - h * uy, my + h * ux), (mx + h * uy, my - h * ux)]


def seg_meet(sa, sb):
    ca, cb = (_circle(sa) if sa[0] == "A" else None), (_circle(sb) if sb[0] == "A" else None)
    if sa[0] == "C" and sb[0] == "C":
        cand = _line_line(sa[1], sa[2], sb[1], sb[2])
    elif ca and sb[0] == "C":
        cand = _circle_line(ca[0], ca[1], ca[2], sb[1], sb[2])
    elif cb and sa[0] == "C":
        cand = _circle_line(cb[0], cb[1], cb[2], sa[1], sa[2])
    elif ca and cb:
        cand = _circle_circle(ca, cb)
    else:
        cand = []
    return [p for p in cand if on_seg(sa, p[0], p[1]) and on_seg(sb, p[0], p[1])]


def analytic_meets(ga, gb):
    return any(seg_meet(sa, sb)
               for ra in ga for sa in ra for rb in gb for sb in rb)


# --- independent OGC predicate engine (I4) ----------------------------------
# Indices row-major: 0=II 1=IB 2=IE / 3=BI 4=BB 5=BE / 6=EI 7=EB 8=EE.
OGC_PATTERNS = {
    # name: list of 9-char patterns ('*' wild, 'F', 'T', or a digit)
    "DISJOINT":   ["FF*FF****"],                       # II=IB=BI=BB=F
    "INTERSECTS": ["T********", "*T*******",            # II=T or IB=T
                   "***T*****", "****T****"],           # or BI=T or BB=T
    "CONTAINS":   ["T*****FF*"],                        # II=T, EI=F, EB=F
    "WITHIN":     ["T*F**F***"],                        # II=T, IE=F, BE=F
    "OVERLAPS":   ["T*T***T**"],                        # II=T, IE=T, EI=T (areal)
}


def pat_char(pc, ch):
    if pc == "*":
        return True
    if pc == "F":
        return ch == "F"
    if pc == "T":
        return ch != "F"
    return ch == pc


def ogc_holds(matrix, name):
    pats = OGC_PATTERNS[name]
    return any(all(pat_char(p[i], matrix[i]) for i in range(9)) for p in pats)


# --- shapes -----------------------------------------------------------------
def disk(cx, cy, r):
    return [[("A", (cx + r, cy), (cx, cy + r), (cx - r, cy)),
             ("A", (cx - r, cy), (cx, cy - r), (cx + r, cy))]]


def sq(x0, y0, x1, y1):
    return [[("C", (x0, y0), (x1, y0)), ("C", (x1, y0), (x1, y1)),
             ("C", (x1, y1), (x0, y1)), ("C", (x0, y1), (x0, y0))]]


def annulus(cx, cy, ro, ri):
    return [disk(cx, cy, ro)[0], disk(cx, cy, ri)[0]]


def lens(cx, r):
    return [[("A", (cx + r, 0), (cx, r), (cx - r, 0)), ("C", (cx - r, 0), (cx + r, 0))]]


# ---------------------------------------------------------------------------
emit("# Adversarial tests for CURVE_RELATE_MATRIX (RocqRefRunner), R-PR / JTS #1195 §7.")
emit("# Computes the full TRUE-OGC 9-cell DE-9IM of two curve geometries.")
emit("# I1 curated, I2 transpose, I3 independent dense-sampling, I4 OGC predicates.")
emit("# '!!' lines are gated-invariant violations (CI-failing).")
emit()


CASES = [
    ("disjoint disks",        disk(0, 0, 5),   disk(20, 0, 5),  "FF2FF1212"),
    ("A contains B (disk)",   disk(0, 0, 10),  disk(0, 0, 2),   "212FF1FF2"),
    ("B within A (disk)",     disk(0, 0, 2),   disk(0, 0, 10),  "2FF1FF212"),
    ("overlapping disks",     disk(0, 0, 5),   disk(6, 0, 5),   "212101212"),
    ("externally tangent",    disk(0, 0, 5),   disk(10, 0, 5),  "FF2F01212"),
    ("equal disks",           disk(0, 0, 5),   disk(0, 0, 5),   "2FFF1FFF2"),
    ("disjoint squares",      sq(0, 0, 2, 2),  sq(5, 5, 7, 7),  "FF2FF1212"),
    ("square contains disk",  sq(-9, -9, 9, 9), disk(0, 0, 3),  "212FF1FF2"),
    ("disk in annulus hole",  annulus(0, 0, 10, 5), disk(0, 0, 2), "FF2FF1212"),
    ("far-apart lenses",      lens(0, 2),      lens(20, 2),     "FF2FF1212"),
]

emit("## I1 CURATED + I2 TRANSPOSE + I4 OGC-PREDICATE")
for name, ga, gb, expect in CASES:
    got = run(ga, gb)
    tags = []
    if got != expect:
        violations += 1
        tags.append(f"!! I1_EXPECTED_{expect}_GOT_{got}")
    # I2 transpose
    swapped = run(gb, ga)
    if swapped != transpose(got):
        violations += 1
        tags.append(f"!! I2_TRANSPOSE got_swap={swapped} expect={transpose(got)}")
    # I4 repo cross-check: feed the computed matrix to the repo RELATE_PREDICATE
    # mode (lookup_matrix accepts a literal 9-char string) and require agreement
    # with the independent OGC engine -- but ONLY for the OGC-robust predicates
    # CONTAINS / WITHIN.  The repo's DISJOINT / INTERSECTS / OVERLAPS patterns are
    # the OLDER non-OGC simplification (im_intersects includes the IE disjunct,
    # the documented DE9IM.disjoint_intersects3 quirk; im_overlaps omits the
    # IE/EI requirement so it fires on `equal`), so they are intentionally NOT
    # routed through the repo engine -- the independent engine is the oracle.
    if len(got) == 9 and all(c in "FT012" for c in got):
        for pred in ("CONTAINS", "WITHIN"):
            ind = ogc_holds(got, pred)
            repo = predicate(got, pred) == "TRUE"
            if ind != repo:
                violations += 1
                tags.append(f"!! I4_{pred} ind={ind} repo={repo}")
    emit(f"  [{name}] {ga and ''}-> {got!r}   {' '.join(tags) if tags else 'ok'}")

emit()
emit("## I3 INDEPENDENT DENSE-SAMPLING AGREEMENT (oracle == separate inference)")
for name, ga, gb, _ in CASES:
    got = run(ga, gb)
    ind = independent_matrix(ga, gb)
    if got != ind:
        violations += 1
        emit(f"  [{name}] !! I3_DISAGREE oracle={got} independent={ind}")
    else:
        emit(f"  [{name}] oracle == independent ({got})   ok")

emit()
emit("## I4 named-predicate sanity (independent OGC engine)")
for name, ga, gb, expect in CASES:
    got = run(ga, gb)
    checks = []
    if "disjoint" in name or "far-apart" in name or "in annulus hole" in name:
        checks = [("DISJOINT", True), ("INTERSECTS", False)]
    elif "contains" in name:
        checks = [("CONTAINS", True)]
    elif "within" in name:
        checks = [("WITHIN", True)]
    elif "overlapping" in name:
        checks = [("OVERLAPS", True), ("INTERSECTS", True)]
    for pred, want in checks:
        if ogc_holds(got, pred) != want:
            violations += 1
            emit(f"  [{name}] !! I4_OGC_{pred} expected {want} on {got}")
        else:
            emit(f"  [{name}] OGC {pred}={want}   ok")

emit()
if violations:
    emit(f"::error::CURVE_RELATE_MATRIX violated {violations} invariant(s)/expectation(s).")
    sys.exit(1)
emit("# All invariants (I1 curated, I2 transpose, I3 agreement, I4 OGC predicates) hold.")
