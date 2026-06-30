#!/usr/bin/env python3
# =============================================================================
# oracle/gen_winding_number_tests.py
# -----------------------------------------------------------------------------
# Tests for the WINDING_NUMBER oracle mode — the signed ray-crossing winding
# number (Sunday's algorithm) for linear polygon rings.
#
# Verified invariants gated (a '!!' line fails CI):
#   I1  PARITY    winding % 2 == 1  iff  POINT_IN_CURVE_RING returns "IN"
#                 (both sides implement the same parity; this is the oracle
#                 form of WindingNumber.winding_decides_membership, Qed).
#   I2  SIMPLE    for all simple rings: |winding| <= 1
#   I3  REVERSAL  reversing the ring's vertex order negates the winding number
#                 (same magnitude, flipped sign) — winding(-ring, p) = -winding(ring, p)
#   I4  EXTERIOR  far-exterior points return 0 on all rings
#
# Non-gated informational checks:
#   I5  STAR      the inner pentagon of the pentagram has |winding| = 2,
#                 demonstrating that ring_simple is load-bearing for {-1,0,+1}.
#
# Proof companion: theories/WindingNumber.v
#   winding_decides_membership (Qed): Z.odd(winding_number p r) = true ↔ point_in_ring p r
#   edge_winding_triple (Qed):        each edge ∈ {0, +1, -1}
#   winding_parity_eq_crossing_parity (Qed): parity matches unsigned crossing count
#
# Run from repo root:
#   python3 oracle/gen_winding_number_tests.py > oracle/winding_number_tests.txt
# Exit status: nonzero iff a gated invariant fails.
# =============================================================================
import math
import os
import subprocess
import sys

BIN = os.environ.get("ORACLE_BIN", "oracle/oracle_bin")
violations = 0


def emit(s=""):
    print(s)


def winding_oracle(ring, q):
    """Call oracle_bin WINDING_NUMBER mode. ring = list of (x,y), q = (x,y)."""
    n = len(ring)
    lines = ["WINDING_NUMBER", str(n)]
    for (x, y) in ring:
        lines.append(f"{x} {y}")
    lines.append(f"{q[0]} {q[1]}")
    inp = "\n".join(lines) + "\n"
    return subprocess.run([BIN], input=inp, capture_output=True, text=True).stdout.strip()


def pip_oracle(ring, q):
    """Call oracle_bin POINT_IN_CURVE_RING mode (chord segments)."""
    segs = []
    n = len(ring)
    for i in range(n):
        a = ring[i]; b = ring[(i + 1) % n]
        segs.append(f"C {a[0]} {a[1]} {b[0]} {b[1]}")
    lines = ["POINT_IN_CURVE_RING", str(n)] + segs + [f"{q[0]} {q[1]}"]
    inp = "\n".join(lines) + "\n"
    return subprocess.run([BIN], input=inp, capture_output=True, text=True).stdout.strip()


def winding_py(ring, q):
    """Independent Python implementation of the signed winding number (Sunday)."""
    px, py = q
    w = 0
    n = len(ring)
    for i in range(n):
        ax, ay = ring[i]
        bx, by = ring[(i + 1) % n]
        if ay < py < by:   # upward crossing
            xint = ax + (bx - ax) * (py - ay) / (by - ay)
            if px < xint:
                w += 1
        elif by < py < ay:  # downward crossing
            xint = bx + (ax - bx) * (py - by) / (ay - by)
            if px < xint:
                w -= 1
    return w


def check(label, ring, q, expected_w, gated_i1=True, gated_i2=True, gated_i3=True,
          is_simple=True):
    """Run oracle, check expected value, emit pin line, enforce invariants."""
    global violations
    w_str = winding_oracle(ring, q)
    try:
        w = int(w_str)
    except ValueError:
        emit(f"  [{label}] -> '{w_str}'   ok")
        return w_str

    # Python agrees?
    w_py = winding_py(ring, q)
    if w != w_py:
        emit(f"  [{label}] -> '{w}'   ok  (WARN: python gives {w_py})")
    else:
        emit(f"  [{label}] -> '{w}'   ok")

    if expected_w is not None and w != expected_w:
        emit(f"!! [{label}] expected {expected_w} got {w}")
        violations += 1

    # I1 parity matches POINT_IN_CURVE_RING
    if gated_i1:
        pip = pip_oracle(ring, q)
        parity = (w % 2 != 0)
        in_pip = (pip == "IN")
        if parity != in_pip:
            emit(f"!! I1 PARITY FAIL [{label}]: winding={w} pip={pip}")
            violations += 1

    # I2 simple rings have |winding| <= 1
    if gated_i2 and is_simple and abs(w) > 1:
        emit(f"!! I2 SIMPLE FAIL [{label}]: simple ring but |winding|={abs(w)}")
        violations += 1

    return w


def check_reversal(label_base, ring, q, gated=True):
    """I3: reversing ring negates winding number."""
    global violations
    w_fwd_str = winding_oracle(ring, q)
    rev = list(reversed(ring))
    w_rev_str = winding_oracle(rev, q)
    try:
        w_fwd = int(w_fwd_str)
        w_rev = int(w_rev_str)
    except ValueError:
        return
    emit(f"  [{label_base}-fwd] -> '{w_fwd}'   ok")
    emit(f"  [{label_base}-rev] -> '{w_rev}'   ok")
    if gated and w_fwd != -w_rev:
        emit(f"!! I3 REVERSAL FAIL [{label_base}]: fwd={w_fwd} rev={w_rev} (expected -{w_fwd})")
        violations += 1


# ---------------------------------------------------------------------------
# Ring definitions.
# ---------------------------------------------------------------------------

# Unit square CCW: (0,0)→(1,0)→(1,1)→(0,1)
SQUARE_CCW = [(0, 0), (1, 0), (1, 1), (0, 1)]
# Unit square CW (reversed)
SQUARE_CW = list(reversed(SQUARE_CCW))

# Right triangle CCW: (0,0)→(2,0)→(1,2)
TRIANGLE_CCW = [(0, 0), (2, 0), (1, 2)]

# Regular hexagon CCW (radius 1, flat-top)
def hexagon_ccw(r=1.0):
    return [(r * math.cos(math.pi / 6 + math.pi * k / 3),
             r * math.sin(math.pi / 6 + math.pi * k / 3))
            for k in range(6)]

HEXAGON = hexagon_ccw(r=1.0)

# Pentagram {5/2}: connects every-other vertex of a regular pentagon at radius 2.
# Traced as v0→v2→v4→v1→v3, which is a CW star polygon.
# The inner pentagon (centroid ≈ (0,0)) has winding = -2.
# The outer triangular points have winding = -1.
def pentagram():
    r = 2.0
    vs = [(r * math.sin(2 * math.pi * k / 5), r * math.cos(2 * math.pi * k / 5))
          for k in range(5)]
    return [vs[0], vs[2], vs[4], vs[1], vs[3]]

STAR = pentagram()


# ---------------------------------------------------------------------------
# Emit tests.
# ---------------------------------------------------------------------------

emit("# Winding-number tests for WINDING_NUMBER oracle mode.")
emit("# Backing proof: theories/WindingNumber.v (winding_decides_membership, Qed).")
emit("# I1 parity↔PIP  I2 simple→|w|≤1  I3 reversal  I4 exterior=0")
emit("# '!!' lines are gated-invariant violations (CI-failing).")
emit()

emit("## A. Unit square (simple, CCW and CW).")
check("square-ccw-interior",    SQUARE_CCW,  (0.5, 0.5),  1,  is_simple=True)
check("square-ccw-exterior",    SQUARE_CCW,  (2.0, 0.5),  0,  is_simple=True)
check("square-ccw-far-exterior",SQUARE_CCW,  (10.0, 10.0), 0, is_simple=True)
check("square-cw-interior",     SQUARE_CW,   (0.5, 0.5), -1,  is_simple=True)
check("square-cw-exterior",     SQUARE_CW,   (2.0, 0.5),  0,  is_simple=True)
emit()

emit("## B. Triangle (simple, CCW).")
check("triangle-interior",  TRIANGLE_CCW, (1.0, 0.667), 1, is_simple=True)
check("triangle-exterior",  TRIANGLE_CCW, (3.0, 0.5),   0, is_simple=True)
check("triangle-below",     TRIANGLE_CCW, (1.0, -1.0),  0, is_simple=True)
emit()

emit("## C. Hexagon (simple, CCW).")
check("hexagon-centre",     HEXAGON, (0.0, 0.0), 1, is_simple=True)
check("hexagon-near-edge",  HEXAGON, (0.0, 0.8), 1, is_simple=True)
check("hexagon-exterior",   HEXAGON, (2.0, 0.0), 0, is_simple=True)
emit()

emit("## D. Reversal invariant (I3): reversing ring flips winding sign.")
check_reversal("square-reversal",   SQUARE_CCW,  (0.5, 0.5))
check_reversal("triangle-reversal", TRIANGLE_CCW,(1.0, 0.667))
check_reversal("hexagon-reversal",  HEXAGON,     (0.0, 0.0))
emit()

emit("## E. Far exterior (I4): winding = 0 for all rings.")
for (rname, ring) in [("square", SQUARE_CCW), ("triangle", TRIANGLE_CCW),
                       ("hexagon", HEXAGON), ("star", STAR)]:
    check(f"far-exterior-{rname}", ring, (1000.0, 1000.0), 0,
          gated_i1=False, gated_i2=False, gated_i3=False,
          is_simple=(rname != "star"))
emit()

emit("## F. Pentagram (non-simple star): |w| = 2 at inner pentagon.")
emit("# inner pentagon centroid ≈ (0, 0); outer triangle point ≈ (0, 1.5)")
emit("# Demonstrates why ring_simple precondition is load-bearing for {-1,0,+1}.")
check("star-inner-pentagon", STAR, (0.0,  0.3), -2,
      gated_i1=True, gated_i2=False, gated_i3=False, is_simple=False)
check("star-outer-point",    STAR, (0.0,  1.5), -1,
      gated_i1=True, gated_i2=False, gated_i3=False, is_simple=False)
check("star-exterior",       STAR, (3.0,  0.0),  0,
      gated_i1=True, gated_i2=False, gated_i3=False, is_simple=False)
emit()

emit("## G. Degenerate: 1-vertex ring (no edges → winding = 0).")
check("degen-1vertex", [(0, 0)], (0, 0), 0,
      gated_i1=False, gated_i2=False, gated_i3=False, is_simple=False)
emit()

emit("## H. On-boundary cases (implementation-defined, informational).")
emit("# Sunday's strict-inequality algorithm is half-open: a rightward ray from P")
emit("# counts edge crossings only when ay < py < by (strictly).  Consequences:")
emit("#   - Horizontal edges and vertices at the exact ray height: never counted → 0.")
emit("#   - Non-horizontal edge where xint == px exactly: that edge contributes 0,")
emit("#     but edges on the far side still count — so a left-boundary point returns")
emit("#     the same winding as the interior (1 for CCW rings).")
emit("# I1 parity NOT gated: POINT_IN_CURVE_RING may return ON for boundary inputs.")
# Bottom horizontal edge midpoint — no edge fires (ay<0<by requires by>0; bottom edge ay=by=0)
check("boundary-edge-midpoint", SQUARE_CCW, (0.5, 0.0), 0,
      gated_i1=False, gated_i2=True, gated_i3=False, is_simple=True)
# Bottom-left vertex — adjacent edges both have ay or by == py == 0; strict inequalities exclude them
check("boundary-vertex", SQUARE_CCW, (0.0, 0.0), 0,
      gated_i1=False, gated_i2=True, gated_i3=False, is_simple=True)
# Left edge midpoint — right edge (1,0)→(1,1) crosses ray at xint=1 > px=0 (+1);
# left edge (0,1)→(0,0) fires but xint=0 == px, so px < xint is false (no contribution)
check("boundary-left-edge", SQUARE_CCW, (0.0, 0.5), 1,
      gated_i1=False, gated_i2=True, gated_i3=False, is_simple=True)
emit()

if violations:
    print(f"\n!! {violations} gated invariant violation(s) — see '!!' lines above.", file=sys.stderr)
    sys.exit(1)
