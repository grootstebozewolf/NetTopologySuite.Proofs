#!/usr/bin/env python3
"""
Hunter for CurveType (0=CircularArc, 1=EllipticArc, 2=Bezier3Curve).

Drives the RocqRefRunner (oracle_bin) with segments of each type (and mixtures)
looking for interesting / adversarial behaviour in the focus areas:
noding, soundness, DIM9/relate, orientation, InCircleArc.

Output is human + grep-friendly.  Lines containing "INTERESTING", "DIVERGE",
"NAN", or large sensitivity are candidates to promote into permanent tests.

Usage:
  python3 oracle/gen_adversarial_curves.py --types 0,1,2 --budget 20000 \
      > oracle/curve_type_hunt.txt

The script prefers the independent Python models for classification and uses
oracle_bin mainly to surface NaN / surprising definite answers on the cheap path.
"""

import argparse
import math
import os
import random
import subprocess
import sys
from fractions import Fraction as F

BIN = os.environ.get("ORACLE_BIN", "oracle/oracle_bin")
random.seed(42)   # reproducible hunts

def run_oracle(mode, stdin):
    try:
        p = subprocess.run([BIN], input=stdin, capture_output=True, text=True, timeout=2)
        return p.stdout.strip()
    except Exception:
        return "ERROR"

def emit(s=""):
    print(s)

# ------------------------------------------------------------------
# Segment emitters (must match the syntax accepted by driver.ml parsers)
# ------------------------------------------------------------------

def seg_c(p0, p1):
    return f"C {p0[0]} {p0[1]} {p1[0]} {p1[1]}"

def seg_a(p0, p1, p2):
    return f"A {p0[0]} {p0[1]} {p1[0]} {p1[1]} {p2[0]} {p2[1]}"

def seg_e(cx, cy, rx, ry, rot, sa, sw):
    # CurveType=1
    return f"E {cx} {cy} {rx} {ry} {rot} {sa} {sw}"

def seg_b(p0, p1, p2, p3):
    # CurveType=2
    return f"B {p0[0]} {p0[1]} {p1[0]} {p1[1]} {p2[0]} {p2[1]} {p3[0]} {p3[1]}"

# ------------------------------------------------------------------
# Simple independent models (very approximate for first-cut hunting)
# ------------------------------------------------------------------

def orient(p0, p1, p2):
    """Return sign of cross product (p1-p0) x (p2-p0) using Fraction."""
    ax, ay = F(p1[0]) - F(p0[0]), F(p1[1]) - F(p0[1])
    bx, by = F(p2[0]) - F(p0[0]), F(p2[1]) - F(p0[1])
    cr = ax * by - ay * bx
    if cr > 0: return "POS"
    if cr < 0: return "NEG"
    return "ZERO"

def incircle_sign(a, b, c, p):
    """Very rough proxy using shoelace-style det on the four points."""
    # Not the true inCircle; used only to look for NaN vs definite in oracle.
    # Real hunters for InCircleArc will compare against a better model or known
    # circular cases.
    pts = [a, b, c, p]
    q = [F(x) for pt in pts for x in pt]
    # simplified 4x4 det sign (placeholder)
    s = (q[0]-q[6])*(q[3]-q[9]) - (q[1]-q[7])*(q[2]-q[8])   # dummy
    if s > 0: return "POS"
    if s < 0: return "NEG"
    return "ZERO"

# ------------------------------------------------------------------
# Hunters per focus area
# ------------------------------------------------------------------

def hunt_orientation_and_incircle(n=5000):
    emit("## HUNT: orientation + incircle on controls / characteristic points of each CurveType")
    types = [0, 1, 2]
    for _ in range(n):
        ctype = random.choice(types)
        mag = random.choice([1.0, 10.0, 1e6, 2**26, 2**30])
        if ctype == 0:
            # Circular (use A style)
            s = (random.uniform(-mag, mag), random.uniform(-mag, mag))
            m = (s[0] + random.uniform(-mag/10, mag/10), s[1] + random.uniform(-mag/10, mag/10))
            e = (random.uniform(-mag, mag), random.uniform(-mag, mag))
            seg = seg_a(s, m, e)
            label = "Circular(0)"
        elif ctype == 1:
            cx, cy = random.uniform(-mag, mag), random.uniform(-mag, mag)
            rx = random.uniform(1, mag)
            ry = rx * random.uniform(0.01, 4.0)   # eccentricity
            rot = random.uniform(0, math.pi)
            sa = random.uniform(0, 2*math.pi)
            sw = random.uniform(0.01, 2*math.pi - 0.01)
            seg = seg_e(cx, cy, rx, ry, rot, sa, sw)
            label = "Elliptic(1)"
            # For orient we use the center as a proxy point
            s = (cx - rx*math.cos(rot), cy - ry*math.sin(rot))
            e = (cx + rx*math.cos(rot), cy + ry*math.sin(rot))
        else:
            s = (random.uniform(-mag, mag), random.uniform(-mag, mag))
            c1 = (s[0] + random.uniform(-mag, mag), s[1] + random.uniform(-mag, mag))
            c2 = (c1[0] + random.uniform(-mag, mag), c1[1] + random.uniform(-mag, mag))
            e = (c2[0] + random.uniform(-mag, mag), c2[1] + random.uniform(-mag, mag))
            seg = seg_b(s, c1, c2, e)
            label = "Bezier3(2)"

        # Drive ORIENT on a few triplets involving the controls
        pts = [s, (s[0]+1, s[1]), e] if ctype != 1 else [s, (cx,cy), e]
        o = run_oracle("ORIENT", f"ORIENT\n{pts[0][0]} {pts[0][1]}\n{pts[1][0]} {pts[1][1]}\n{pts[2][0]} {pts[2][1]}\n")
        ox = run_oracle("ORIENT_EXACT", f"ORIENT_EXACT\n{pts[0][0]} {pts[0][1]}\n{pts[1][0]} {pts[1][1]}\n{pts[2][0]} {pts[2][1]}\n")
        if o not in ("POS","NEG","ZERO") or ox.startswith("NAN"):
            emit(f"  INTERESTING orient NaN/surprise {label}: {o} vs EXACT {ox}")

        # INCIRCLE on four points (for elliptic this is meaningful; for others a proxy)
        if ctype in (0, 1):
            ic = run_oracle("INCIRCLE_SIGN", f"INCIRCLE_SIGN\n{pts[0][0]} {pts[0][1]}\n{pts[1][0]} {pts[1][1]}\n{pts[2][0]} {pts[2][1]}\n{pts[0][0]+0.1} {pts[0][1]+0.1}\n")
            if "NAN" in ic or ic not in ("POS","NEG","ZERO"):
                emit(f"  INTERESTING incircle {label}: {ic}")

    emit()

def hunt_passes_and_noding(n=3000):
    emit("## HUNT: hot-pixel passes-through near controls of each CurveType")
    for _ in range(n):
        ctype = random.choice([0,1,2])
        mag = random.choice([1.0, 64.0, 2**20])
        c = (0.0, 0.0)   # pixel center
        if ctype == 0:
            p0 = (random.uniform(-mag, mag), random.uniform(-mag, mag))
            p1 = (p0[0] + random.uniform(-1, 1), p0[1] + random.uniform(-1, 1))
            seg = seg_a(p0, ((p0[0]+p1[0])/2, (p0[1]+p1[1])/2), p1)  # fake mid
        elif ctype == 1:
            cx, cy = random.uniform(-mag, mag), random.uniform(-mag, mag)
            rx = random.uniform(0.5, mag); ry = rx * random.uniform(0.2, 3)
            rot = random.uniform(0, 2*math.pi)
            sa = random.uniform(0, 2*math.pi)
            sw = 0.3
            seg = seg_e(cx, cy, rx, ry, rot, sa, sw)
            p0 = (cx - rx, cy); p1 = (cx + rx, cy)
        else:
            p0 = (random.uniform(-mag, mag), random.uniform(-mag, mag))
            p1 = (p0[0] + random.uniform(-mag*0.1, mag*0.1), p0[1] + random.uniform(-mag*0.1, mag*0.1))
            p2 = (p1[0] + random.uniform(-mag*0.1, mag*0.1), p1[1] + random.uniform(-mag*0.1, mag*0.1))
            p3 = (p2[0] + random.uniform(-mag*0.1, mag*0.1), p2[1] + random.uniform(-mag*0.1, mag*0.1))
            seg = seg_b(p0, p1, p2, p3)
            p0, p1 = p0, p3

        f = run_oracle("PASSES_THROUGH_FILTER", f"PASSES_THROUGH_FILTER\n{p0[0]} {p0[1]}\n{p1[0]} {p1[1]}\n{c[0]} {c[1]}\n")
        if f not in ("TRUE", "FALSE"):
            emit(f"  INTERESTING passes {f} for type{ctype}")

def hunt_curve_ring_point_in(n=200):
    """Next slice starter: demonstrate POINT_IN_CURVE_RING with rings containing the new CurveType segments.
    (Full formatting and validation will be in the gens; here we show the syntax is accepted.)
    """
    emit("## HUNT (next slice): POINT_IN_CURVE_RING with Elliptic/Bezier rings (syntax demo)")
    # Hard-coded small examples using the supported syntax
    examples = [
        ("Bezier3(2) small", "POINT_IN_CURVE_RING\n2\nB 0 0 1 0.5 2 0 3 0\nC 3 0 0 0\n0.5 0.1\n"),
        ("Elliptic(1) small", "POINT_IN_CURVE_RING\n2\nE 1.5 1.5 1.5 1.0 0.0 0.0 6.28\nC 3 1.5 0 1.5\n1.5 1.5\n"),
    ]
    for name, stdin in examples:
        res = run_oracle("POINT_IN_CURVE_RING", stdin)
        emit(f"  {name}: {res}")

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--types", default="0,1,2")
    ap.add_argument("--budget", type=int, default=10000)
    args = ap.parse_args()
    wanted = [int(x) for x in args.types.split(",")]

    emit("# CurveType adversarial hunter (0=Circular, 1=Elliptic, 2=Bezier3)")
    emit(f"# budget={args.budget} types={wanted}")
    emit()

    if 0 in wanted or 1 in wanted or 2 in wanted:
        hunt_orientation_and_incircle(args.budget // 2)
    hunt_passes_and_noding(args.budget // 2)
    hunt_curve_ring_point_in(50)  # next slice starter

    emit("# hunter finished")

if __name__ == "__main__":
    main()
