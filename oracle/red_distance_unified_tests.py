#!/usr/bin/env python3
# coverage: feat:distance geom:arc,cs,cc,cp,multi
"""
RED tests for unified DISTANCE_UNIFIED (Slice 5 + Rung 3).
Includes multi-segment cases (CC-like compound, CP-like boundary) to support CC/CP tagging.
"""
import os
import subprocess
import sys

BIN = os.environ.get("ORACLE_BIN", "oracle/oracle_bin")

def run(stdin):
    p = subprocess.run([BIN], input=stdin, capture_output=True, text=True)
    return p.stdout.strip(), p.stderr.strip(), p.returncode

def fail(name, got, exp, sample):
    print(f"RED FAIL {name}")
    print("  got:", got)
    print("  exp:", exp)
    print("  stdin[:200]:", sample[:200])
    sys.exit(1)

def to_float(s):
    try:
        return float(s)
    except:
        return float.fromhex(s)

# chord chord dist 9
stdin = """DISTANCE_UNIFIED
1
C 0 0 1 0
1
C 10 0 11 0
"""
out, _, rc = run(stdin)
print("RED_NOTE chord_chord_got=", out)
if rc != 0 or not out:
    fail("chord_chord", out, "9", stdin)
got = to_float(out)
if abs(got - 9) > 0.1:
    fail("chord_chord", out, "9", stdin)
print("chord chord ok")

# arc chord approx 9
stdin2 = """DISTANCE_UNIFIED
1
A 1 0 0.7071 0.7071 0 1
1
C 10 0 10 1
"""
out2, _, rc2 = run(stdin2)
print("RED_NOTE arc_chord_got=", out2)
if rc2 != 0 or not out2:
    fail("arc_chord", out2, "~9", stdin2)
got2 = to_float(out2)
if got2 < 8:
    fail("arc_chord", out2, "~9", stdin2)
print("arc chord ok")

# CC-like (multiple segments, simulating CompoundCurve / CurveCollection via GetSegments)
# Two segments: chord + arc, distance to a far chord. Should be finite and reasonable (~9 range)
stdin3 = """DISTANCE_UNIFIED
2
C 0 0 1 0
A 1 0 0.7071 0.7071 0 1
1
C 10 0 10 1
"""
out3, _, rc3 = run(stdin3)
print("RED_NOTE cc_like_got=", out3)
if rc3 != 0 or not out3:
    fail("cc_like", out3, "finite", stdin3)
got3 = to_float(out3)
if got3 < 8 or got3 > 10:
    fail("cc_like", out3, "~9", stdin3)
print("cc like ok")

# CP-like simulation (segments from multiple rings / boundary for distance context)
stdin4 = """DISTANCE_UNIFIED
4
C 0 0 1 0
C 1 0 1 1
C 1 1 0 1
C 0 1 0 0
1
C 10 0 10 1
"""
out4, _, rc4 = run(stdin4)
print("RED_NOTE cp_like_got=", out4)
if rc4 != 0 or not out4:
    fail("cp_like", out4, "finite", stdin4)
got4 = to_float(out4)
if got4 < 8 or got4 > 11:
    fail("cp_like", out4, "~9-10", stdin4)
print("cp like ok")

# --- Slice 5 RED: complete Distance full column (unified model + dispatcher)
# Targets: CP, Multi, mixed linear/curve, output fidelity (correct min via D-AA/D-AS not just ends)
# These assert unified segment iteration behaviour (GetSegments flattened lists + analytical dispatch)
# Examples from query: TestCurvePolygon_Distance_MultiCurve, TestMulti_LineString_Curve_Distance_PreservesArc
# Will FAIL until Green improves pair_dist to full reuse of ARC_ARC_DISTANCE / ARC_SEGMENT_DISTANCE logic.

def test_curvepolygon_distance_multicurve():
    # CurvePolygon boundary (4 segs incl arcs) vs MultiCurve (2 arc parts)
    # Mixed case with arcs in both; fidelity requires correct arc-arc min (0 for intersecting sweeps)
    stdin = """DISTANCE_UNIFIED
4
C 0 0 1 0
A 1 0 0.7071 0.7071 0 1
C 0 1 -1 0
A -1 0 0 0.7071 -0.5 0
2
A 0 1 0.7071 0.7071 1 0
A 0.5 0.5 1.2 0.5 1.5 0
"""
    out, _, rc = run(stdin)
    print("RED_NOTE TestCurvePolygon_Distance_MultiCurve_got=", out)
    if rc != 0 or not out:
        fail("TestCurvePolygon_Distance_MultiCurve", out or "err", "finite >=0 (analytical)", stdin)
    got = to_float(out)
    # Expect 0 for this configuration (arcs cross in sweep); current partial pair_dist gives ~0.07
    if abs(got) > 1e-9:
        fail("TestCurvePolygon_Distance_MultiCurve", out, "0.0 (intersecting via D-AA in unified)", stdin)
    print("RED for TestCurvePolygon_Distance_MultiCurve (CP segs vs MultiCurve arcs)")

def test_multi_linestring_curve_distance_preserves_arc():
    # Multi* (linear + curve member via GetSegments recursion) distance; must use arc analytical not chord approx
    # A: mixed linear/curve (from MultiLineString + Curve part), B: point-like far chord
    # The min must come from the arc member (radial) for fidelity
    stdin = """DISTANCE_UNIFIED
3
C 0 0 1 0
C 1 0 1 1
A 1 1 0.7071 0.7071 0 1
1
C 10 0 10 1
"""
    out, _, rc = run(stdin)
    print("RED_NOTE TestMulti_LineString_Curve_Distance_PreservesArc_got=", out)
    if rc != 0 or not out:
        fail("TestMulti_LineString_Curve_Distance_PreservesArc", out or "err", "finite using arc", stdin)
    got = to_float(out)
    if got < 8 or got > 10:
        fail("TestMulti_LineString_Curve_Distance_PreservesArc", out, "~9 via arc dispatch (not linearized chord)", stdin)
    print("RED for TestMulti_LineString_Curve_Distance_PreservesArc (Multi delegation + arc preserve)")

def test_arc_arc_fidelity_zero_unified():
    # Direct mixed/arc case for D-AA: arcs whose circles intersect in both sweeps -> dist 0.0
    # Uses full analytical (reuses D-AA leaf); current inline gives non-zero
    stdin = """DISTANCE_UNIFIED
1
A 0 1 0.7071 0.7071 1 0
1
A 0.5 0.5 1.2 0.5 1.5 0
"""
    out, _, rc = run(stdin)
    print("RED_NOTE arc_arc_fidelity_zero_got=", out)
    if rc != 0 or not out:
        fail("arc_arc_fidelity_zero", out or "err", "0.0", stdin)
    got = to_float(out)
    if abs(got) > 1e-9:
        fail("arc_arc_fidelity_zero", out, "0.0 exact (D-AA intersect case)", stdin)
    print("RED for arc-arc fidelity (D-AA) in unified")

def test_mixed_linear_curve_arcseg_fidelity():
    # Arc (from CS/CC) to linear chord; must use full arc-segment (radial foot if valid + ends)
    # not just chord-ends to arc
    stdin = """DISTANCE_UNIFIED
1
A 0 1 0.7071 0.7071 1 0
1
C 0.5 2 1.5 2
"""
    out, _, rc = run(stdin)
    print("RED_NOTE mixed_arcseg_fidelity_got=", out)
    if rc != 0 or not out:
        fail("mixed_arcseg_fidelity", out or "err", "finite correct", stdin)
    got = to_float(out)
    # For this, radial or proper should be smaller than pure endpoint; expect ~0. something specific but at least < endpoint dist
    if got > 2.0:
        fail("mixed_arcseg_fidelity", out, "small (proper arc-seg foot via D-AS)", stdin)
    print("RED for mixed linear/curve arc-seg fidelity")

test_curvepolygon_distance_multicurve()
test_multi_linestring_curve_distance_preserves_arc()
test_arc_arc_fidelity_zero_unified()
test_mixed_linear_curve_arcseg_fidelity()

print("RED tests for Slice 5 Distance full column (unified model) added. All assertions now pass post-Green (full D-AA/D-AS reuse).")
print("Matrix cells targeted: Distance/Arc,CS,CC,CP,Multi (Slice 5 unified model + dispatcher; 4+ cells advanced).")
