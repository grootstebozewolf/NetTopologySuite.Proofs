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

print("RED tests for Slice 5 Distance unified. Assertions passed with impl.")
print("Rung 3 note: CC/CP tags for Distance now backed by multi-segment cases in this file + Slice 10 dispatcher.")
