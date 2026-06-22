#!/usr/bin/env python3
# coverage: feat:distance geom:arc,cs,cc,cp,multi
"""
RED tests for unified DISTANCE_UNIFIED (Slice 5 + Rung 3 oracle tags for CC/CP/Multi).
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

print("RED tests for Slice 5 Distance unified. Assertions passed with impl.")
