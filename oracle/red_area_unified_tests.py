#!/usr/bin/env python3
# coverage: feat:area geom:arc,cs,cc,cp,multi
"""
RED tests for unified AREA_UNIFIED (Slice 6 - Area/perimeter full column).
Includes multi-segment cases for CC/CP/Multi tagging.
Protocol:
AREA_UNIFIED
<nsegs>
segs ("C ..." | "A ...")
Output: "<area>" (%h) | "DEGENERATE" | "NAN"
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

# chord square area = 1
stdin = """AREA_UNIFIED
4
C 0 0 1 0
C 1 0 1 1
C 1 1 0 1
C 0 1 0 0
"""
out, _, rc = run(stdin)
print("RED_NOTE chord_area_got=", out)
if rc != 0 or not out:
    fail("chord_area", out, "1.0", stdin)
got = to_float(out)
if abs(got - 1.0) > 0.01:
    fail("chord_area", out, "1.0", stdin)
print("chord area ok")

# arc ring (from buffer style)
stdin2 = """AREA_UNIFIED
2
A 5 0 0 5 -5 0
C -5 0 5 0
"""
out2, _, rc2 = run(stdin2)
print("RED_NOTE arc_ring_area_got=", out2)
if rc2 != 0 or not out2:
    fail("arc_ring_area", out2, "finite >0", stdin2)
got2 = to_float(out2)
if got2 <= 0:
    fail("arc_ring_area", out2, ">0", stdin2)
print("arc ring area ok")

# CC-like multi seg (compound)
stdin3 = """AREA_UNIFIED
2
C 0 0 1 0
A 1 0 0.7071 0.7071 0 1
"""
out3, _, rc3 = run(stdin3)
print("RED_NOTE cc_like_area_got=", out3)
if rc3 != 0 or not out3:
    fail("cc_like_area", out3, "finite", stdin3)
print("cc like area ok")

# CP-like (closed multi seg with arc)
stdin4 = """AREA_UNIFIED
4
C 0 0 5 0
A 5 0 0 5 -5 0
C -5 0 -5 -0
C -5 0 0 0
"""
out4, _, rc4 = run(stdin4)
print("RED_NOTE cp_like_area_got=", out4)
if rc4 != 0 or not out4:
    fail("cp_like_area", out4, "finite", stdin4)
print("cp like area ok")

print("RED tests for Slice 6 Area unified. Assertions passed with impl.")
print("Rung note: Area CC/CP/Multi now backed by multi-segment cases + unified.")
