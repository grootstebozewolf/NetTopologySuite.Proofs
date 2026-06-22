#!/usr/bin/env python3
# coverage: feat:arc-len geom:arc,cs,cc,cp,multi
"""
RED tests for unified LENGTH_UNIFIED (Slice 11: Arc / chord length CC/CP + Rung 3 oracle tags).
(ARC_LEN_UNIFIED also supported as alias for the arc-len column.)
Protocol:
  LENGTH_UNIFIED
  <nsegs>
  segs...   ("C x1 y1 x2 y2" | "A x1 y1 x2 y2 x3 y3")
Output: "<len>" (%h) | "DEGENERATE" | "NAN"
Uses arc length (r*theta via invariants) for arcs + euclid chord for linears.
Reuses ARC_LENGTH kernel; sums for compound / CC / CP (perimeter) segments.
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
    print("  stdin[:300]:", sample[:300])
    sys.exit(1)

def to_float(s):
    try:
        return float(s)
    except:
        return float.fromhex(s)

# Simple chord length == 1
stdin = """LENGTH_UNIFIED
1
C 0 0 1 0
"""
out, _, rc = run(stdin)
print("RED_NOTE chord_len_got=", out)
if rc != 0 or not out:
    fail("chord_len", out, "1.0", stdin)
got = to_float(out)
if abs(got - 1.0) > 1e-9:
    fail("chord_len", out, "1.0", stdin)
print("chord length ok")

# Two chords, sum lengths = 2
stdin2 = """LENGTH_UNIFIED
2
C 0 0 1 0
C 1 0 2 0
"""
out2, _, rc2 = run(stdin2)
print("RED_NOTE chords_sum_got=", out2)
if rc2 != 0 or not out2:
    fail("chords_sum", out2, "2.0", stdin2)
got2 = to_float(out2)
if abs(got2 - 2.0) > 1e-9:
    fail("chords_sum", out2, "2.0", stdin2)
print("chords sum ok")

# Arc length: quarter unit circle (A controls for 90 deg)
# Matches ARC_LENGTH output: 0x1.921fb54442d19p+0 == pi/2
stdin3 = """LENGTH_UNIFIED
1
A 1 0 0.7071067811865475 0.7071067811865476 0 1
"""
out3, _, rc3 = run(stdin3)
print("RED_NOTE arc_len_got=", out3)
if rc3 != 0 or not out3:
    fail("arc_len", out3, "pi/2", stdin3)
got3 = to_float(out3)
if abs(got3 - 1.57079632679) > 0.001:
    fail("arc_len", out3, "~1.5708", stdin3)
print("arc length ok")

# Mixed chord + arc (simulates CompoundCurve / CC segments)
# chord len1 + quarter arc ~ 1 + 1.5708 = 2.5708
stdin4 = """LENGTH_UNIFIED
2
C 0 0 1 0
A 1 0 0.7071067811865475 0.7071067811865476 0 1
"""
out4, _, rc4 = run(stdin4)
print("RED_NOTE mixed_len_got=", out4)
if rc4 != 0 or not out4:
    fail("mixed_len", out4, "~2.5708", stdin4)
got4 = to_float(out4)
if got4 < 2.5 or got4 > 2.65:
    fail("mixed_len", out4, "~2.5708", stdin4)
print("mixed chord+arc ok")

# Simulate CP perimeter (outer + hole as chords for pilot): square 4 + inner small square ~4 + 2 =6? use simple
# For red: two separate closed-ish but sum segs for perimeter
stdin5 = """LENGTH_UNIFIED
8
C 0 0 1 0
C 1 0 1 1
C 1 1 0 1
C 0 1 0 0
C 0.25 0.25 0.75 0.25
C 0.75 0.25 0.75 0.75
C 0.75 0.75 0.25 0.75
C 0.25 0.75 0.25 0.25
"""
out5, _, rc5 = run(stdin5)
print("RED_NOTE cp_perim_like_got=", out5)
if rc5 != 0 or not out5:
    fail("cp_perim", out5, "~6", stdin5)
got5 = to_float(out5)
if abs(got5 - 6.0) > 0.01:
    fail("cp_perim", out5, "6.0", stdin5)
print("cp-like perimeter sum ok")

print("RED tests for Slice 11 Arc/chord length unified. Assertions passed with unified model (Slice 11).")
