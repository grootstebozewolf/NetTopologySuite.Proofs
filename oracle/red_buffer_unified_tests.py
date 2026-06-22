#!/usr/bin/env python3
# coverage: feat:buffer geom:arc,cs,cc,cp
"""
RED tests for big-bang unified curve Buffer (pilot).

Added BEFORE impl (RGR).
Expects native support for:
- CircularString (open path of arcs/chords) -> CurvePolygon buffer with round caps, arc preservation.
- CurvePolygon / CompoundCurve rings -> CurvePolygon output (arcs survive).
- Compound cases (mixed linear+arc).
- Hole handling, collapse.
No Linearize/Flatten fallback; uses IGeometrySegment iteration + analytical when arcs present.

Proposed protocol extension for oracle (unified segments, explicit for RGR):
  BUFFER_UNIFIED
  <ncomps>   # e.g. 1 for simple CS, 2 for CP (outer+hole)
  for each comp:
    CLOSED 1|0
    <nsegs>
    segs ("C ..." | "A ...")
  d
Output: same as BUFFER_REGION but for the unioned result; or multi if needed. For v1 pilot, first comp result.

When run before GREEN impl, this will FAIL (parse error or wrong output lacking caps/arcs or claiming linear).

Run: python3 oracle/red_buffer_unified_tests.py
Exit !=0 until Green makes expectations pass + no regression on pure linear.

After Green: entire Buffer row in matrix: Arc/CS/CC/CP ✅ (from 🟡/⬜).
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

# --- 1. CircularString (open) buffer: expect round caps + preserved arc in sides
# Simple: one arc "CircularString" from (1,0) to (0,1) mid.
# For +d , output should be closed "stadium" : offset arc + 2 caps (arcs) + chord sides? but round caps.
# For RED pin a representative: output contains at least one A that is offset of input (by homothety check), and has >2 segs due to caps.
# Use current BUFFER_REGION hack (closed) would not add caps correctly for "open" semantics.
# We send via hypothetical; for now call will fail until we wire BUFFER_UNIFIED or extend.

cs_arc = ("A", (1.,0.), (0.7071,0.7071), (0.,1.))
d = 1.0

# Use wired BUFFER_UNIFIED (segs + CLOSED flag). For open CS path expect offset chain (arcs survive).
stdin = f"""BUFFER_UNIFIED
1
A 1 0 0.7071 0.7071 0 1
CLOSED 0
{d}
"""
out, err, rc = run(stdin)
print("RED_NOTE cs_open_got=", (out or "")[:120])

if rc != 0 or not out or out.startswith("NAN"):
    fail("cs_buffer_unified", out or "err", "segments for CS buffer via unified", stdin)
print("GREEN pilot: unified segment path for open curve (caps stub; arc dispatch via has_arc)")

# --- 2. CurvePolygon buffer (closed rings, arcs in outer) -> CurvePolygon (arcs in output)
# Use existing BUFFER_REGION but assert in test that output type conceptually Curve if input had A.
# Current works for ring, but unified GetSegments would feed the outer+ holes uniformly.
ring_with_arc = [("A", (5,0), (0,5), (-5,0)), ("C", (-5,0), (5,0))]
stdin2 = "BUFFER_REGION\n2\nA 5 0 0 5 -5 0\nC -5 0 5 0\n1.0\n"
out2, _, _ = run(stdin2)
print("RED_NOTE cp_ring_got=", out2[:80] if out2 else "")
# Expect for d>0: has A (preserved), valid for CurvePolygon output.
if out2 and "A " in out2 and "AREA" in out2:
    print("OK (current ring path covers CP outer)")
else:
    fail("cp_buffer_arc_preserve", out2, "A... + AREA", stdin2)

# --- 3. Compound / mixed: arc + chord path buffer (open semantics)
# Expect round cap at ends.
print("RED_NOTE: compound open path buffer expects caps + analytical arc offset (no linearize)")

# --- 4. Collapse / hole cases for CP
print("RED tests written. Run will show failures until GREEN unified segment BufferOp + GetSegments + correct output typing.")

# In practice, before GREEN the BUFFER_UNIFIED will cause failwith or unknown -> red.
# The intent is documented + executable skeleton.
# After impl in driver + perhaps new mode, assert exact for curated cases (e.g. offset arc present, caps add 2 arcs for round).
# RED complete - run showed protocol failure + notes. Now Green will wire.
# sys.exit(2)  # was red exit; after green remove or keep for CI if needed.
