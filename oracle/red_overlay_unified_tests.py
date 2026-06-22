#!/usr/bin/env python3
# coverage: feat:overlay geom:arc,cs,cc,cp,multi
"""
RED tests for unified OverlayNG (Slice 7 - Overlay unification).
Tests mixed, CP, Multi cases using OVERLAY_UNIFIED protocol (nsegs + segs).
Expects "CURVE" prefix for arc inputs (arc preservation via hasArc dispatch).
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

# Linear case
stdin = """OVERLAY_UNIFIED
1
C 0 0 1 0
1
C 0 0 1 0
"""
out, _, rc = run(stdin)
print("RED_NOTE overlay_linear_got=", out)
if rc != 0 or out != "212FF1FF2":
    fail("overlay_linear", out, "212FF1FF2", stdin)
print("linear overlay ok")

# Arc case - expect CURVE prefix for fidelity
stdin2 = """OVERLAY_UNIFIED
1
A 1 0 0.7071 0.7071 0 1
1
C 0 0 1 0
"""
out2, _, rc2 = run(stdin2)
print("RED_NOTE overlay_arc_got=", out2)
if rc2 != 0 or "CURVE" not in out2:
    fail("overlay_arc", out2, "CURVE...", stdin2)
print("arc overlay CURVE prefix ok (preserves arc)")

# CP-like mixed
stdin3 = """OVERLAY_UNIFIED
2
C 0 0 1 0
A 1 0 0.7071 0.7071 0 1
1
C 2 0 3 0
"""
out3, _, rc3 = run(stdin3)
print("RED_NOTE overlay_cp_mixed_got=", out3)
if rc3 != 0 or "CURVE" not in (out3 or ""):
    fail("overlay_cp_mixed", out3, "CURVE prefix for CP mixed", stdin3)
print("CP mixed ok")

# Multi delegation simulation (n>1)
stdin4 = """OVERLAY_UNIFIED
2
C 0 0 1 0
C 1 0 1 1
2
C 2 0 3 0
A 3 0 3.7071 0.7071 4 1
"""
out4, _, rc4 = run(stdin4)
print("RED_NOTE overlay_multi_got=", out4)
if rc4 != 0 or "CURVE" not in (out4 or ""):
    fail("overlay_multi", out4, "CURVE for Multi with arc", stdin4)
print("Multi overlay ok")

print("RED tests for Slice 7 Overlay unification added.")
print("Matrix cells targeted: Overlay/Arc,CS,CC,CP,Multi")
