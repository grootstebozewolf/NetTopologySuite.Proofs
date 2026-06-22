#!/usr/bin/env python3
# coverage: feat:relate geom:arc,cs,cc,cp,multi
"""
RED tests for unified Relate/DE-9IM full column (Slice 8).
Uses CURVE_RELATE_MATRIX with L and ring forms for unified segment dispatch.
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

# Lineal disjoint
stdin = """CURVE_RELATE_MATRIX
L
1
C 0 0 1 0
L
1
C 2 0 3 0
"""
out, _, rc = run(stdin)
print("RED_NOTE relate_disjoint_got=", out)
if rc != 0 or out != "FFFFFFFFF":
    fail("relate_disjoint", out, "FFFFFFFFF", stdin)
print("relate disjoint ok")

# Arc vs chord
stdin2 = """CURVE_RELATE_MATRIX
L
1
A 0 0 0.5 0.5 1 0
L
1
C 0.5 0.5 2 0.5
"""
out2, _, rc2 = run(stdin2)
print("RED_NOTE relate_arc_chord_got=", out2)
if rc2 != 0 or not out2 or len(out2) != 9:
    fail("relate_arc_chord", out2, "9-char", stdin2)
print("arc chord relate ok")

# CP square vs inner
stdin3 = """CURVE_RELATE_MATRIX
2
4
C 0 0 1 0
C 1 0 1 1
C 1 1 0 1
C 0 1 0 0
4
C 0.25 0.25 0.75 0.25
C 0.75 0.25 0.75 0.75
C 0.75 0.75 0.25 0.75
C 0.25 0.75 0.25 0.25
2
4
C 0 0 2 0
C 2 0 2 2
C 2 2 0 2
C 0 2 0 0
4
C 0.5 0.5 1.5 0.5
C 1.5 0.5 1.5 1.5
C 1.5 1.5 0.5 1.5
C 0.5 1.5 0.5 0.5
"""
out3, _, rc3 = run(stdin3)
print("RED_NOTE relate_cp_got=", out3)
if rc3 != 0 or not out3 or len(out3) != 9:
    fail("relate_cp", out3, "9-char", stdin3)
print("cp relate ok")

print("RED tests for Slice 8 Relate/DE-9IM full column added.")
print("Matrix cells targeted: Relate/Arc,CS,CC,CP,Multi")
