#!/usr/bin/env python3
# =============================================================================
# oracle/gen_i_circular_tests.py
# -----------------------------------------------------------------------------
# Differential-ready checks for I_CIRCULAR (extracted Year-1 circular 𝓘).
# Ground truth is CircularCookZ.v (vm_compute lemmas on the locked fixture).
#
#   I1  LOCKED-HIT       (0,0) r=5 vs (7,0) r=5 → HIT 0 1
#   I2  DISJOINT-EMPTY   (0,0) r=5 vs (20,0) r=5 → EMPTY
#   I3  COINCIDENT       (0,0) r=5 vs (0,0) r=5 → DECLINE
#   I4  ZERO-RADIUS      r1=0 → DECLINE
#   I5  EXTERNAL-KISS    d = r1+r2 → DECLINE
#   I6  REPLAY           two calls on the locked pair mint the same hens
#
# Not OverlayNGCurve. Not ARC_ARC_XY node coordinates. Not #671 resultant.
#
# Run from repo root:
#   python3 oracle/gen_i_circular_tests.py
# Exit nonzero iff a proven invariant is violated.
# =============================================================================
import os
import subprocess
import sys

BIN = os.environ.get("ORACLE_BIN", "oracle/oracle_bin")

violations = 0


def emit(s=""):
    print(s)


def run(o1x, o1y, r1, o2x, o2y, r2):
    stdin = f"I_CIRCULAR\n{o1x} {o1y} {r1}\n{o2x} {o2y} {r2}\n"
    out = subprocess.run([BIN], input=stdin, capture_output=True, text=True)
    if out.returncode != 0:
        return f"ERR rc={out.returncode} {out.stderr.strip()}"
    return out.stdout.strip().splitlines()[-1] if out.stdout.strip() else "ERR empty"


def expect(label, got, want):
    global violations
    if got != want:
        violations += 1
        emit(f"!! {label}: got {got!r} want {want!r}")
    else:
        emit(f"ok {label}: {got}")


def main():
    if not os.path.isfile(BIN):
        emit(f"SKIP: {BIN} not built (oracle/oracle_bin is gitignored).")
        emit("Build via the pinned toolchain, then re-run.")
        return 0

    emit("# I_CIRCULAR extracted 𝓘 (CircularCookZ.v)")
    expect("I1 locked hit", run(0, 0, 5, 7, 0, 5), "HIT 0 1")
    expect("I2 disjoint empty", run(0, 0, 5, 20, 0, 5), "EMPTY")
    expect("I3 coincident decline", run(0, 0, 5, 0, 0, 5), "DECLINE")
    expect("I4 zero radius", run(0, 0, 0, 7, 0, 5), "DECLINE")
    expect("I5 external kiss", run(0, 0, 5, 10, 0, 5), "DECLINE")
    a = run(0, 0, 5, 7, 0, 5)
    b = run(0, 0, 5, 7, 0, 5)
    expect("I6 replay same hens", a, b)
    if a != "HIT 0 1":
        global violations
        violations += 1
        emit(f"!! I6 expected HIT 0 1 on replay, got {a!r}")

    if violations:
        emit(f"::error::I_CIRCULAR violated {violations} proven invariant(s).")
        return 1
    emit("I_CIRCULAR invariants I1-I6 ok.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
