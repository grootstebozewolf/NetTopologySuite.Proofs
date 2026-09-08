#!/usr/bin/env python3
# =============================================================================
# oracle/gen_i_circular_tests.py
# -----------------------------------------------------------------------------
# Checks for I_CIRCULAR (extracted I_circles_z).
# Ground truth: CircularCookZ.v partition + locked witnesses.
#
#   I1  LOCKED-HIT       (0,0) r=5 vs (7,0) r=5 → HIT 0 1
#   I2  DISJOINT-EMPTY   (0,0) r=5 vs (20,0) r=5 → EMPTY
#   I3  COINCIDENT       (0,0) r=5 vs (0,0) r=5 → DECLINE
#   I4  ZERO-RADIUS      r1=0 → DECLINE
#   I5  EXTERNAL-KISS    d = r1+r2 → TOUCH 0
#   I6  REPLAY           two calls on the locked pair mint the same hens
#   I7  INTERNAL-KISS    (0,0) r=5 vs (3,0) r=2 → TOUCH 0
#   I8  UNEQUAL-RADII    locked pair r2=8 → HIT 0 1 (not the I5 kiss)
#   I9  NON-INTEGER      7.5 / +7 / 0x7 rejected (NAN); digits-only grammar
#   I10 NEGATIVE-CENTRE  (0,0) r=5 vs (-7,0) r=5 → HIT 0 1
#
# Run from repo root:
#   python3 oracle/gen_i_circular_tests.py > oracle/i_circular_tests.txt
# Exit nonzero iff a proven invariant is violated.
# =============================================================================
import os
import subprocess
import sys

BIN = os.environ.get("ORACLE_BIN", "oracle/oracle_bin")

violations = 0


def emit(s=""):
    print(s)


def run_raw(stdin):
    out = subprocess.run([BIN], input=stdin, capture_output=True, text=True)
    if out.returncode != 0:
        return f"ERR rc={out.returncode} {out.stderr.strip()}"
    return out.stdout.strip().splitlines()[-1] if out.stdout.strip() else "ERR empty"


def run(o1x, o1y, r1, o2x, o2y, r2):
    stdin = f"I_CIRCULAR\n{o1x} {o1y} {r1}\n{o2x} {o2y} {r2}\n"
    return run_raw(stdin)


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

    emit("# I_CIRCULAR I_circles_z (CircularCookZ.v)")
    expect("I1 locked hit", run(0, 0, 5, 7, 0, 5), "HIT 0 1")
    expect("I2 disjoint empty", run(0, 0, 5, 20, 0, 5), "EMPTY")
    expect("I3 coincident decline", run(0, 0, 5, 0, 0, 5), "DECLINE")
    expect("I4 zero radius", run(0, 0, 0, 7, 0, 5), "DECLINE")
    expect("I5 external kiss", run(0, 0, 5, 10, 0, 5), "TOUCH 0")
    a = run(0, 0, 5, 7, 0, 5)
    b = run(0, 0, 5, 7, 0, 5)
    expect("I6 replay same hens", a, b)
    if a != "HIT 0 1":
        global violations
        violations += 1
        emit(f"!! I6 expected HIT 0 1 on replay, got {a!r}")
    expect("I7 internal kiss", run(0, 0, 5, 3, 0, 2), "TOUCH 0")
    expect("I8 unequal radii hit", run(0, 0, 5, 7, 0, 8), "HIT 0 1")
    expect(
        "I9 non-integer rejected",
        run_raw("I_CIRCULAR\n0 0 5\n7.5 0 5\n"),
        "NAN",
    )
    expect(
        "I9 leading-plus rejected",
        run_raw("I_CIRCULAR\n0 0 5\n+7 0 5\n"),
        "NAN",
    )
    expect(
        "I9 hex rejected",
        run_raw("I_CIRCULAR\n0 0 5\n0x7 0 5\n"),
        "NAN",
    )
    expect("I10 negative centre hit", run(0, 0, 5, -7, 0, 5), "HIT 0 1")

    if violations:
        emit(f"::error::I_CIRCULAR violated {violations} proven invariant(s).")
        return 1
    emit("I_CIRCULAR invariants I1-I10 ok.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
