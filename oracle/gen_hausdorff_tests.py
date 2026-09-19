#!/usr/bin/env python3
# =============================================================================
# oracle/gen_hausdorff_tests.py
# -----------------------------------------------------------------------------
# Checks for HAUSDORFF_DIRECTED / HAUSDORFF_SYMM (extracted
# HausdorffDiscreteQ.q_ddh_sq / q_hsymm_sq; #423 ticket-10 line 2).
# Ground truth: an independent exact Fraction implementation of the same
# vertices-against-locus kernel (clamped point-to-segment, min over edges,
# max over vertices), plus the locked JTS pair.
#
#   H1  JTS-PAIR        A=(0 0,100 0,10 100) B=(0 100,0 10,80 10) → 500/1 (√500)
#   H2  JTS-PAIR-BACK   h(B,A) matches the Fraction oracle
#   H3  SYMM-IS-MAX     HAUSDORFF_SYMM = max of the two directed squares
#   H4  SYMM-SYMMETRIC  swapping operands leaves HAUSDORFF_SYMM unchanged
#   H5  IDENTICAL       h(A,A) = 0
#   H6  ASYMMETRY       (0 0,1 0) vs (0 2,3 2): 4/1 forward, 8/1 backward
#   H7  DECIMALS        exact decimals: (0.5 0,1.5 0) vs (0 0.25,2 0.25) → 1/16
#   H8  SINGLE-POINT    a 1-point operand → NAN (proven domain needs an edge)
#   H9  BAD-TOKEN       "1e3" / "+7" / "0x7" → NAN
#   H10 REPLAY          two calls on the JTS pair agree
#   H11 FLOAT-IS-SQRT   the float token is %.17g of sqrt(num/den)
#
# Run from repo root:
#   python3 oracle/gen_hausdorff_tests.py > oracle/hausdorff_tests.txt
# Exit nonzero iff a proven invariant is violated.
# =============================================================================
import math
import os
import subprocess
import sys
from fractions import Fraction as F

BIN = os.environ.get("ORACLE_BIN", "oracle/oracle_bin")

violations = 0


def emit(s=""):
    print(s)


def run_raw(stdin):
    out = subprocess.run([BIN], input=stdin, capture_output=True, text=True)
    if out.returncode != 0:
        return f"ERR rc={out.returncode} {out.stderr.strip()}"
    return out.stdout.strip().splitlines()[-1] if out.stdout.strip() else "ERR empty"


def payload(mode, A, B):
    lines = [mode, str(len(A))] + [f"{x} {y}" for x, y in A] + [str(len(B))] + [f"{x} {y}" for x, y in B]
    return "\n".join(lines) + "\n"


def run(mode, A, B):
    return run_raw(payload(mode, A, B))


# --- independent exact reference (Fractions) --------------------------------
def seg_dist_sq(a, b, p):
    ax, ay = a
    bx, by = b
    px, py = p
    l2 = (bx - ax) ** 2 + (by - ay) ** 2
    if l2 == 0:
        t = F(0)
    else:
        t = ((px - ax) * (bx - ax) + (py - ay) * (by - ay)) / l2
        t = max(F(0), min(F(1), t))
    qx, qy = ax + t * (bx - ax), ay + t * (by - ay)
    return (px - qx) ** 2 + (py - qy) ** 2


def ddh_sq(A, B):
    A = [(F(x), F(y)) for x, y in A]
    B = [(F(x), F(y)) for x, y in B]
    edges = list(zip(B, B[1:]))
    return max(min(seg_dist_sq(a, b, p) for a, b in edges) for p in A)


def wire(sq):
    h = math.sqrt(float(sq.numerator) / float(sq.denominator))
    return f"{h:.17g} {sq.numerator}/{sq.denominator}"


def expect(label, got, want):
    global violations
    if got != want:
        violations += 1
        emit(f"!! {label}: got {got!r} want {want!r}")
    else:
        emit(f"ok {label}: {got}")


JTS_A = [("0", "0"), ("100", "0"), ("10", "100")]
JTS_B = [("0", "100"), ("0", "10"), ("80", "10")]


def main():
    if not os.path.isfile(BIN):
        emit(f"SKIP: {BIN} not built (oracle/oracle_bin is gitignored).")
        emit("Build via the pinned toolchain, then re-run.")
        return 0

    emit("# HAUSDORFF_DIRECTED / HAUSDORFF_SYMM q_ddh_sq / q_hsymm_sq (HausdorffDiscreteQ.v)")
    fwd = ddh_sq(JTS_A, JTS_B)
    back = ddh_sq(JTS_B, JTS_A)
    if fwd != 500:
        global violations
        violations += 1
        emit(f"!! reference: JTS pair forward square is {fwd}, expected 500")
    expect("H1 JTS pair directed", run("HAUSDORFF_DIRECTED", JTS_A, JTS_B), wire(F(500)))
    expect("H2 JTS pair backward", run("HAUSDORFF_DIRECTED", JTS_B, JTS_A), wire(back))
    expect("H3 symm is max", run("HAUSDORFF_SYMM", JTS_A, JTS_B), wire(max(fwd, back)))
    expect("H4 symm symmetric", run("HAUSDORFF_SYMM", JTS_B, JTS_A), run("HAUSDORFF_SYMM", JTS_A, JTS_B))
    expect("H5 identical", run("HAUSDORFF_DIRECTED", JTS_A, JTS_A), wire(F(0)))
    asy_a = [("0", "0"), ("1", "0")]
    asy_b = [("0", "2"), ("3", "2")]
    expect("H6 asymmetry forward", run("HAUSDORFF_DIRECTED", asy_a, asy_b), wire(F(4)))
    expect("H6 asymmetry backward", run("HAUSDORFF_DIRECTED", asy_b, asy_a), wire(F(8)))
    dec_a = [("0.5", "0"), ("1.5", "0")]
    dec_b = [("0", "0.25"), ("2", "0.25")]
    expect("H7 decimals exact", run("HAUSDORFF_DIRECTED", dec_a, dec_b), wire(F(1, 16)))
    expect("H8 single point NAN", run("HAUSDORFF_DIRECTED", JTS_A, [("0", "0")]), "NAN")
    expect("H9 exponent token NAN", run_raw("HAUSDORFF_DIRECTED\n2\n1e3 0\n1 0\n2\n0 2\n3 2\n"), "NAN")
    expect("H9 leading-plus NAN", run_raw("HAUSDORFF_DIRECTED\n2\n+7 0\n1 0\n2\n0 2\n3 2\n"), "NAN")
    expect("H9 hex NAN", run_raw("HAUSDORFF_SYMM\n2\n0x7 0\n1 0\n2\n0 2\n3 2\n"), "NAN")
    a = run("HAUSDORFF_DIRECTED", JTS_A, JTS_B)
    b = run("HAUSDORFF_DIRECTED", JTS_A, JTS_B)
    expect("H10 replay", a, b)
    toks = a.split()
    if len(toks) == 2 and "/" in toks[1]:
        n, d = toks[1].split("/")
        expect("H11 float is sqrt of companion", toks[0], f"{math.sqrt(float(n) / float(d)):.17g}")
    else:
        violations += 1
        emit(f"!! H11 malformed wire {a!r}")

    if violations:
        emit(f"::error::HAUSDORFF_* violated {violations} proven invariant(s).")
        return 1
    emit("HAUSDORFF_DIRECTED / HAUSDORFF_SYMM invariants H1-H11 ok.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
