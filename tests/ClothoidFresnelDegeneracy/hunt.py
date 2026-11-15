#!/usr/bin/env python3
"""Exact-degeneracy sweep of the extracted clothoid integrals (Step 6a).

Drives `oracle_bin` in mode B64_CLOTHOID (extracted B64_ClothoidMap.cm_accept /
cm_Icos / cm_Isin) and compares it with an exact-rational reference for

    Icos(A, s) = int_0^s cos(u^2 / (2 A^2)) du
    Isin(A, s) = sigma * int_0^s sin(u^2 / (2 A^2)) du

The reference is the alternating power series summed in `fractions.Fraction`
with its remainder bound, so every comparison is exact arithmetic on the
doubles the oracle saw.  The proved contract is
B64_ClothoidMap.b64_clothoid_Icos_err / _Isin_err: on accepted input the
result is finite and within A / 2^41 of the integral.

Reports every disagreement; patches nothing.

usage: ORACLE=path/to/oracle_bin python3 hunt.py
exit:  0 no bug · 1 at least one bug · 2 oracle missing / unusable
"""
import os
import struct
import subprocess
import sys
from fractions import Fraction

ORACLE = os.environ.get(
    "ORACLE", ".ci-artifacts/oracle-bin-linux/oracle_bin")
BOUND_DEN = 2 ** 41          # contract: |err| <= A / 2^41
R2 = Fraction(6369051672525773, 2 ** 52)   # cm_r2, the oracle's sqrt(2)
XMAX = Fraction(5, 2)        # fresnel_accept_ok: |x| <= 5/2


def bits(x):
    return "%016x" % struct.unpack(">Q", struct.pack(">d", x))[0]


def unbits(h):
    return struct.unpack(">d", struct.pack(">Q", int(h, 16)))[0]


def run(cases):
    """cases: list of (A, s, neg) -> list of None (declined) or (Icos, Isin)."""
    # the oracle reads its mode from the first stdin line
    inp = "B64_CLOTHOID\n" + "".join(
        "%s %s %d\n" % (bits(a), bits(s), 1 if n else 0) for a, s, n in cases)
    out = subprocess.run([ORACLE], input=inp, text=True,
                         capture_output=True, check=True).stdout.split("\n")
    res = []
    for line in out:
        line = line.strip()
        if not line:
            continue
        if line.startswith("DECLINE"):
            res.append(None)
        else:
            c, s = line.split()
            res.append((unbits(c), unbits(s)))
    if len(res) != len(cases):
        raise RuntimeError("oracle answered %d of %d" % (len(res), len(cases)))
    return res


def exact(A, s, neg):
    """(Icos, Isin, remainder) as Fractions; |true - returned| <= remainder."""
    A, s = Fraction(A), Fraction(s)
    q = s * s / (2 * A * A)                 # heading at s
    q2 = q * q
    tol = abs(A) / 2 ** 120
    # C = s * sum (-1)^n q^(2n) / ((2n)! (4n+1))
    # S = s * sum (-1)^n q^(2n+1) / ((2n+1)! (4n+3))
    tc, ts = Fraction(1), q                 # q^(2n)/(2n)!, q^(2n+1)/(2n+1)!
    C = S = Fraction(0)
    n = 0
    while True:
        dc, ds = tc / (4 * n + 1), ts / (4 * n + 3)
        C += dc if n % 2 == 0 else -dc
        S += ds if n % 2 == 0 else -ds
        tc = tc * q2 / ((2 * n + 1) * (2 * n + 2))
        ts = ts * q2 / ((2 * n + 2) * (2 * n + 3))
        n += 1
        # terms decrease once q^2 < (2n+1)(2n+2); then the tail is below
        # the next term (alternating series).
        if q2 < (2 * n + 1) * (2 * n + 2) and \
                abs(s) * max(tc / (4 * n + 1), ts / (4 * n + 3)) <= tol:
            break
    rem = abs(s) * (tc / (4 * n + 1) + ts / (4 * n + 3))
    S = -S if neg else S
    return s * C, s * S, rem


def spec_accept(A, s):
    """Mirror of cm_accept on the real side, for the boundary cases only."""
    A, s = Fraction(A), Fraction(s)
    return (Fraction(1, 2 ** 500) <= A <= 2 ** 500 and abs(s) <= 2 ** 500
            and abs(s / (R2 * A)) <= XMAX)


class Tally:
    def __init__(self):
        self.ok = self.warn = self.bug = 0
        self.lines = []

    def note(self, kind, msg):
        setattr(self, kind, getattr(self, kind) + 1)
        if kind != "ok":
            self.lines.append("%-4s %s" % (kind.upper(), msg))


def hx(x):
    return float(x).hex()


def check_accuracy(t, tag, cases):
    worst = Fraction(0)
    for (A, s, neg), r in zip(cases, run(cases)):
        if r is None:
            if spec_accept(A, s):
                # rounding of s / (r2 A) may push a boundary input out;
                # a decline is always safe, so this is a note, not a bug.
                t.note("warn", "%s: declined inside |x| <= 5/2: A=%s s=%s"
                       % (tag, hx(A), hx(s)))
            else:
                t.note("ok", "")
            continue
        ec, es, rem = exact(A, s, neg)
        lim = Fraction(A) / BOUND_DEN + rem
        for name, got, ref in (("Icos", r[0], ec), ("Isin", r[1], es)):
            if got != got or got in (float("inf"), float("-inf")):
                t.note("bug", "%s: %s not finite: A=%s s=%s neg=%d"
                       % (tag, name, hx(A), hx(s), neg))
                continue
            err = abs(Fraction(got) - ref)
            worst = max(worst, err * BOUND_DEN / Fraction(A))
            if err > lim:
                t.note("bug", "%s: %s off by %.3g A/2^41: A=%s s=%s neg=%d got=%s"
                       % (tag, name, float(err * BOUND_DEN / Fraction(A)),
                          hx(A), hx(s), neg, hx(got)))
            else:
                t.note("ok", "")
    return float(worst)


def main():
    if not os.path.exists(ORACLE):
        print("oracle not found: %s (set ORACLE)" % ORACLE)
        return 2
    t = Tally()
    two = lambda k: 2.0 ** k
    As = [1.0, 3.0, 0.1, two(-500), two(500), two(-300) * 1.7, two(200) * 1.3,
          1e-3, 12345.678, 0.7071067811865476]

    def s_of(A, x):          # nearest double to x * r2 * A
        return float(Fraction(x) * R2 * Fraction(A))

    # D1  s = +0 and -0: the integral is 0.
    cases = [(A, z, n) for A in As for z in (0.0, -0.0) for n in (0, 1)]
    for (A, s, n), r in zip(cases, run(cases)):
        if r is None:
            t.note("warn", "D1 zero: declined A=%s" % hx(A))
        elif r[0] != 0.0 or r[1] != 0.0:
            t.note("bug", "D1 zero: nonzero at s=%s A=%s: %s %s"
                   % (hx(s), hx(A), hx(r[0]), hx(r[1])))
        else:
            t.note("ok", "")

    xs = [Fraction(n, d) for n, d in
          ((1, 2 ** 60), (1, 2 ** 20), (1, 1000), (1, 9), (1, 3), (1, 2),
           (2, 3), (1, 1), (5, 4), (3, 2), (7, 4), (2, 1), (9, 4), (12, 5),
           (249, 100), (5, 2))]

    # D2  odd in s, D3 sign flag: bit-exact symmetries of the integrals.
    base = [(A, s_of(A, x), 0) for A in As for x in xs]
    pos = run(base)
    negs = run([(A, -s, 0) for A, s, _ in base])
    flag = run([(A, s, 1) for A, s, _ in base])
    for (A, s, _), p, m, f in zip(base, pos, negs, flag):
        if (p is None) != (m is None) or (p is None) != (f is None):
            t.note("bug", "D2/D3: accept differs under s -> -s or the sign "
                          "flag: A=%s s=%s" % (hx(A), hx(s)))
            continue
        if p is None:
            t.note("ok", "")
            continue
        if bits(m[0]) != bits(-p[0]) or bits(m[1]) != bits(-p[1]):
            t.note("bug", "D2 odd in s: A=%s s=%s: (%s,%s) vs (%s,%s)"
                   % (hx(A), hx(s), hx(p[0]), hx(p[1]), hx(m[0]), hx(m[1])))
        else:
            t.note("ok", "")
        if bits(f[0]) != bits(p[0]) or bits(f[1]) != bits(-p[1]):
            t.note("bug", "D3 sign flag: A=%s s=%s: (%s,%s) vs (%s,%s)"
                   % (hx(A), hx(s), hx(p[0]), hx(p[1]), hx(f[0]), hx(f[1])))
        else:
            t.note("ok", "")

    # D4  (A, s) -> (2^k A, 2^k s) scales both integrals by exactly 2^k.
    mid = [(A, s_of(A, x)) for A in (1.0, 3.0, 0.1, 12345.678)
           for x in xs]
    ref = run([(A, s, 0) for A, s in mid])
    for k in (-200, -53, -1, 1, 52, 200):
        sc = run([(A * two(k), s * two(k), 0) for A, s in mid])
        for (A, s), p, q in zip(mid, ref, sc):
            if p is None or q is None:
                if (p is None) != (q is None):
                    t.note("bug", "D4 scale 2^%d: accept differs A=%s s=%s"
                           % (k, hx(A), hx(s)))
                else:
                    t.note("ok", "")
            elif bits(q[0]) != bits(p[0] * two(k)) or \
                    bits(q[1]) != bits(p[1] * two(k)):
                t.note("warn", "D4 scale 2^%d not bit-exact: A=%s s=%s"
                       % (k, hx(A), hx(s)))
            else:
                t.note("ok", "")

    # D5  accuracy against the exact integral, both signs of s and sigma.
    acc = [(A, sg * s_of(A, x), n) for A in As for x in xs
           for sg in (1, -1) for n in (0, 1)]
    worst = check_accuracy(t, "D5 grid", acc)

    # D6  the edge of the accepted range |x| = 5/2: doubles on both sides.
    import math
    edge = []
    for A in As:
        s0 = s_of(A, XMAX)
        s = s0
        for _ in range(4):
            s = math.nextafter(s, 0.0)
        for _ in range(9):
            edge += [(A, s, 0), (A, -s, 1)]
            s = math.nextafter(s, math.inf)
    worst_edge = check_accuracy(t, "D6 edge", edge)
    got = run(edge)
    for (A, s, n), r in zip(edge, got):
        if r is not None and abs(Fraction(s) / (R2 * Fraction(A))) > \
                XMAX * (1 + Fraction(1, 2 ** 50)):
            t.note("bug", "D6 edge: accepted outside |x| <= 5/2: A=%s s=%s"
                   % (hx(A), hx(s)))

    # D7  inputs the contract excludes must decline, never answer.
    bad = [(two(-501), 0.0, 0), (two(501), 1.0, 0), (1.0, two(501), 0),
           (1.0, -two(501), 0), (0.0, 0.0, 0), (-1.0, 0.5, 0),
           (float("nan"), 1.0, 0), (1.0, float("nan"), 0),
           (float("inf"), 1.0, 0), (1.0, float("inf"), 0),
           (5e-324, 0.0, 0), (1.0, 4.0, 0), (1.0, -4.0, 1)]
    for (A, s, n), r in zip(bad, run(bad)):
        if r is not None:
            t.note("bug", "D7 out of contract but answered: A=%s s=%s -> %s %s"
                   % (hx(A), hx(s), hx(r[0]), hx(r[1])))
        else:
            t.note("ok", "")

    for line in t.lines:
        print(line)
    print("worst error, grid: %.4g of A/2^41; edge: %.4g of A/2^41"
          % (worst, worst_edge))
    print("SUMMARY ok=%d warn=%d bug=%d" % (t.ok, t.warn, t.bug))
    return 1 if t.bug else 0


if __name__ == "__main__":
    sys.exit(main())
