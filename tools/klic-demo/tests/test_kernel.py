"""The extracted kernel against its specification, on concrete values.

These are TESTS of the extracted binary and the text shim (main.ml); the
kernel's correctness itself is the Qed reflection theorems in
theories-flocq/HotPixel_Q_exec.v.  The independent reference here is plain
Python Fraction arithmetic, written from the definitions (not from the OCaml).
"""
from __future__ import annotations

import math
import random
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import verified_hotpixel as vk  # noqa: E402


def ref_round_ne(q: Fraction) -> int:
    f = math.floor(q)
    r = q - f
    if r < Fraction(1, 2):
        return f
    if r > Fraction(1, 2):
        return f + 1
    return f if f % 2 == 0 else f + 1


def ref_snap(x: Fraction, s: Fraction) -> Fraction:
    return Fraction(ref_round_ne(x * s)) / s


def ref_touch_closed(p0, p1, c, s) -> bool:
    """Closed segment vs closed square of half-width 1/(2s), by exact
    Liang-Barsky written independently."""
    r = 1 / (2 * s)
    lo, hi = Fraction(0), Fraction(1)
    for k in (0, 1):
        a, b = p0[k], p1[k]
        lo_k, hi_k = c[k] - r, c[k] + r
        d = b - a
        if d == 0:
            if not (lo_k <= a <= hi_k):
                return False
            continue
        t1, t2 = (lo_k - a) / d, (hi_k - a) / d
        lo, hi = max(lo, min(t1, t2)), min(hi, max(t1, t2))
    return lo <= hi


def test_round_half_even_by_snap_unit():
    xs = [Fraction(5, 2), Fraction(7, 2), Fraction(-5, 2), Fraction(-7, 2), Fraction(1, 3),
          Fraction(-1, 3), Fraction(0), Fraction(155523520699, 1000), Fraction(155523520500, 1000)]
    got = vk.snap_many(xs, 1)
    for x, (sn, d) in zip(xs, got):
        assert sn == ref_round_ne(x)
        assert d == abs(sn - x)


def test_snap_at_scale_1000_on_metres():
    got = vk.snap_many([Fraction("155523.5207"), Fraction("155523.5205"), Fraction("155523.5215")], 1000)
    assert [g[0] for g in got] == [Fraction("155523.521"), Fraction("155523.520"), Fraction("155523.522")]


def test_snap_random_against_reference():
    rnd = random.Random(1)
    xs, ss = [], []
    for _ in range(400):
        xs.append(Fraction(rnd.randint(-10**12, 10**12), rnd.randint(1, 10**6)))
        ss.append(rnd.choice([Fraction(1), Fraction(1000), Fraction(1, 10), Fraction(3, 7)]))
    rep = vk.run_batch([vk.q_snap(x, s) for x, s in zip(xs, ss)])
    for x, s, line in zip(xs, ss, rep):
        sn, d = (Fraction(t) for t in line.split())
        assert sn == ref_snap(x, s)
        assert d == abs(sn - x)
        assert d <= 1 / (2 * s)  # the theorem's bound, observed


def test_passes_and_touches_examples():
    P = lambda x, y: (Fraction(x), Fraction(y))  # noqa: E731
    # through the centre, along the pixel edge, just outside
    assert vk.passes_many([(P(0, 0), P(10, 10), P(5, 5))], 1) == [True]
    assert vk.passes_many([(P(0, 0), P(10, 0), P(5, 1))], 1) == [False]
    assert vk.passes_many([(P(0, 0), P(10, 0), P(5, "1/2"))], 1) == [True]   # closed pixel
    assert vk.passes_many([(P(0, 0), P(10, 0), P(5, "501/1000"))], 1) == [False]


def test_touch_random_against_reference():
    rnd = random.Random(2)
    items = []
    for _ in range(600):
        c = (Fraction(rnd.randint(-5, 5)), Fraction(rnd.randint(-5, 5)))
        p0 = (Fraction(rnd.randint(-60, 60), 8), Fraction(rnd.randint(-60, 60), 8))
        if rnd.random() < 0.2:
            p1 = (p0[0], Fraction(rnd.randint(-60, 60), 8))  # vertical, degenerate x axis
        else:
            p1 = (Fraction(rnd.randint(-60, 60), 8), Fraction(rnd.randint(-60, 60), 8))
        items.append((p0, p1, c))
    rep = vk.run_batch([vk.q_touch(p0, p1, c, 1) for p0, p1, c in items])
    assert [r == "1" for r in rep] == [ref_touch_closed(p0, p1, c, 1) for p0, p1, c in items]
    rep2 = vk.run_batch([vk.q_pass(p0, p1, c, 1) for p0, p1, c in items])
    ref2 = [ref_touch_closed(p0, p1, c, 1) and
            ref_touch_closed((ref_snap(p0[0], 1), ref_snap(p0[1], 1)),
                             (ref_snap(p1[0], 1), ref_snap(p1[1], 1)), c, 1)
            for p0, p1, c in items]
    assert [r == "1" for r in rep2] == ref2


def test_intersection_examples():
    P = lambda x, y: (Fraction(x), Fraction(y))  # noqa: E731
    got = vk.intersections_many([
        (P(0, 0), P(2, 2), P(0, 2), P(2, 0)),     # X
        (P(0, 0), P(1, 0), P(0, 1), P(1, 1)),     # parallel
        (P(0, 0), P(1, 1), P(3, 0), P(3, 5)),     # lines meet outside segment 1
        (P(0, 0), P(3, 1), P(1, -1), P(1, 7)),    # rational node
    ])
    assert got == [P(1, 1), None, None, (Fraction(1), Fraction(1, 3))]


def test_big_rd_magnitudes_exact():
    """No range limit: values far beyond the binary64 tight grid (2^22)."""
    x = Fraction(629_000_000_123_456_789, 1000)  # 6.29e14 mm, nonsense but exact
    (sn, d), = vk.snap_many([x], 1)
    assert sn == ref_round_ne(x) and d == abs(sn - x)
