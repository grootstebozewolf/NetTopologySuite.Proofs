#!/usr/bin/env python3
# tests/B64CurveEvalMeasure/cmp.py
# Measured binary64 error of Horner (power basis) vs de Casteljau (Bernstein)
# on p_n(t) = (1-2t)^n, against an exact Fraction reference.  Companion to
# docs/b64-curve-eval-error-bounds-2026-11.md; the proved bounds are in
# theories-flocq/B64_{HornerGamma,DeCasteljau,BezierStability}.v.
# Run:  python3 -I tests/B64CurveEvalMeasure/cmp.py
# Python floats are IEEE binary64 RNE, and the loops do exactly one multiply
# and one add per Horner step / per de Casteljau weight pair, as in the
# Rocq evaluators.

import math, random
from fractions import Fraction
u = 2.0**-53
def horner(a, t):
    r = a[-1]
    for c in reversed(a[:-1]): r = r*t + c      # one mult + one add each, matches b64_horner
    return r
def dcast(b, t):
    s = 1.0 - t; row = list(b)
    for _ in range(len(b)-1):
        row = [s*row[i] + t*row[i+1] for i in range(len(row)-1)]
    return row[0]
random.seed(1)
print("n  maxerr_Horner  maxerr_dC   ratio   |  proved: Horner main 2nu*3^n  dC main 6nu")
for n in (5,10,15,20,25,30):
    a = [float(math.comb(n,i)*(-2)**i) for i in range(n+1)]   # exact: < 2^53 for n<=30
    assert all(Fraction(a[i]) == math.comb(n,i)*(-2)**i for i in range(n+1))
    b = [(-1.0)**j for j in range(n+1)]
    eh = ed = 0.0
    for _ in range(20000):
        t = random.uniform(0.2,0.8) if random.random()<0.5 else 0.5 + random.uniform(-1e-3,1e-3)
        t = float(t)
        ex = (1 - 2*Fraction(t))**n
        eh = max(eh, abs(float(Fraction(horner(a,t)) - ex)))
        ed = max(ed, abs(float(Fraction(dcast(b,t)) - ex)))
    print(f"{n:2d} {eh:12.3e} {ed:12.3e} {eh/ed if ed else float('inf'):9.1f} | {2*n*u*3**n:12.3e} {6*n*u:10.3e}")
