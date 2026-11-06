#!/usr/bin/env python3
"""Conformance corpus for the proved binary64 de Casteljau evaluator.

  python3 tests/B64DeCasteljauConformance/corpus.py --oracle oracle/oracle_bin --out DIR

writes DIR/B64_DECASTELJAU.in (one query per line: "t c0 .. cn", 16-hex-digit
bit patterns, the oracle's input format), DIR/B64_DECASTELJAU.out (the answers of
the Rocq-extracted oracle, mode B64_DECASTELJAU) and DIR/MANIFEST.tsv
(cases, sha256 of both files, seed).  The C# port is then checked with
  dotnet run --project tests/B64DeCasteljauConformance -c Release -- DIR
and agrees with the oracle iff it prints bug=0.

Contents (all deterministic from --seed):
  * endpoints and the midpoint: t = 0, -0, 1, 0.5, 1 - 2^-53, 2^-1074 (min
    subnormal), 2^-1022 (min normal), on nets of every degree 0..40;
  * random nets: degree 0..40 (dense), 50/100/200/500/1000, controls from
    several magnitude regimes (unit, wide-exponent, near the 2^500 cap,
    random bit patterns within the cap), t uniform / dyadic / log-uniform
    small / bit-random in [0,1] / near 1;
  * subnormal and underflow stress: controls and t in the subnormal range,
    products that underflow, alternating signs with cancellation;
  * the degree-30 regression family p(t) = (1-2t)^30: Bernstein net
    (-1)^j, j = 0..30, on a dense grid around the root t = 1/2 and uniformly;
    also alternating nets of every degree 1..60;
  * 30000 fully random bit-pattern queries (arbitrary t and controls);
  * every decline, and every ORDER of declines: empty, degree 1000 (certified)
    vs 1001 (> max length) vs 1002 (decline), NaN/Inf/-Inf in t and in each
    control position, t just outside [0,1], controls at +-2^500 exact (certified)
    and one ulp above (decline), +-DBL_MAX, with combinations of two failing
    conditions to pin the checking order.
AI assistance disclosure: AI-drafted; human review pending.
"""
import argparse, hashlib, math, os, random, struct, subprocess, sys

def bits(v): return struct.unpack("<Q", struct.pack("<d", v))[0]
def fb(b): return struct.unpack("<d", struct.pack("<Q", b))[0]
def hx(v): return "%016x" % bits(v)

CAP = math.ldexp(1.0, 500)
MIN_SUB = fb(1)
MIN_NORM = math.ldexp(1.0, -1022)
DBL_MAX = sys.float_info.max

def up(x): return math.nextafter(x, math.inf)
def dn(x): return math.nextafter(x, -math.inf)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--oracle", default=os.environ.get("ORACLE", "oracle/oracle_bin"))
    ap.add_argument("--out", required=True)
    ap.add_argument("--seed", type=int, default=20261106)
    ap.add_argument("--scale", type=float, default=1.0, help="multiply the random-case counts")
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    rng = random.Random(a.seed)
    Q = []  # queries: (t, [controls])

    def rbits_within(bound):
        while True:
            v = fb(rng.getrandbits(64))
            if math.isfinite(v) and abs(v) <= bound: return v

    def ctrl(regime):
        if regime == 0: return rng.uniform(-1.0, 1.0)
        if regime == 1:
            m = math.ldexp(1.0 + rng.random(), rng.randint(-60, 60))
            return m if rng.random() < 0.5 else -m
        if regime == 2:  # near the cap, both signs (certified up to 2^500)
            m = math.ldexp(1.0 + rng.random(), rng.randint(490, 499))
            return m if rng.random() < 0.5 else -m
        if regime == 3: return rbits_within(CAP)
        if regime == 4:  # subnormal / tiny
            return fb(rng.getrandbits(52)) * (1 if rng.random() < 0.5 else -1)
        return rng.choice([0.0, -0.0, 1.0, -1.0, MIN_SUB, -MIN_SUB, MIN_NORM, -MIN_NORM])

    def tval(kind):
        if kind == 0: return rng.random()
        if kind == 1: return rng.randint(0, 1 << 20) / float(1 << 20)       # dyadic
        if kind == 2: return math.ldexp(1.0 + rng.random(), -rng.randint(1, 1074 - 52))  # log-uniform small
        if kind == 3: return 1.0 - math.ldexp(rng.random(), -rng.randint(1, 53))         # near 1
        while True:                                                          # bit-random in [0,1]
            v = abs(fb(rng.getrandbits(64)))
            if 0.0 <= v <= 1.0: return v

    n_rand = int(a.scale * 20)
    # ---- endpoints / midpoint on nets of every degree ------------------------
    for t in (0.0, -0.0, 1.0, 0.5, dn(1.0), up(0.0), MIN_NORM, dn(MIN_NORM), 0.25, 0.75):
        for deg in range(0, 41):
            for regime in (0, 1, 3, 5):
                for _ in range(3):
                    Q.append((t, [ctrl(regime) for _ in range(deg + 1)]))
    # ---- random nets ---------------------------------------------------------
    degs = list(range(0, 41)) * 120 + [50, 100, 200, 500, 1000] * 40
    for deg in degs:
        for _ in range(n_rand):
            regime = rng.choice([0, 0, 1, 1, 2, 3, 4, 5])
            Q.append((tval(rng.randint(0, 4)), [ctrl(regime) for _ in range(deg + 1)]))
    # ---- subnormal / underflow stress ----------------------------------------
    for _ in range(20000):
        deg = rng.randint(1, 12)
        t = rng.choice([MIN_SUB, 2 * MIN_SUB, fb(rng.getrandbits(52)), math.ldexp(1.0, -rng.randint(500, 1074))])
        Q.append((t, [fb(rng.getrandbits(52)) * rng.choice([1, -1]) for _ in range(deg + 1)]))
        Q.append((1.0 - t if rng.random() < 0.5 else t,
                  [rng.choice([MIN_SUB, -MIN_SUB, MIN_NORM, -MIN_NORM, 1.0, -1.0, fb(rng.getrandbits(52))]) for _ in range(deg + 1)]))
    # ---- alternating nets (cancellation), every degree 1..60 -----------------
    for deg in range(1, 61):
        net = [(-1.0) ** j for j in range(deg + 1)]
        for t in [0.0, 1.0, 0.5, dn(0.5), up(0.5)] + [rng.random() for _ in range(150)] \
                 + [0.5 + k * math.ldexp(1.0, -20) for k in range(-40, 41)]:
            if 0.0 <= t <= 1.0: Q.append((t, net))
    # ---- the degree-30 regression: p(t) = (1 - 2t)^30, Bernstein net (-1)^j ---
    net30 = [(-1.0) ** j for j in range(31)]
    reg = [0.5, dn(0.5), up(0.5), 0.0, 1.0] + [0.5 + k * math.ldexp(1.0, -30) for k in range(-300, 301)] \
          + [0.5 + k * math.ldexp(1.0, -12) for k in range(-1000, 1001)] \
          + [rng.uniform(0.2, 0.8) for _ in range(20000)] + [rng.random() for _ in range(5000)] \
          + [0.5 + rng.uniform(-1e-3, 1e-3) for _ in range(10000)]
    for t in reg: Q.append((t, net30))
    # ---- declines and their order ---------------------------------------------
    nanv, inf = math.nan, math.inf
    sNaN = fb(0x7FF0000000000001)
    base = [0.5, -0.5, 0.25]
    Q.append((0.5, []))
    for t in (nanv, inf, -inf, 2.0, -1.0): Q.append((t, []))          # EMPTY comes first
    for L in (999, 1000, 1001, 1002, 1003, 2000):                     # degree boundary (L controls)
        for t in (0.5, nanv, 2.0):
            Q.append((t, [rng.uniform(-1, 1) for _ in range(L)]))
            Q.append((t, [CAP] * L if L <= 1001 else [CAP] * L))
    for t in (nanv, sNaN, inf, -inf):                                  # nonfinite t
        Q += [(t, base), (t, [CAP * 4]), (t, [1.0])]
    for pos in range(4):                                               # nonfinite control at each position
        for bad in (nanv, sNaN, inf, -inf):
            c = [0.5, -0.5, 0.25, 1.0]; c[pos] = bad
            for t in (0.5, 2.0, nanv):                                 # NONFINITE beats PARAM
                Q.append((t, c))
            c2 = [CAP * 4, -CAP * 4, 3.0, 2.0]; c2[pos] = bad          # NONFINITE beats GUARD
            Q.append((0.5, c2))
    for t in (up(1.0), 1.0000001, 2.0, -MIN_SUB, dn(0.0), -1.0, 1e300, -1e300, DBL_MAX, -DBL_MAX):
        Q += [(t, base), (t, [CAP * 4, 1.0]), (t, [1.0])]              # PARAM beats GUARD
    for t in (0.0, 1.0, 0.5):
        for edge in (CAP, -CAP, dn(CAP), -dn(CAP)):                    # exactly at the cap: certified
            Q += [(t, [edge, 1.0]), (t, [1.0, edge, -1.0]), (t, [edge])]
        for bad in (up(CAP), -up(CAP), CAP * 2, DBL_MAX, -DBL_MAX, math.ldexp(1.0, 501)):
            for pos in range(3):
                c = [1.0, -1.0, 0.5]; c[pos] = bad
                Q.append((t, c))
            Q.append((t, [bad]))                                       # degree 0 still guarded
    # ---- random bit-pattern queries: t and controls arbitrary (mostly declines) ---
    for _ in range(int(a.scale * 30000)):
        deg = rng.randint(0, 6)
        t = fb(rng.getrandbits(64)) if rng.random() < 0.6 else tval(rng.randint(0, 4))
        Q.append((t, [fb(rng.getrandbits(64)) if rng.random() < 0.5 else ctrl(rng.randint(0, 5))
                      for _ in range(deg + 1)]))
    # ---- run the oracle -------------------------------------------------------
    lines = [hx(t) + "".join(" " + hx(c) for c in cs) for t, cs in Q]
    r = subprocess.run([a.oracle], input="B64_DECASTELJAU\n" + "\n".join(lines) + "\n",
                       capture_output=True, text=True, check=True)
    out = [l for l in r.stdout.split("\n") if l.strip()]
    assert len(out) == len(lines), (len(out), len(lines))
    with open(os.path.join(a.out, "B64_DECASTELJAU.in"), "w") as f: f.write("\n".join(lines) + "\n")
    with open(os.path.join(a.out, "B64_DECASTELJAU.out"), "w") as f: f.write("\n".join(out) + "\n")
    h = lambda p: hashlib.sha256(open(p, "rb").read()).hexdigest()
    with open(os.path.join(a.out, "MANIFEST.tsv"), "w") as f:
        f.write("mode\tcases\tsha256_in\tsha256_out\tseed\n")
        f.write("B64_DECASTELJAU\t%d\t%s\t%s\t%d\n" % (
            len(lines), h(os.path.join(a.out, "B64_DECASTELJAU.in")),
            h(os.path.join(a.out, "B64_DECASTELJAU.out")), a.seed))
    kinds = {}
    for o in out: kinds[o.split(" ")[0]] = kinds.get(o.split(" ")[0], 0) + 1
    print("cases", len(lines), kinds)

if __name__ == "__main__":
    main()
