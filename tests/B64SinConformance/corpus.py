#!/usr/bin/env python3
"""S10 conformance corpus: inputs generated from the contracts, answered once
by the Rocq-extracted oracle, then replayed against every port (C#, Java).

  python3 tests/B64SinConformance/corpus.py --oracle oracle/oracle_bin --out DIR

writes, per mode, DIR/<MODE>.in (one query per line, the oracle's input
format) and DIR/<MODE>.out (the oracle's answers), plus DIR/MANIFEST.tsv
(mode, cases, sha256 of .in and .out).  Ports are then checked with
  dotnet run --project tests/B64SinConformance -c Release -- DIR
  java -cp BUILD nts.proofs.numerics.Conformance DIR
and agree with the oracle iff they print bug=0 for every mode; since both
compare against the same answers, oracle == C# == Java bit for bit.

The boundary points are derived from the contracts, i.e. from the Coq
literals themselves (gen_constants.literals()):
  * every intake cap +-k ulp (sin_accept 10, ap_cap 2^998, fresnel 5/2,
    cm_Alo 2^-500, cm_cap 2^500);
  * every argument-reduction transition +-k ulp (sn_T1, sn_T3, sn_T5, the
    multiples k C1 of the reduction constant, k pi/2);
  * zero and signed zero, the subnormal / normal transitions;
  * margin boundaries +-k ulp: the exact flip of mf_seg_g_outcome between
    DECLINE and POSITIVE, found by bisection on bit patterns with the oracle;
  * the Fresnel tail transition: the cap 5/2 itself and, for clothoids, the
    exact s where the COMPUTED argument fl(s / fl(fl(sqrt 2) A)) leaves the
    intake (bisection with the oracle);
  * seeded random values from every accepted region and random bit patterns.
AI assistance disclosure: AI-drafted; human review pending.
"""
import argparse, hashlib, math, os, random, struct, subprocess, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_constants  # noqa: E402

def bits(v): return struct.unpack("<Q", struct.pack("<d", v))[0]
def fb(b): return struct.unpack("<d", struct.pack("<Q", b))[0]
def hx(v): return "%016x" % bits(v)

def around(x, k):
    """x and its k neighbours on each side, by ulp."""
    out = [x]; up = dn = x
    for _ in range(k):
        up = math.nextafter(up, math.inf); dn = math.nextafter(dn, -math.inf)
        out += [up, dn]
    return out

def pm(xs): return [s * x for x in xs for s in (1.0, -1.0)]

class Oracle:
    def __init__(self, path): self.path = path
    def ask(self, mode, lines):
        r = subprocess.run([self.path], input=mode + "\n" + "\n".join(lines) + "\n",
                           capture_output=True, text=True, check=True)
        out = [l for l in r.stdout.split("\n") if l.strip()]
        assert len(out) == len(lines), (mode, len(out), len(lines))
        return out

def flip(oracle, mode, fmt, lo, hi, is_hi):
    """Smallest positive double in (lo, hi] whose answer satisfies is_hi,
    assuming the answer is monotone between lo (not is_hi) and hi (is_hi)."""
    a, b = bits(lo), bits(hi)
    assert not is_hi(oracle.ask(mode, [fmt(fb(a))])[0])
    assert is_hi(oracle.ask(mode, [fmt(fb(b))])[0])
    while b - a > 1:
        m = (a + b) // 2
        if is_hi(oracle.ask(mode, [fmt(fb(m))])[0]): b = m
        else: a = m
    return fb(b)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--oracle", default=os.environ.get("ORACLE", "oracle/oracle_bin"))
    ap.add_argument("--out", required=True)
    ap.add_argument("--seed", type=int, default=20261103)
    a = ap.parse_args()
    os.makedirs(a.out, exist_ok=True)
    O = Oracle(a.oracle)
    K = {n: v for n, _, v in gen_constants.literals()}
    rng = random.Random(a.seed)
    specials = [math.nan, math.inf, -math.inf, fb(0x7FF0000000000001), fb(0xFFF8000000000000)]
    sub = [fb(1), fb(2), fb(0x000FFFFFFFFFFFFF), fb(0x0010000000000000), fb(0x0010000000000001), 1e-300]

    def rand_bits(bound, n):
        out = []
        while len(out) < n:
            v = fb(rng.getrandbits(64))
            if math.isfinite(v) and abs(v) <= bound: out.append(v)
        return out

    # ---- B64_SIN / B64_COS --------------------------------------------------
    trig = [0.0, -0.0] + pm(sub) + specials
    for c in ("sn_T1", "sn_T3", "sn_T5", "sn_ten"):
        trig += pm(around(K[c], 8))
    for k in (1.0, 2.0, 3.0):  # k C1 is exact (C1 has 50 significant bits)
        trig += pm(around(k * K["sn_C1"], 8))
    for k in range(1, 7): trig += pm(around(k * math.pi / 2, 8))
    trig += [1e300, -1e300]
    trig += [rng.uniform(-10.0, 10.0) for _ in range(150000)] + rand_bits(10.0, 100000)
    trig_lines = [hx(x) for x in trig]
    modes = {"B64_SIN": trig_lines, "B64_COS": trig_lines}

    # ---- B64_ARC_PT ---------------------------------------------------------
    acc_t = [x for x in trig if math.isfinite(x) and abs(x) <= 10.0]
    def mag():
        m = math.ldexp(1.0 + rng.random(), rng.randint(-60, 60))
        return m if rng.random() < 0.5 else -m
    arc = []
    for c in pm(around(K["ap_cap"], 1)) + [0.0, -0.0, fb(1)] + specials:
        t = rng.choice(acc_t)
        arc += [(c, 1.0, 1.0, t), (1.0, c, 1.0, t), (1.0, 1.0, c, t), (c, c, c, t)]
    arc += [(mag(), mag(), mag(), rng.choice(acc_t)) for _ in range(150000)]
    modes["B64_ARC_PT"] = ["%s %s %s %s" % tuple(hx(v) for v in q) for q in arc]

    # ---- B64_FRESNEL --------------------------------------------------------
    fr = [0.0, -0.0] + pm(sub) + specials + pm(around(K["fr_X"], 16)) + [3.0, -1e300]
    fr += [rng.uniform(-2.5, 2.5) for _ in range(150000)] + rand_bits(2.5, 50000)
    modes["B64_FRESNEL"] = [hx(x) for x in fr]

    # ---- B64_CLOTHOID -------------------------------------------------------
    r2 = math.sqrt(2.0)
    cl = []
    def accepted(ans): return not ans.startswith("DECLINE")
    for A in (1.0, 100.0, 126.49110640673517, math.ldexp(1.0, -30), math.ldexp(1.0, 30), 0.3):
        # the computed-argument tail transition: largest accepted s for this A
        sfmt = lambda s, A=A: "%s %s 0" % (hx(A), hx(s))
        s_first_rej = flip(O, "B64_CLOTHOID", sfmt, 2.0 * r2 * A, 3.0 * r2 * A,
                           lambda ans: not accepted(ans))
        for s in pm(around(s_first_rej, 8)):
            cl += [(A, s, 0), (A, s, 1)]
    for A in around(K["cm_Alo"], 1) + around(K["cm_cap"], 1) + [0.0, -1.0, math.nan, math.inf]:
        for s in [0.0, -0.0, 1.0, -1.0] + pm(around(K["cm_cap"], 1)) + [fb(1), math.nan, -math.inf]:
            cl += [(A, s, 0), (A, s, 1)]
    for _ in range(120000):
        A = math.ldexp(1.0 + rng.random(), rng.randint(-40, 40))
        x = rng.uniform(-2.6, 2.6)
        cl.append((A, x * r2 * A, rng.randint(0, 1)))
    modes["B64_CLOTHOID"] = ["%s %s %d" % (hx(A), hx(s), g) for A, s, g in cl]

    # ---- B64_SEG_G ----------------------------------------------------------
    gfmt = hx
    t_star = flip(O, "B64_SEG_G", gfmt, 1e-5, 1e-4, lambda ans: ans.startswith("POSITIVE"))
    sg = pm(around(t_star, 64)) + [0.0, -0.0] + pm(sub) + specials
    sg += pm(around(K["sn_ten"], 4))
    sg += [rng.uniform(-10.0, 10.0) for _ in range(100000)]
    sg += [rng.uniform(1e-5, 1e-4) * rng.choice((1.0, -1.0)) for _ in range(50000)]
    modes["B64_SEG_G"] = [hx(x) for x in sg]

    # ---- answer, write, manifest -------------------------------------------
    man = ["mode\tcases\tsha256_in\tsha256_out\tboundary_note"]
    notes = {"B64_SEG_G": "margin flip t* = %r (%s)" % (t_star, hx(t_star))}
    for mode, lines in modes.items():
        ans = O.ask(mode, lines)
        tin = "\n".join(lines) + "\n"; tout = "\n".join(ans) + "\n"
        open(os.path.join(a.out, mode + ".in"), "w").write(tin)
        open(os.path.join(a.out, mode + ".out"), "w").write(tout)
        man.append("%s\t%d\t%s\t%s\t%s" % (mode, len(lines),
                   hashlib.sha256(tin.encode()).hexdigest(),
                   hashlib.sha256(tout.encode()).hexdigest(), notes.get(mode, "")))
    open(os.path.join(a.out, "MANIFEST.tsv"), "w").write("\n".join(man) + "\n")
    print("\n".join(man))

if __name__ == "__main__":
    main()
