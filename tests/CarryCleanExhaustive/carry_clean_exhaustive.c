/* ===========================================================================
   carry_clean_exhaustive.c -- exhaustive small-precision evidence for
   theories-flocq/B64_CarryClean.v.  Reconnaissance, not proof: one failure
   would refute an open statement, no number of passes proves one.

   Models, in p-bit binary arithmetic with round-to-nearest-even, exactly the
   corpus algorithms:
     - fast_expansion_sum (B64_FastExpansionSum_Shewchuk.v): insertion sort
       by |x| (x goes before y iff |x| <= |y|), TwoSum chain
       (Q, h) := TwoSum(g_i, Q), output Q :: rev hs;
     - cc_push / cc_run (B64_CarryClean.v): MODE 0 = cancel_clean,
       MODE 1 = carry_clean (cancel is not re-tested after a cancel; a carry
       is re-tested against the new top).
   and enumerates EVERY input pair in a window.  Values are scaled integers,
   so the model is exact; each TwoSum is checked to be error-free.

   Checks, per MODE:
     0, 1  the cleanup's output is nonoverlapping in Shewchuk's sense
           (|next| < 2^lsb(prev) or the symmetric case) -> "fails";
     1     also the block PATTERN of the open bridge, on the zero-filtered
           raw output, decomposed greedily into singles, twins (x, x) and
           anti pairs (x, -x): "pattern" = keys not strictly decreasing
           (part (a), `fes_priest_carry_pattern`), "reduction" = reduced list
           not nonoverlapping (part (b), `fes_priest_reduction_nonoverlap`);
           and "cascades" = sweeps where a carry carries again or a cancel
           exposes an equal/opposite pair (what the strict pattern excludes);
     2     no cleanup: the raw output is within one bit of slack
           (`overlap_within 1`, Priest's one-digit bound) -> "fails".

   Inputs: CLASS 0 = Priest expansions (normalised p-bit significands,
   exponent gap >= p); CLASS 1 = Shewchuk-nonoverlapping expansions
   (|next| < 2^lsb(prev)).  Lengths 1..L.  Without FLOOR: unbounded
   exponents, e's top exponent fixed at 0 (scale invariance), f ranges over
   exponents [KLO, KHI].  With FLOOR = 1: KLO is emin (an underflow floor,
   gradual underflow), subnormal components m * 2^emin with m < 2^(p-1) are
   included (their Priest exponent lies below emin), and e's top exponent
   ranges too (no scale invariance under a floor).

   Build and run:
     cc -O2 -o carry_clean_exhaustive carry_clean_exhaustive.c
     ./carry_clean_exhaustive P KLO KHI L MODE CLASS [FLOOR [TOTAL]]
   TOTAL (at least 2; default 99, i.e. no limit) keeps only pairs whose
   lengths sum to at most TOTAL; SUMMARY echoes it.

   Recorded results (2026-10-29 .. 2026-10-31), CLASS 0 unless stated:
     p KLO KHI L MODE FLOOR        pairs  fails  notes
     3  -9   4 3   0    0      366766976    680  cancel_clean refuted
     3  -9   4 3   1    0      366766976      0  pattern 0, reduction 0, cascades 0
     2  -8   3 4   1    0      148581504      0
     2 -10   0 5   1    0     1196510640      0  pattern 0, reduction 0, cascades 0
     5 -10   5 2   1    0      420560896      0
     4  -9   3 3   1    0     2146417920      0  pattern 0, reduction 0, cascades 0
     3 -10   2 4   1    0     4670763328      0  pattern 0, reduction 0, cascades 0
     3   0   8 3   1    1      129367876      0  underflow floor; pattern 0, reduction 0, cascades 0
     2   0   9 4   1    1      346332100      0  underflow floor; pattern 0, reduction 0, cascades 0
     4   0   7 3   1    1      147428164      0  underflow floor; pattern 0, reduction 0, cascades 0
     3  -9   4 3   2    0      366766976      0  one-digit bound, raw output
     4  -9   3 3   2    0     2146417920      0  one-digit bound, raw output
     3 -10   2 4   2    0     4670763328      0  one-digit bound, raw output
     3  -7   2 3   1    0      130842880    758  CLASS 1: nonoverlapping inputs
   Pattern/reduction/cascade counts are noted on the rows whose run printed
   them; the other MODE 1 rows predate those counters (rerun to see them).

   By total length (MODE 1, CLASS 0, TOTAL given; 2026-10-31 .. 11-01).  The RAW
   line counts pairs whose zero-filtered output BEFORE carry_clean has an
   overlapping neighbour pair (ovl) or is not strictly decreasing (desc).
   Every row has pattern 0, reduction 0, cascades 0.
     p KLO KHI L FLOOR TOTAL      pairs  fails  twins  antis  ovl  desc
     2 -10   2 4    0     4      299408      0      0      0    0     0
     3 -16   2 4    0     4    15005888      0      0      0    0     0
     4 -12   2 4    0     4    60006144      0      0      0    0     0
     5  -7   2 4    0     4    48670720      0      0      0    0     0
     2   0   9 4    1     4      852420      0      0      0    0     0  underflow floor
     3   0   8 4    1     4     4644676      0      0      0    0     0  underflow floor
     4   0   7 4    1     4    17929028      0      0      0    0     0  underflow floor
     2  -8   2 5    0     5     1630000      0      8      8   16    16
     3  -8   2 5    0     5    15474368      0     16     16   32    32
     2  -8   2 6    0     6    10772272      0    372    372  744   744
     3  -7   2 6    0     6    23920256      0    200    200  400   400
     2   0   8 6    1     6    19297828      0   1264   1264 2528  2528  underflow floor
     2 -14   2 6    0     6   296188752      0    948    948 1896  1896
     2 -14   2 7    0     7  3345873744      0  44140  44140 88264 88264
   Through total 4 the raw output is already strictly decreasing and
   nonoverlapping (all singles; B64_CarryCleanRung3.v proves it).  Twins
   and anti pairs first occur at total 5; at totals 5 and 6 ovl = desc =
   twins + antis, i.e. every raw defect is one equal-magnitude pair, which
   carry_clean then merges or cancels.  At total 7 (PAIRS line of the
   2 -14 2 7 row): 88,248 outputs carry one pair and 16 carry two -- two ties
   in one TwoSum chain -- none carry three, and carry_clean still has no
   failure, pattern or reduction violation.  Ties at steps 5, 6 and 7 of
   that run (all chain lengths <= 7 together): 11976, 11676 and 20488 each
   as anti and as twin, none as singles.

   Ties of the TwoSum chain (TIE lines; 2026-11-01), by chain length n and
   step k, as anti/twin counts.  No tie ever resolves as singles.  PAIRS:
   at totals <= 6 every defective output carries exactly one pair.
     p KLO KHI FLOOR TOTAL   n=5 k=5    n=6 k=5    n=6 k=6
     3  -8   2    0     5     16/16
     3  -7   2    0     6     16/16         -      184/184
     2  -8   2    0     6      8/8     128/128    236/236
     2 -14   2    0     6      8/8     320/320    620/620
     2   0   8    1     6     44/44    512/512    708/708

   Prints FAIL lines (up to five); in MODE 1 a SHAPE line, a RAW line, the
   number of outputs by count of twin/anti pairs (PAIRS), and the ties of the
   TwoSum chain by its length n, step and outcome (TIE: at step k,
   |h_(k-1)| = ulp(g_k);
   anti if h_k = -h_(k-1), twin if h_k = 0 and Q_k = h_(k-1), else singles);
   and a SUMMARY.  "cascades" in the SHAPE line counts carry cascades inside
   carry_clean (a carry or cancel that triggers another), not the TwoSum
   chain.
   Exit status 1 on any failure or (MODE 1) any pattern/reduction violation.

   Assisted-by: Claude
   =========================================================================== */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef __int128 I;

static int p, KLO, KHI, L, MODE, CLASS, FLOOR;

static I iabs(I x) { return x < 0 ? -x : x; }

static I rnd(I x) {
  if (!x) return 0;
  int s = x > 0 ? 1 : -1;
  I a = iabs(x);
  int n = 0;
  for (I t = a; t; t >>= 1) n++;
  int sh = n - p;
  if (FLOOR && sh < 0) sh = 0;     /* one unit = 2^emin: below that, exact */
  if (sh <= 0) return x;
  I q = a >> sh, r = a - (q << sh), half = ((I)1) << (sh - 1);
  if (r > half || (r == half && (q & 1))) q++;
  return s * (q << sh);
}

static void two_sum(I x, I y, I *a, I *b) {
  I s = rnd(x + y), xp = rnd(s - x);
  I dx = rnd(x - rnd(s - xp)), dy = rnd(y - xp);
  *a = s;
  *b = rnd(dx + dy);
  if (*a + *b != x + y) { fprintf(stderr, "TwoSum inexact\n"); exit(1); }
}

static int lsb(I x) { int k = 0; for (x = iabs(x); !(x & 1); x >>= 1) k++; return k; }

/* Shewchuk nonoverlapping with k bits of slack (k = 0: nonoverlapping). */
static int overlap_within(int k, I a, I b) {
  if (!a || !b) return 1;
  return iabs(b) < (((I)1) << (lsb(a) + k)) || iabs(a) < (((I)1) << (lsb(b) + k));
}

/* The last sum's TwoSum chain, 1-based: g[k] sorted, Q[k] and h[k] from
   step k (k >= 2), Q[1] = g[1]. */
static I cg[16], cQ[16], ch[16];
static int cn;

static int fes(const I *e, int ne, const I *f, int nf, I *out) {
  I all[16], s[16] = {0}, hs[16];
  int n = 0, ns = 0, nh = 0;
  for (int i = 0; i < ne; i++) all[n++] = e[i];
  for (int i = 0; i < nf; i++) all[n++] = f[i];
  for (int i = n - 1; i >= 0; i--) {          /* insert all[i] into s */
    I x = all[i];
    int j = 0;
    while (j < ns && !(iabs(x) <= iabs(s[j]))) j++;
    memmove(&s[j + 1], &s[j], (ns - j) * sizeof(I));
    s[j] = x;
    ns++;
  }
  I q = s[0];
  cn = ns; cg[1] = s[0]; cQ[1] = q;
  for (int i = 1; i < ns; i++) {
    I a, b; two_sum(s[i], q, &a, &b); q = a; hs[nh++] = b;
    cg[i + 1] = s[i]; cQ[i + 1] = a; ch[i + 1] = b;
  }
  out[0] = q;
  for (int i = 0; i < nh; i++) out[1 + i] = hs[nh - 1 - i];
  return 1 + nh;
}

static long long cascades;

static int clean(const I *o, int n, I *st) {
  int k = 0, cascaded = 0, after_cancel = 0;
  for (int i = 0; i < n; i++) {
    I x = o[i];
    if (!x) continue;
    if (after_cancel && k && (st[k - 1] == x || st[k - 1] == -x)) cascaded = 1;
    after_cancel = 0;
    int carries = 0;
    for (;;) {
      if (k && st[k - 1] == -x) { k--; x = 0; after_cancel = 1; break; }
      if (MODE == 1 && k && st[k - 1] == x) { k--; x = 2 * x; carries++; continue; }
      break;
    }
    if (carries >= 2 || (carries >= 1 && x == 0)) cascaded = 1;
    if (x) st[k++] = x;
  }
  if (cascaded) cascades++;
  return k;
}

/* Greedy block decomposition of the zero-filtered raw output. */
static long long pattern_bad, reduction_bad, twins, antis;
static long long pairs_hist[8];   /* outputs by number of twin/anti pairs */
static long long tie_at[16][16][3];   /* chain length n, tie at step k: anti, twin, singles */
static long long raw_overlap, raw_notdesc;   /* the zero-filtered raw output */

static void shape(const I *o, int n) {
  I z[16], key[16], red[16];
  int nz = 0, nb = 0, nr = 0;
  for (int i = 0; i < n; i++) if (o[i]) z[nz++] = o[i];
  for (int i = 0; i + 1 < nz; i++) if (!overlap_within(0, z[i], z[i + 1])) { raw_overlap++; break; }
  for (int i = 0; i + 1 < nz; i++) if (!(iabs(z[i]) > iabs(z[i + 1]))) { raw_notdesc++; break; }
  int npairs = 0;
  for (int j = 0; j < nz;) {
    if (j + 1 < nz && z[j + 1] == z[j])       { key[nb++] = 2 * iabs(z[j]); red[nr++] = 2 * z[j]; j += 2; twins++; npairs++; }
    else if (j + 1 < nz && z[j + 1] == -z[j]) { key[nb++] = iabs(z[j]); j += 2; antis++; npairs++; }
    else                                      { key[nb++] = iabs(z[j]); red[nr++] = z[j]; j += 1; }
  }
  pairs_hist[npairs < 7 ? npairs : 7]++;
  /* ties in the TwoSum chain: at step k, |h[k-1]| = ulp(g[k]); the outcome
     is read off step k's own TwoSum (Q[k], h[k]) */
  for (int k = 3; k <= cn; k++) {
    I g = cg[k];
    if (!g) continue;
    int nbits = 0;
    for (I t = iabs(g); t; t >>= 1) nbits++;
    int sh = nbits - p;
    if (sh < 0) sh = 0;
    if (iabs(ch[k - 1]) != (((I)1) << sh)) continue;
    if (ch[k] == -ch[k - 1]) tie_at[cn][k][0]++;
    else if (ch[k] == 0 && cQ[k] == ch[k - 1]) tie_at[cn][k][1]++;
    else tie_at[cn][k][2]++;
  }
  for (int b = 0; b + 1 < nb; b++) if (!(key[b] > key[b + 1])) { pattern_bad++; return; }
  for (int r = 0; r + 1 < nr; r++) if (!overlap_within(0, red[r], red[r + 1])) { reduction_bad++; return; }
}

static I comps[8192];
static int ck[8192], nc;
static long long tot, bad;
static I E[8], F[8];
static int ne, nf;
static int TOTAL = 99;                       /* only pairs with ne + nf <= TOTAL */

static void pr(const char *t, const I *v, int n) {
  printf(" %s=", t);
  for (int i = 0; i < n; i++) printf("%lld ", (long long)v[i]);
}

static void check(void) {
  I o[16], c[16];
  int n = fes(E, ne, F, nf, o);
  tot++;
  if (MODE == 2) {
    I z[16]; int nz = 0;
    for (int i = 0; i < n; i++) if (o[i]) z[nz++] = o[i];
    for (int i = 0; i + 1 < nz; i++)
      if (!overlap_within(1, z[i], z[i + 1])) {
        if (++bad <= 5) { printf("FAIL"); pr("e", E, ne); pr("f", F, nf); pr("out", o, n); printf("\n"); }
        return;
      }
    return;
  }
  int m = clean(o, n, c);
  if (MODE == 1) shape(o, n);
  for (int i = 0; i + 1 < m; i++)
    if (!overlap_within(0, c[i], c[i + 1])) {
      if (++bad <= 5) { printf("FAIL"); pr("e", E, ne); pr("f", F, nf); pr("out", o, n); pr("clean", c, m); printf("\n"); }
      return;
    }
}

static int ok_next(I prev, int lastk, int i) {
  if (CLASS == 0) return ck[i] <= lastk - p;
  return iabs(comps[i]) < (((I)1) << lsb(prev));
}

static void genF(int depth, int lastk) {
  if (depth > 0) { nf = depth; check(); }
  if (depth == L || ne + depth >= TOTAL) return;
  for (int i = 0; i < nc; i++) {
    if (depth > 0 && !ok_next(F[depth - 1], lastk, i)) continue;
    F[depth] = comps[i];
    genF(depth + 1, ck[i]);
  }
}

static void genE(int depth, int lastk) {
  if (depth > 0) { ne = depth; genF(0, 0); }
  if (depth == L || depth + 1 >= TOTAL) return;     /* f is never empty */
  for (int i = 0; i < nc; i++) {
    if (depth == 0 && !FLOOR && ck[i] != 0) continue;
    if (depth > 0 && !ok_next(E[depth - 1], lastk, i)) continue;
    E[depth] = comps[i];
    genE(depth + 1, ck[i]);
  }
}

int main(int argc, char **argv) {
  if (argc < 7) {
    fprintf(stderr, "usage: %s P KLO KHI L MODE CLASS [FLOOR [TOTAL]]\n", argv[0]);
    return 2;
  }
  p = atoi(argv[1]); KLO = atoi(argv[2]); KHI = atoi(argv[3]);
  L = atoi(argv[4]); MODE = atoi(argv[5]); CLASS = atoi(argv[6]);
  FLOOR = argc > 7 ? atoi(argv[7]) : 0;
  if (argc > 8) TOTAL = atoi(argv[8]);
  if (p < 2 || L < 1 || L > 7 || KHI < KLO || MODE < 0 || MODE > 2 || TOTAL < 2) { fprintf(stderr, "bad arguments\n"); return 2; }
  int SH = FLOOR ? -KLO : -(KLO - 3 * p);
  for (int k = KLO; k <= KHI; k++)
    for (int m = 1 << (p - 1); m < (1 << p); m++)
      for (int s = -1; s <= 1; s += 2) {
        if (nc == 8192) { fprintf(stderr, "window too large\n"); return 2; }
        comps[nc] = (I)s * ((I)m << (k + SH));
        ck[nc++] = k;
      }
  if (FLOOR)
    for (int m = 1; m < (1 << (p - 1)); m++)
      for (int s = -1; s <= 1; s += 2) {
        int msb = 0;
        while ((m >> (msb + 1)) != 0) msb++;
        if (nc == 8192) { fprintf(stderr, "window too large\n"); return 2; }
        comps[nc] = (I)s * (I)m;             /* m * 2^emin, subnormal */
        ck[nc++] = KLO + msb - (p - 1);      /* Priest exponent, below emin */
      }
  genE(0, 0);
  if (MODE == 1)
    printf("SHAPE pattern=%lld reduction=%lld cascades=%lld twins=%lld antis=%lld\n",
           pattern_bad, reduction_bad, cascades, twins, antis);
  if (MODE == 1) {
    printf("RAW overlap=%lld not_strictly_desc=%lld\n", raw_overlap, raw_notdesc);
    printf("PAIRS per output:");
    for (int k = 0; k < 8; k++) if (pairs_hist[k]) printf(" %d:%lld", k, pairs_hist[k]);
    printf("\n");
    for (int n = 3; n < 16; n++)
      for (int k = 3; k <= n; k++)
        if (tie_at[n][k][0] || tie_at[n][k][1] || tie_at[n][k][2])
          printf("TIE n=%d step %d: anti=%lld twin=%lld singles=%lld\n", n, k,
                 tie_at[n][k][0], tie_at[n][k][1], tie_at[n][k][2]);
  }
  printf("SUMMARY p=%d K=[%d,%d] L=%d mode=%d class=%d floor=%d total=%d pairs=%lld fails=%lld\n",
         p, KLO, KHI, L, MODE, CLASS, FLOOR, TOTAL, tot, bad);
  return (bad || (MODE == 1 && (pattern_bad || reduction_bad))) ? 1 : 0;
}
