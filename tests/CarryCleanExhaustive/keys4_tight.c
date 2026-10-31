/* ===========================================================================
   keys4_tight.c -- are the two keys of B64_CarryCleanRung3.fes4_shape_of_keys
   both needed?

   fes4_shape_of_keys takes four components with |g3| <= |g4| and the keys
     K1: |g1| < ulp(g3)        K2: |g2| < ulp(g4)
   and proves that the raw output [Q4; h4; h3; h2] of three chained TwoSums
   (zeros dropped) is strictly decreasing and nonoverlapping.  This program
   enumerates every sorted quadruple |g1| <= |g2| <= |g3| <= |g4| of p-bit
   values m * 2^k (signs both ways, k in [0, K), plus zero), keeps those
   satisfying the selected keys, and counts outputs that are NOT strictly
   decreasing and nonoverlapping.  Round to nearest even, unbounded exponents.

   Build and run:
     cc -O2 -o keys4_tight keys4_tight.c
     ./keys4_tight P K KEYS
   KEYS selects the hypotheses kept: 3 = both, 1 = K1 only (K2 dropped),
   2 = K2 only (K1 dropped).

   Recorded results (2026-10-31):
     p  K  KEYS  quadruples    bad  first bad: g1 g2 g3 g4 -> Q4 h4 h3 h2
     2  8   3         44368      0
     3  8   3        358272      0
     4  7   3        936688      0
     3  7   1        293304   3108  0 4 5 5 -> 12 1 1 0      (twin 1, 1)
     3  7   2        282640   1984  4 5 5 32 -> 48 -4 1 1    (twin 1, 1)
     4  7   1       2427696  24132  0 8 9 9 -> 24 1 1 0
     4  7   2       2298720  15104  8 9 9 128 -> 160 -8 1 1
   Both keys: no bad output.  Dropping either key admits overlapping outputs
   in the p-bit model, so neither hypothesis of fes4_shape_of_keys can be
   dropped there.  Reconnaissance only: no binary64 witness is pinned, and
   the proof is B64_CarryCleanRung3.v.

   Assisted-by: Claude
   =========================================================================== */
#include <stdio.h>
#include <stdlib.h>

typedef __int128 I;

static int p;

static I iabs(I x) { return x < 0 ? -x : x; }

static I rnd(I x) {
  if (!x) return 0;
  int s = x > 0 ? 1 : -1;
  I a = iabs(x);
  int n = 0;
  for (I t = a; t; t >>= 1) n++;
  int sh = n - p;
  if (sh <= 0) return x;
  I q = a >> sh, r = a - (q << sh), half = ((I)1) << (sh - 1);
  if (r > half || (r == half && (q & 1))) q++;
  return s * (q << sh);
}

/* TwoSum, exactly: s = RN(x + y), e = x + y - s (representable). */
static void two_sum(I x, I y, I *s, I *e) { *s = rnd(x + y); *e = x + y - *s; }

static int lsb(I x) { int k = 0; for (x = iabs(x); !(x & 1); x >>= 1) k++; return k; }

static int nonoverlapping(I a, I b) {
  if (!a || !b) return 1;
  return iabs(b) < (((I)1) << lsb(a)) || iabs(a) < (((I)1) << lsb(b));
}

/* ulp of a nonzero p-bit value; ulp(0) is never compared (keys need g3, g4
   nonzero, and |g| < ulp(0) is false for every g below). */
static I ulp(I x) {
  if (!x) return 0;
  int n = 0;
  for (I t = iabs(x); t; t >>= 1) n++;
  return ((I)1) << (n - p);
}

static void pr(I x) { printf("%lld ", (long long)x); }

int main(int argc, char **argv) {
  if (argc < 4) { fprintf(stderr, "usage: %s P K KEYS\n", argv[0]); return 2; }
  p = atoi(argv[1]);
  int K = atoi(argv[2]), KEYS = atoi(argv[3]);
  if (p < 2 || K < 1 || p + K > 40 || KEYS < 1 || KEYS > 3) { fprintf(stderr, "bad arguments\n"); return 2; }
  static I v[1 << 14];
  int nv = 0;
  v[nv++] = 0;
  for (int k = 0; k < K; k++)
    for (int m = 1 << (p - 1); m < (1 << p); m++) { v[nv++] = (I)m << k; v[nv++] = -((I)m << k); }
  for (int i = 1; i < nv; i++)                     /* sort by magnitude */
    for (int j = i; j > 0 && iabs(v[j]) < iabs(v[j - 1]); j--) { I t = v[j]; v[j] = v[j - 1]; v[j - 1] = t; }
  long long tot = 0, bad = 0;
  for (int a = 0; a < nv; a++)
    for (int b = 0; b < nv; b++) {
      if (iabs(v[b]) < iabs(v[a])) continue;
      for (int c = 0; c < nv; c++) {
        if (iabs(v[c]) < iabs(v[b])) continue;
        if ((KEYS & 1) && !(v[c] && iabs(v[a]) < ulp(v[c]))) continue;             /* K1 */
        for (int d = 0; d < nv; d++) {
          if (iabs(v[d]) < iabs(v[c])) continue;
          I g1 = v[a], g2 = v[b], g3 = v[c], g4 = v[d];
          if ((KEYS & 2) && !(g4 && iabs(g2) < ulp(g4))) continue;                  /* K2 */
          if (!g4) continue;
          I Q2, h2, Q3, h3, Q4, h4;
          two_sum(g2, g1, &Q2, &h2); two_sum(g3, Q2, &Q3, &h3); two_sum(g4, Q3, &Q4, &h4);
          I o[4] = { Q4, h4, h3, h2 }, z[4];
          int nz = 0, ok = 1;
          for (int i = 0; i < 4; i++) if (o[i]) z[nz++] = o[i];
          for (int i = 0; i + 1 < nz; i++)
            if (!(iabs(z[i]) > iabs(z[i + 1])) || !nonoverlapping(z[i], z[i + 1])) ok = 0;
          tot++;
          if (!ok && ++bad == 1) {
            printf("FIRST BAD g="); pr(g1); pr(g2); pr(g3); pr(g4);
            printf("out="); pr(Q4); pr(h4); pr(h3); pr(h2); printf("\n");
          }
        }
      }
    }
  printf("SUMMARY p=%d K=%d keys=%d quadruples=%lld bad=%lld\n", p, K, KEYS, tot, bad);
  return (KEYS == 3 && bad) ? 1 : 0;
}
