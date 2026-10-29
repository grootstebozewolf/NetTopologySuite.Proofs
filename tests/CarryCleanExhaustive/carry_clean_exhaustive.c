/* ===========================================================================
   carry_clean_exhaustive.c -- exhaustive small-precision evidence for
   theories-flocq/B64_CarryClean.v.

   Models, in p-bit binary arithmetic with round-to-nearest-even and no
   exponent bounds, exactly the corpus algorithms:
     - fast_expansion_sum (B64_FastExpansionSum_Shewchuk.v): insertion sort
       by |x| (x goes before y iff |x| <= |y|), TwoSum cascade
       (Q, h) := TwoSum(g_i, Q), output Q :: rev hs;
     - cc_push / cc_run (B64_CarryClean.v): MODE 0 = cancel_clean,
       MODE 1 = carry_clean.
   and enumerates EVERY input pair in a window, checking that the cleanup's
   output is nonoverlapping in Shewchuk's sense (|next| < 2^lsb(prev) or the
   symmetric case).  Values are scaled integers, so the model is exact; each
   TwoSum is checked to be error-free.

   Inputs: CLASS 0 = Priest expansions (normalised p-bit significands,
   exponent gap >= p); CLASS 1 = Shewchuk-nonoverlapping expansions
   (|next| < 2^lsb(prev)).  e's top exponent is fixed at 0 (scale
   invariance); f ranges over exponents [KLO, KHI]; lengths 1..L.

   Build and run:
     cc -O2 -o carry_clean_exhaustive carry_clean_exhaustive.c
     ./carry_clean_exhaustive P KLO KHI L MODE CLASS

   Recorded results (2026-10-29):
     p KLO KHI L MODE CLASS       pairs   fails
     3  -9   4 3   0    0    366766976     680   cancel_clean refuted
     3  -9   4 3   1    0    366766976       0   carry_clean, Priest
     2  -8   3 4   1    0    148581504       0
     5 -10   5 2   1    0    420560896       0
     3  -7   2 3   1    1    130842880     758   carry_clean, nonoverlapping
   Every Priest-class overlap before cleanup (p = 3, [-7,2], 22,576,768
   pairs) was a pair of equal-magnitude powers of two.  The CLASS 1 failure
   family lifts to binary64 (B64_CarryClean.v, QEX 2).

   Prints one FAIL line per failing pair (up to five) and a final
   SUMMARY line.

   Assisted-by: Claude
   =========================================================================== */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef __int128 I;

static int p, KLO, KHI, L, MODE, CLASS;

static I iabs(I x) { return x < 0 ? -x : x; }

static I rnd(I x) {
  if (!x) return 0;
  int s = x > 0 ? 1 : -1;
  I a = iabs(x);
  int n = 0;
  for (I t = a; t; t >>= 1) n++;
  if (n <= p) return x;
  int sh = n - p;
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

static int nonov(I a, I b) {
  if (!a || !b) return 1;
  return iabs(b) < (((I)1) << lsb(a)) || iabs(a) < (((I)1) << lsb(b));
}

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
  for (int i = 1; i < ns; i++) { I a, b; two_sum(s[i], q, &a, &b); q = a; hs[nh++] = b; }
  out[0] = q;
  for (int i = 0; i < nh; i++) out[1 + i] = hs[nh - 1 - i];
  return 1 + nh;
}

static int clean(const I *o, int n, I *st) {
  int k = 0;
  for (int i = 0; i < n; i++) {
    I x = o[i];
    if (!x) continue;
    for (;;) {
      if (k && st[k - 1] == -x) { k--; x = 0; break; }
      if (MODE == 1 && k && st[k - 1] == x) { k--; x = 2 * x; continue; }
      break;
    }
    if (x) st[k++] = x;
  }
  return k;
}

static I comps[4096];
static int ck[4096], nc;
static long long tot, bad;
static I E[8], F[8];
static int ne, nf;

static void pr(const char *t, const I *v, int n) {
  printf(" %s=", t);
  for (int i = 0; i < n; i++) printf("%lld ", (long long)v[i]);
}

static void check(void) {
  I o[16], c[16];
  int n = fes(E, ne, F, nf, o), m = clean(o, n, c);
  tot++;
  for (int i = 0; i + 1 < m; i++)
    if (!nonov(c[i], c[i + 1])) {
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
  if (depth == L) return;
  for (int i = 0; i < nc; i++) {
    if (depth > 0 && !ok_next(F[depth - 1], lastk, i)) continue;
    F[depth] = comps[i];
    genF(depth + 1, ck[i]);
  }
}

static void genE(int depth, int lastk) {
  if (depth > 0) { ne = depth; genF(0, 0); }
  if (depth == L) return;
  for (int i = 0; i < nc; i++) {
    if (depth == 0 && ck[i] != 0) continue;
    if (depth > 0 && !ok_next(E[depth - 1], lastk, i)) continue;
    E[depth] = comps[i];
    genE(depth + 1, ck[i]);
  }
}

int main(int argc, char **argv) {
  if (argc < 7) {
    fprintf(stderr, "usage: %s P KLO KHI L MODE CLASS\n", argv[0]);
    return 2;
  }
  p = atoi(argv[1]); KLO = atoi(argv[2]); KHI = atoi(argv[3]);
  L = atoi(argv[4]); MODE = atoi(argv[5]); CLASS = atoi(argv[6]);
  if (p < 2 || L < 1 || L > 7 || KHI < KLO) { fprintf(stderr, "bad arguments\n"); return 2; }
  int SH = -(KLO - 3 * p);
  for (int k = KLO; k <= KHI; k++)
    for (int m = 1 << (p - 1); m < (1 << p); m++)
      for (int s = -1; s <= 1; s += 2) {
        if (nc == 4096) { fprintf(stderr, "window too large\n"); return 2; }
        comps[nc] = (I)s * ((I)m << (k + SH));
        ck[nc++] = k;
      }
  genE(0, 0);
  printf("SUMMARY p=%d K=[%d,%d] L=%d mode=%d class=%d pairs=%lld fails=%lld\n",
         p, KLO, KHI, L, MODE, CLASS, tot, bad);
  return bad ? 1 : 0;
}
