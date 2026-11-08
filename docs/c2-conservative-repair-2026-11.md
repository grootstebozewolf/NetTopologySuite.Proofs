# Conservative (outward-rounded) repair of the closed Liang-Barsky filter (2026-11)

Provenance: Rocq 9.2.0 + Flocq 4.2.2, local `Makefile.gen` build on branch tip
`f820159` (no CI run id). Modules:
`theories-flocq/PassesThrough_b64_conservative.v` (design + proofs),
`theories-flocq/PassesThrough_b64_conservative_replay.v` (witness replay).
Outcome: **REPAIR-QED**.

## Architecture note

The geometry is proved ONCE, generically, over an enclosure contract on six
directed primitives (`dprims`; theorems `g_q_lower_ok`, `g_q_upper_ok`,
`g_axis_lo_ok`, `g_axis_hi_ok`, `g_touches_complete`). The Flocq-mode filter described
below is the instance `flocq_prims`; its theorem names (`q_lower_ok` ... in the table)
are now aliases/instances of the generic ones. The nearest-plus-pred/succ filter is a
second instance: [`c2-executable-repair-2026-11.md`](c2-executable-repair-2026-11.md).
The contract is enclosure, not equality with Flocq (equality is false for the
executable instance).

## Theorems (all Qed, no Admitted)

| claim | theorem |
|---|---|
| every directed op encloses its exact result, overflow excluded | `minus_m_ok`, `plus_m_ok`, `div_m_ok`, `round_dn_le`, `round_up_ge` |
| outward division, positive and negative denominators | `lowP1/2`, `upP1/2` (b>0); `lowN1/2`, `upN1/2` (b<0) |
| quotient interval contains the exact quotient | `q_lower_ok` (computed lower <= a/b), `q_upper_ok` (a/b <= computed upper) |
| four Liang-Barsky bounds, polarity | `axis_lo_ok` (computed lower <= lb_tlo), `axis_hi_ok` (lb_thi <= computed upper) |
| exact interval nonempty => computed nonempty | inside `b64_touches_complete_cons` |
| exact touch accepted, every binary64 triple | `b64_touches_complete_cons`, `b64_passes_through_complete_cons` |
| old C2 witness accepted | `c2_repair_accepts_witness`, `c2_repair_polarity_at_witness` |

`Print Assumptions` for every theorem above: only `sig_not_dec`,
`sig_forall_dec`, `functional_extensionality_dep` (real-number axioms) and
`Classical_Prop.classic` (Flocq). No new axiom.

## Construction

Every operation is evaluated twice with IEEE directed rounding (Flocq
`mode_DN` / `mode_UP` on `Bminus`/`Bplus`/`Bdiv`), so each result has
binary64 endpoints enclosing the exact real. For axis coordinate c0 -> c1, pixel
centre cc:

* lo = cc - 1/2 in [lo_m, lo_p], hi = cc + 1/2 in [hi_m, hi_p]
* numerators a_lo = lo - c0 in [pmin, pmax] = [DN(lo_m - c0), UP(lo_p - c0)];
  a_hi = hi - c0 in [rmin, rmax] likewise
* denominator b = c1 - c0 in [bmin, bmax] = [DN(c1-c0), UP(c1-c0)]

**Interval formulas** (n = numerator interval [nmin, nmax]):

| denominator | lower bound of n/b | upper bound of n/b |
|---|---|---|
| b > 0 (bmin >= 2^-500) | DN( nmin / (0 <= nmin ? bmax : bmin) ) | UP( nmax / (0 <= nmax ? bmin : bmax) ) |
| b < 0 (bmax <= -2^-500) | DN( nmax / (nmax <= 0 ? bmin : bmax) ) | UP( nmin / (nmin <= 0 ? bmax : bmin) ) |
| interval touches 0 or is within 2^-500 of it | unbounded (no constraint) | unbounded |

The negative-denominator cases are NOT the positive ones with endpoints
swapped: they use different (numerator, denominator) combinations (proved
separately; the divisions are not monotone in the same direction).

Axis lower bound = min(lower(p), lower(r)) (tlo = min(p,r) >= that); axis upper
bound = max(upper(p), upper(r)); a degenerate axis (c1 = c0) contributes 0 / 1 and
uses an outward slab guard lo_m <= c0 <= hi_p. Then
Tminus = max(0, lo_x, lo_y), Tplus = min(1, hi_x, hi_y), accept iff Tminus <= Tplus.
An unbounded bound is skipped in the max/min (it is -inf / +inf).

## nextDown / nextUp

Not used. Directed rounding is applied per operation by Flocq's `mode_DN` /
`mode_UP`, so each endpoint is round-toward-minus/plus-infinity of the exact
operation (`round_DN_pt` / `round_UP_pt`). The same enclosure can be obtained
from round-to-nearest plus pred/succ of EACH operation (not only the final
quotient); that variant is not formalised. Extracting this module to native
floats therefore needs either IEEE rounding-mode control or that pred/succ
emulation: not wired into the oracle.

## Special values

* **zero**: a zero or zero-straddling denominator interval falls in the
  "unbounded" row; zero numerators are ordinary.
* **subnormal**: no special case; the enclosure lemmas hold for gradual
  underflow (FLT with subnormals).
* **overflow**: excluded by construction. Domain |c| <= 2^500 gives every
  subtraction |.| <= 2^502 << 2^1024; the 2^-500 denominator guard gives
  |n/d| <= 2^1002 < 2^1024 (`div_abs_bound`).
* **infinity / NaN / |c| > 2^500**: the whole touch ACCEPTS (`b64_dom`).

## Answers to the design questions

* **Changes the specification?** No. `b64_passes_through_hot_pixel` is untouched;
  the old `..._compute` is untouched (its counterexample stands). A new filter
  `b64_passes_through_hot_pixel_cons` is added.
* **False positives?** Yes, by design: outward widening by a few ulps (the
  witness interval is [0x1.c71c71c71c71bp-4, 0x1.c71c71c71c71dp-4] around 1/9),
  the unbounded branch for denominators < 2^-500 (an axis with
  0 < |c1 - c0| < 2^-500 contributes no constraint), and out-of-domain accepts.
* **Extra operations per bound**: shared per axis 10 directed add/sub (old: 5);
  per Liang-Barsky bound (lower or upper of an axis) 2 directed divisions
  (p and r), at most 3 comparisons per quotient (2 guard, 1 selection) and 1
  min/max. Per axis: 4 divisions (old: 2) and at most ~14 comparisons.

## Witness replay

Old filter: that_x = 0x1.c71c71c71c71dp-4 > that_y = 0x1.c71c71c71c71cp-4,
rejects. Repair: lower_x = 8006399337547547 * 2^-56 = 0x1.c71c71c71c71bp-4 <= 1/9,
upper_y = 8006399337547549 * 2^-56 = 0x1.c71c71c71c71dp-4 >= 1/9, so the
interval is nonempty and `b64_passes_through_hot_pixel_cons c2P0 c2P1 c2C = true`.

SUMMARY ok=7 warn=1 bug=0
