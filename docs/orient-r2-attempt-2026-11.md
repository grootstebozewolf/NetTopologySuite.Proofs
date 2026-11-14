<!-- doc-kind: finding
date: 2026-11-08
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# R2 attempt: sign agreement of the binary64 orient2d determinant (2026-11)

Provenance: Rocq 9.2.0 + Flocq 4.2.2, local `Makefile.gen` build on top of
branch tip `89ae916` (no CI run id). Module: `theories-flocq/Orient_b64_R2.v`.
Not routed through the over/under/gap framework; no new taxonomy.

## Target

D = `cross_R_BP` = A·B − C·Dd (exact), Dhat = B2R(`b64_orient2d`). Prove
|Dhat − D| ≤ E ∧ E < |D| → sign Dhat = sign D, then decide whether the corpus
gives E < |D| off-grid.

## Outcome

| Piece | Result |
|---|---|
| Bridge `sign_of_error_bound` | proved (elementary reals) |
| Premise 1, forward error | **not in the corpus** (`Orient_b64_sound.v` header carries it as prose only; the filter-soundness theorems exist only in the integer regime). Proved here: `b64_orient2d_forward_error`, under the corpus's own `b64_orient2d_safe`. |
| `b64_orient2d_R2` | proved: premise 1 discharged; separation `o2_E < |D|` is the only hypothesis |
| Premise 2, separation | **NOT dischargeable**; bracketed below |

`o2_E = 6u(|AB| + |C·Dd|) + 6e(|A|+|B|+|C|+|Dd| + 1)`, u = 2^-53,
e = 2^-1075. The e-term is the absolute underflow floor, without which the bound is
false in the underflow regime (the corpus's own `Orient_b64_underflow_unsound`
witness). Constants are crude (4.2u would do), not Shewchuk's. Built from
`b64ae_round_err` (B64_AbsErr) + `b64_minus_correct`/`b64_mult_correct`:
the only new content is the real-arithmetic composition (`mul_err`,
`prod_err`, `chain`). `Print Assumptions`: only the repo's allowlisted
real-number axioms plus Flocq's `Classical_Prop.classic`.

## Separation: both sides proved

* `o2_separation_tight_grid`: integer coordinates, |n| ≤ 2^22, D ≠ 0 ⇒
  o2_E < |D| (E < 0.1, |D| ≥ 1). So R2 is unconditional there.
* `o2_separation_fails_on_int_grid`: inside the corpus's own
  `orient2d_inputs_int_safe` (|n| ≤ 2^25), P0=(0,0), P1=(n,n−1), Q=(n−1,n−2),
  n=2^25−1: D = −1 ≠ 0 yet o2_E ≥ 1.33. (Arithmetic there is exact in the
  corpus, so the sign is right; the *premise* fails, not the sign.)

Hence no domain predicate of the form "finite / bounded / int-safe" implies the
separation, and a fortiori not general off-grid inputs.

## The smallest missing lemma (pure mathematics)

For the orientation kernel the separation is a *lattice-width* condition, not a
domain property. Stated, **not proved here**:

> If every coordinate is X·2^-k with integer |X| ≤ 2^22 and 12·e·(m+1) < 2^-2k,
> then D ≠ 0 ⇒ |D| ≥ 2^-2k > o2_E.

(2^-k scaling is exact, so k cancels against the u-term and the width bound is
k-invariant; this is the same proof as `o2_separation_tight_grid` with a
power-of-two scale, I expect, but I did not carry it out.) For arbitrary
off-grid doubles no such lemma exists: D can be arbitrarily small relative to
|AB|+|C·Dd|.

## Does this settle off-grid C2? No, and not for the reason R2 targets

1. C2 is **spec ⇒ compute** (completeness). On the grid that direction used
   monotone rounding (`round_le`, `b64_tmin_eq_round_exact_grid`) and needed
   no separation; separation (`PassesThrough_b64_grid_separation.v`) served the
   *soundness* direction. R2-type premises cannot reach completeness at all:
   the spec's closed boundary case (tmin = tmax exactly, gap 0) is excluded by
   any premise |D| > E.
2. The grid identity "computed t-bound = round(exact t-bound)" holds because
   the numerators/denominators are exact integers. Off grid they are
   themselves rounded (`fl(cx − 1/2)`, `fl(· − x0)`), so the identity is
   false and the monotone-rounding argument has nothing to act on. That, not a
   separation gap, is the structural fact missing for C2.
3. The C2 compute path is rounded `b64_div`, not `b64_orient2d`; R2 would
   apply only after cross-multiplying the quotient comparison.

SUMMARY ok=4 warn=2 bug=0
