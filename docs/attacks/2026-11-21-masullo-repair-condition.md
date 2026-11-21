<!-- doc-kind: finding
date: 2026-11-21
Provenance: b7cc174
Theorems: `MasulloRepairCondition.v : repair_partial_sums_bounded`, `MarkushevichBoundQEX.v : psi_unbounded`
-->
# What would rescue Masullo's (10.3.1.18)? A conditional repair statement

Companion to `2026-11-21-masullo-grh-draft.md` (slices 3–9). That finding
was merged and is immutable, so this follow-up gets its own file. The gap
itself is upstream **mccorvie/riemann-masullo#1169**, reported first there.
This finding asks the next question: **under what condition does the
nuclearity estimate of §10.3 survive** once the uniform `C` is gone?

## The estimate and its repair

**The estimate.** In A. M. Masullo, *The Music of the Primes* (draft
2026-11-20), p. 451, inequality (10.3.1.20) bounds the singular values of
the finite-rank pieces:

`σ_m(A_{(k,j)}) ≤ N_s · C · 2^{N_s−1} · Σ_{i<N_s} |φ̂^{(i)}(t_{k,j})|`,

with `N_s ≤ (s−1)/2 + 1`. Nuclearity of `A = Σ_{(k,j)} A_{(k,j)}`, and with it
the spectral side, then follows from `Σ_{(k,j)} |φ̂^{(i)}(t_{k,j})| < ∞`:
`φ̂` decays faster than any polynomial, and there are `≪ T log T` zeros.

**The repair.** With a zero-dependent constant `C_t` (for example
`C_t = sup_m ‖η_{t,m'}‖·‖ψ_{t,m}‖`), the same argument goes through if

`Σ_t C_t · Σ_i |φ̂^{(i)}(t)| < ∞`.

## Sufficient condition (summation skeleton machine-checked)

The sum converges if
- **(P)** `C_t ≤ A·(1+|t|)^K` for some `A`, `K` (polynomial growth), and
- the decay of `φ̂` (for every `M`, `|φ̂^{(i)}(t)| ≤ B_M(1+|t|)^{−M}`, which
  holds since `φ ∈ D(C_F)`) is used with `M = K+4`.

The zero count `#{|t| ∈ [2^j, 2^{j+1})} ≤ D·4^{j+1}` is crude (`T²` against
the true `T log T`) but enough.

`docs/h1-vacuity/MasulloRepairCondition.v : repair_partial_sums_bounded`
(Stdlib, `Q`) is *Closed under the global context*. For dyadic shells
`j` with at most `c_j ≤ D·4^{j+1}` terms, each at most `E·16^{−j}`,
every partial sum is bounded by `(16/3)·D·E`.
- The per-term bound `E·16^{−j}` is what `C_t|φ̂(t)| ≤ A·B·(1+|t|)^{−4}` gives on
  `|t| ∈ [2^j, 2^{j+1})`.
- The passage from (P) plus decay to that per-term bound is a translation
  (exponent arithmetic), and is not re-proved.

## Is (P) available? (reading)

`MarkushevichBoundQEX.v : psi_unbounded` and its lemma `close_pair_lower`
give `‖ψ_t‖ ≥ 1/‖η_t − η_{t'}‖`, and `‖η_t − η_{t'}‖ → 0` as `|t − t'| → 0`.
So `C_t` is bounded below by roughly the reciprocal of a power of the gap
from `t` to the nearest other critical-zero ordinate. **(P) therefore needs,
at least, a polynomial lower bound on gaps between consecutive distinct
critical-zero ordinates.** No such bound is known unconditionally. Bounds of
this kind are tied to open questions about the fine spacing of zeros, which
include their simplicity.

Two further cautions, both readings:
- (P) is **sufficient, not necessary**. A repair could instead exploit
  cancellation among neighbouring pieces, or regroup close zeros into blocks
  whose combined projector is controlled. The draft does neither on
  pp. 450–455.
- Even with (P), §10.3 would still need `C_t` defined and bounded through the
  quotient norm on `H^s_{F,a}`. That is the same setting as #1169's remark
  that the inequality survives taking the infimum over representatives.

## OUTCOME

**CONDITIONAL.** The nuclearity sum of §10.3 converges under (P). Its
summation skeleton is machine-checked, with the decay and zero count as
hypotheses. (P) is roughly equivalent to an unconditional polynomial
gap lower bound for critical zeros, which is not known. So the "make `C`
depend on `t`" repair is open exactly to the extent that such a gap bound is.
No claim is made about other repair routes.

**SUMMARY ok 1 / warn 1 (repair needs an unknown gap bound) / bug 0.**
