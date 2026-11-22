<!-- doc-kind: finding
date: 2026-11-22
Provenance: 0a2d842
Theorems: `AlpogeIntegralQED.v : RI_lipschitz`, `AlpogeIntegralQED.v : rsum_inv_cv`, `AlpogeIntegralQED.v : windowHyp_of_rpow`, `AlpogeSkeleton.v : integral_slice_proved_is_refined`
-->
# Alpöge main line: allowlist-clean integration, and windowHyp_of_rpow proved over R (33/39)

Follows `2026-11-21-alpoge-third-batch-over-reals.md`. That finding left 7
refined items blocked: they need integral facts, and Stdlib's integral
theory is outside the corpus allowlist. This slice builds the first piece of
an allowlist-clean integration toolkit and proves one blocked item with it.

External subject: mirror `CocoSgt/riemann-hypothesis-lean` @ `7cbf7a0`, read
from source; nothing was built.

## Which Stdlib pieces are clean (`Print Assumptions`)

| carries `Classical_Prop.classic` | allowlist-clean |
|---|---|
| `continuity_implies_RiemannInt`, `RiemannInt_P6` (through `Heine_cor2`) | `Riemann_integrable` (the definition), `Riemann_integrable_ext`, `RiemannInt_P1` |
| `SubEqui`, `SubEqui_P1`–`P9` (equidistant subdivision, through `maxN`) | `StepFun_P38` (a step function from any ordered list), `StepFun_P4`, `StepFun_P18` |
| `MVT`, `MVT_cor1`, `MVT_cor2`, `Rolle`, `derive_increasing_interv`, `null_derivative_loc` | `archimed`, `Rle_cv_lim`, `CV_plus`, `CV_mult`, `sum_eq`, `minus_sum`, `sum_Rle` |
| the value `RiemannInt`, `RiemannInt_P10`, `RiemannInt_P11` | |

## Rocq (`docs/h1-vacuity/AlpogeIntegralQED.v`), within the allowlist

| result | content | axioms |
|---|---|---|
| `RI_lipschitz` | A function that is Lipschitz on `[a,b]` is `Riemann_integrable` in **Stdlib's own sense**. The proof builds the equidistant subdivision directly (`eqlist`, `cell_index` via `archimed`, `meshN`), so it avoids `SubEqui` and Heine. The modulus is explicit, since `Riemann_integrable` lives in `Type`. | `sig_forall_dec`, `fun_ext` |
| `rsum_inv_cv` | For `0 < a ≤ b`, the uniform Riemann sums of `1/y` on `[a,b]` converge to `Lc b − Lc a`. The proof brackets each step with `(x'−x)/x' ≤ Lc x' − Lc x ≤ (x'−x)/x` (from `1 − 1/t ≤ log t ≤ t − 1`), then telescopes. The error is at most `(b−a)(1/a−1/b)/(n+1)`. No mean value theorem is used. | all 3 |
| `windowHyp_of_rpow` (WindowHypOfRpow.lean) | `WindowHyp` from the rpow window bound, as in Lean (see below) | all 3 |

**How `windowHyp_of_rpow` goes.** It uses the majorant `R y = |C|·y^θ`
(`rpc`):
1. The integrand `R y·y^{−θ−1}` equals `|C|/y` on the window. It is
   integrable by `RI_lipschitz` (constant `|C|/Y²`) with
   `Riemann_integrable_ext`.
2. Its integral is `|C|(Lc(Y^{1+δ}) − Lc Y) = |C|·δ·Lc Y`, by
   `rsum_inv_cv`.
3. That is at most `Y^η`, by `windowHyp_of_rpow_eventually` (already proved
   over `R`).

`WindowHypR` writes Lean's `WindowHyp` over `R`: the integrability and the
integral are an `IntVal` (`Riemann_integrable` plus the limit of uniform
Riemann sums, from `AlpogeDeepStatements.v`).

`AlpogeSkeleton.v : integral_slice_proved_is_refined` checks that
`windowHyp_of_rpow` is a refined ledger item, and that the 33 items proved
over `R` are distinct.

## Status of the 6 still-blocked items

| item | what remains |
|---|---|
| `windowHypU_of_windowHyp` | change of variables `y = e^u` for the integral (the substitution is nonlinear, so uniform sums do not map to uniform sums) |
| `landau_window_ineq` | additivity over `window ∪ tails`, and the triangle inequality for complex integrals |
| `kernel_integral` | the exact improper integral. `RI_lipschitz` now gives integrability on `[0,T]`. The value needs bracketing of `u^k e^{−au}` against its antiderivative, then `T → ∞`. |
| `landau_tails_chernoff` | additivity and set-monotonicity of improper integrals |
| `landau_coeff` | linearity of `IntVal`: integrability of `c·f`, now constructible by `RI_lipschitz` for Lipschitz `f`, or by a direct step-function scaling |
| `landau_cauchy` | Cauchy integral formula |

`RI_lipschitz` and the bracketing method are the reusable pieces. The next
natural targets are `landau_coeff` (via linearity) and `kernel_integral`
(via bracketing).

## OUTCOME

**QED.** Riemann integrability of Lipschitz functions and the logarithmic
integral are now available within the allowlist. `windowHyp_of_rpow` is
proved over `R`, bringing the total to **33 of 39** refined items.

The Alpöge verdict is unchanged: **PASS-STATIC / PENDING**.

**SUMMARY ok 3 / warn 0 / bug 0.**
