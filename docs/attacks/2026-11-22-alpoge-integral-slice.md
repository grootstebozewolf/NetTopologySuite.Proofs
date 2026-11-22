<!-- doc-kind: finding
date: 2026-11-22
Provenance: 0a2d842
Theorems: `AlpogeIntegralQED.v : RI_lipschitz`, `AlpogeIntegralQED.v : rsum_inv_cv`, `AlpogeIntegralQED.v : windowHyp_of_rpow`, `AlpogeSkeleton.v : integral_slice_proved_is_refined`
-->
# Alpöge main line: allowlist-clean integration, and windowHyp_of_rpow proved over R (34/39 with #1047)

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

## Relation to #1047 (`CleanIntegralQED.v`), merged concurrently

While this slice was in review, #1047 landed a more general allowlist-clean
library, `docs/h1-vacuity/CleanIntegralQED.v`
(`docs/attacks/2026-11-22-clean-integral-library.md`). It provides:
- tagged-partition integrals (`RInt`);
- linearity, monotonicity and Chasles;
- its own one-sided mean value theorem, and FTC;
- change of variables and improper integrals;
- proofs of `kernel_integral` and `windowHyp_of_rpow_r`.

The two files overlap and complement each other:
- **`windowHyp_of_rpow` is now proved twice.** It is proved here for
  `WindowHypR` with Stdlib-style `IntVal` (`Riemann_integrable` plus
  uniform sums, as in `AlpogeDeepStatements.v`), and in #1047 with `RInt`.
  The two `WindowHypR` definitions differ only in the integral notion.
- **`RI_lipschitz` is not in #1047.** It yields integrability in
  **Stdlib's own sense** (`Riemann_integrable`, built from step functions),
  which is what `AlpogeDeepStatements.v`'s statements use. #1047's `RInt` is
  a separate notion, and the two are not linked by a proof here.
- **`kernel_integral`** (proved in #1047) now counts as proved over `R`.

`AlpogeSkeleton.v : integral_slice_proved_is_refined` checks that
`windowHyp_of_rpow` and `kernel_integral` are refined ledger items. It also
checks that the **34** items proved over `R` are distinct, and the skeleton
`Check`s both `CleanIntegralQED.kernel_integral` and
`CleanIntegralQED.windowHyp_of_rpow_r`.

## Status of the 5 still-blocked items (after #1047)

| item | what remains |
|---|---|
| `windowHypU_of_windowHyp` | #1047's `windowU_change_var` covers majorants whose y-integrand has an antiderivative. A merely integrable majorant needs FTC part 1. |
| `landau_window_ineq` | #1047 provides splitting (`RIntInf_chasles`) and monotonicity. The triangle inequality for complex integrals still needs integrability of `\|f\|`. |
| `landau_tails_chernoff` | the tools now exist (`RIntInf_chasles`, `RIntInf_le`); not yet assembled |
| `landau_coeff` | the obstruction is gone (`RInt_scal`); not yet assembled |
| `landau_cauchy` | Cauchy integral formula |

## OUTCOME

**QED.** Within the allowlist:
- Lipschitz functions are integrable in Stdlib's own sense;
- the logarithmic integral is available;
- `windowHyp_of_rpow` is proved over `R`.

Together with #1047's `kernel_integral`, **34 of 39** refined items are now
proved over `R`.

The Alpöge verdict is unchanged: **PASS-STATIC / PENDING**.

**SUMMARY ok 3 / warn 0 / bug 0.**
