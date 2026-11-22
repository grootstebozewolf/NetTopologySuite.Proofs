<!-- doc-kind: finding
date: 2026-11-21
Provenance: 50d953a
Theorems: `AlpogeRealsQED3.v : landau_dichotomy`, `AlpogeRealsQED3.v : landau_nearest`, `AlpogeRealsQED3.v : landau_window`, `AlpogeRealsQED3.v : landau_tails`, `AlpogeRealsQED3.v : landau_window_key`, `AlpogeRealsQED3.v : proposition_size_bound`, `AlpogeRealsQED3.v : ch_core`, `AlpogeRealsQED3.v : landau_pole_re_le_bound`, `AlpogeSkeleton.v : third_batch_proved_are_refined`
-->
# Alpöge main line: a third batch of refined lemmas proved over Stdlib's reals (8 of a requested 12; 32/39 in total)

Requested: the next 12 refined lemmas, proved to the corpus's three-axiom
standard. **Delivered: 8.** Only 15 refined items remained. Of those, 7
cannot be proved within the allowlist with the Stdlib infrastructure
available (see below).

All 8 are proved over Stdlib's `R`. Every `Print Assumptions` is within
`docs/axiom-allowlist.txt`, and `scripts/audit_axioms.sh` is OK. **32 of the
39 refined items** are now proved over `R`.

External subject: mirror `CocoSgt/riemann-hypothesis-lean` @ `7cbf7a0`, read
from source; nothing was built.

## The eight (`docs/h1-vacuity/AlpogeRealsQED3.v`)

| Lean lemma | proof over `R` | inventory inputs (named hypotheses) |
|---|---|---|
| `landau_dichotomy` | ported from the `Q` rebuild (squared distances, finite list, decidable split over `ρ₀ :: F`) | `landau_finite` (as the covering list) |
| `landau_nearest` | ported likewise (avoidance of finitely many critical heights) | `landau_finite` |
| `landau_window` | the full case split. Real radii come from `sqrt` (no rational approximation needed), and the contradiction is the **exp-form** `landau_window_contra` | `landau_window_key` (in Lean's exp form), `landau_cauchy`, `landau_pole_asym` (×2), `landau_finite`, `landau_pole_re_le` |
| `landau_tails` | Lean's parameters `l = 2+6/δ`, `M`, `σ`, `k = ⌈(1+δ/2)σU⌉` (via `archimed`), with `landau_tails_pow` over `R` from batch 1 | `landau_tails_chernoff` |
| `landau_window_key` | the final arithmetic, with constant `2 + 2C₀\|C\|` | `landau_tails` (proved here), plus `WindowHypU`, `landau_window_ineq` and `landau_coeff` (as one input) |
| `proposition_size_bound` (GrowthSizeBound) | **Lean's `SizeWindows` written out over `R`** with the allowlist-clean `rpc`. It is reduced to the atom form, and the 120-line `nra` proof is ported from the `Q` rebuild. | none |
| `ch_core` | the threshold (`3 ≤ x`, `26 ≤ x^{3ε/8}` via `eventually_rpc_ge`), then `character_balance_core`, then `proposition_size_bound` | per-coset bounds (`th_le`, `ch_balance`, `ch_top`), `sum_Th`, `one_char` |
| `landau_pole_re_le_bound` | **from the Riemann sums themselves**, using `PoleData` and `LaplaceAt` from `AlpogeDeepStatements.v`. The steps are below the table. | none |

**How `landau_pole_re_le_bound` is proved.** With `q = e^{−ch}`, `c = σ − 2`
and step `h`:
1. `|Σ h f(jh)| ≤ C₀ h Σ q^j ≤ C₀ h/(1−q) ≤ C₀(1/c + h)`. This uses `tech3`
   and `exp ≥ 1 + x`.
2. `h → 0` (`inv_Sn_cv`), so the Riemann-sum limit is at most `C₀/c`
   (`lim_bound`).
3. The real and imaginary parts are each bounded by `C₀/c`, so
   `‖Φ s‖ ≤ 2C₀/(σ−2)`.

`AlpogeSkeleton.v : third_batch_proved_are_refined` checks by computation
that the eight are refined ledger items, and that all 32 proved over `R` are
distinct.

## Why the other 7 are not proved within the allowlist

| item | obstruction |
|---|---|
| `windowHyp_of_rpow` | needs `∫_Y^{Y^{1+δ}} dy/y = δ log Y`, an integral value |
| `windowHypU_of_windowHyp` | needs change of variables for integrals |
| `landau_window_ineq` | needs set-splitting (`(0,∞) = window ∪ tails`) and the triangle inequality for integrals |
| `kernel_integral` | needs the exact improper integral `∫₀^∞ u^k e^{−au}/k! = a^{−(k+1)}` (FTC / Gamma) |
| `landau_tails_chernoff` | needs set-splitting and set-monotonicity of improper integrals |
| `landau_coeff` | needs integrability of a constant multiple: `RiemannInt_P10` carries `classic` |
| `landau_cauchy` | needs the Cauchy integral formula and power-series coefficients |

**Root cause: the allowlist rules out Stdlib's integral theory.** Stdlib's
`RiemannInt` value and its integrability combinators (`RiemannInt_P10`)
carry `Classical_Prop.classic`. The definition used here (limits of uniform
Riemann sums) supports monotonicity and linearity of limits. It does not
directly support additivity over adjacent intervals, change of variables or
FTC.

**What it would take.** Proving these 7 would need an allowlist-clean
integration library: step-function integrals, Chasles, FTC for Lipschitz
integrands, and change of variables. That is a separate project.

## OUTCOME

**QED (8/8 delivered; 12 not reachable).** All within the three-axiom
standard; the audit is OK and there are no `Admitted`.

| status | count |
|---|---|
| refined (of 53) | 39 |
| proved over `R` | 32 |
| refined, blocked by the integral obstruction | 7 |
| unrefined | 14 (4 of them stated) |

The Alpöge verdict is unchanged: **PASS-STATIC / PENDING**.

**SUMMARY ok 8 / warn 1 (7 items need an allowlist-clean integral library) / bug 0.**
