<!-- doc-kind: finding
date: 2026-11-21
Provenance: cd85d90
Theorems: `AlpogeSkeleton.v : two_thirds_refined`, `AlpogeSkeleton.v : counts`, `AlpogeRefineBatch.v : landau_tails_chernoff_r`, `AlpogeRefineBatch.v : windowHypU_of_windowHyp_r`, `AlpogeRefineBatch.v : landau_pole_re_le_r`, `AlpogeRefineBatch.v : sigA_le_r`
-->
# Alpöge main line: a Rocq skeleton, refined to 39/53 (stop condition 2/3 met)

Requested: start with a skeleton in Rocq, and refine until 2/3 of all lemmas
are refined. **Reached: 39 of 53 lemmas refined (73.6%).**
`AlpogeSkeleton.v : two_thirds_refined` checks `2·53 ≤ 3·39` by computation.

External subject: mirror `CocoSgt/riemann-hypothesis-lean` @ `7cbf7a0`, read
from source; nothing was built.

## The skeleton

`docs/h1-vacuity/AlpogeSkeleton.v` imports every Alpöge probe. It holds:
- **The skeleton theorem:** `CoreSliceQED.v : main_line_from_core`, which
  gives ZeroFreeAbove (1/2) from named inputs.
- **A ledger:** the 53 main-line Lean lemmas, each with its Rocq witness or
  `-`, and a refined flag.
- **A `Check` of every cited witness,** so the ledger cannot cite a theorem
  that does not exist.
- **`counts`** (53 total, 39 refined) and **`two_thirds_refined`**, both
  computed. They are *Closed under the global context*.

**The refinement criterion.** A lemma counts as refined when the Lean proof's
own reasoning is rebuilt in Rocq with zero axioms. Its remaining inputs may
be only:
- standard Mathlib facts, named as hypotheses; or
- other inventory lemmas.

Instance checks do not count; `sum_A` and `sum_Th` stay unrefined despite
`CoreSliceQED.v`.

**Granularity, the main caveat.** Each lemma that was read is one item. Each
subtree that was not expanded is also one item, however large:
- `TopG` (via `shapeWin` from `GLq.Green`);
- `HostExW`;
- `one_char`, `th_le`, `ch_balance`, `ch_top`;
- `gmA_eq`;
- `poleData`.

So **2/3 by count is not 2/3 by mathematical content.** The unrefined 14
items contain essentially all of the development's deep mathematics. The
refined 39 are its logical and analytic scaffolding.

## This slice: 16 lemmas refined (`AlpogeRefineBatch.v`)

All 16 are *Closed under the global context*.

| Lean lemma (file) | Rocq | Mathlib inputs named |
|---|---|---|
| `hypV_of_cls`, `eFamC_of_cls` (ZeroFreeAllOfTopG) | `hypV_of_cls_r`, `eFamC_of_cls_r` | none (repackaging; `C = 4`) |
| `tiedCore_of_chainTied` (LevelGmLeOnFamilyScales) | `tiedCore_of_chainTied_r` | none (extensional `TT` identification) |
| `sigA_le` (SigALe) | `sigA_le_r`, `sq_one_cases` (the `chr_bounded` ±1 split) | `mul_self_eq_one_iff`, `card_PsiA` |
| `level_family` (LevelFamily) | `level_family_sum`, `level_family_zerofree` | none |
| `windowHyp_of_rpow_eventually` | `windowHyp_of_rpow_eventually_r` | `log_le_rpow_div`, `rpow_add`, `tendsto_rpow_atTop` |
| `windowHypU_of_windowHyp` | `windowHypU_of_windowHyp_r` (window membership, integrand identity) | `exp_le_exp`, `exp_log`, `rpow_def_of_pos`, change of variables |
| `charFamily_LFunction_ne_zero_of_one_le_re` | `charFamily_ne_zero_r` | `LFunction_modOne_eq`, `riemannZeta_ne_zero_of_one_le_re`, `LFunction_ne_zero_of_one_le_re` |
| `landau_kernel_max` | `landau_kernel_max_r` | `pow_div_factorial_le_exp`, `exp_add` |
| `kernel_integral` | `kernel_integral_r` | Gamma integral, `Gamma_nat_eq_factorial` |
| `landau_tails_chernoff` | `landau_tails_chernoff_r` (pointwise split, integral monotonicity in both integrand and set, linearity) | `exp_le_exp`, `exp_add`, `exp_pos`, `setIntegral_mono_on` / `_set` |
| `landau_coeff` | `landau_coeff_sign_r` (`(−1)^k(−u)^k = u^k`) | none (given `iteratedDeriv_laplace`) |
| `landau_cauchy` | `landau_cauchy_r` | `norm_cauchyPowerSeries_le`, `le_opNorm` |
| `landau_pole_re_le_bound` | `landau_pole_re_le_bound_r` (pointwise) | `exp_le_exp`, `exp_add`, `norm_integral_le_of_norm_le` |
| `landau_pole_re_le` | `landau_pole_re_le_r`, `pole_residue_zero_r` (the limit argument as an Archimedean step) | `tendsto_nhds_unique` |
| `landau_window_re_pos` | `landau_window_re_pos_r` | `abs_re_le_norm` |

**Thin items, stated plainly.** Five refinements are thin because the Lean
proofs are themselves bookkeeping:
- `hypV_of_cls`;
- `eFamC_of_cls`;
- `tiedCore_of_chainTied`;
- `kernel_integral`;
- `landau_cauchy`.

## The 14 unrefined lemmas

| Item | Reason or partial evidence |
|---|---|
| `TopG` | deep: family-connectedness of host classes |
| `HostExW` | not expanded |
| `large_x_eventually` | 614-line file, not read |
| `gmA_eq` | not refined |
| `sum_Th` | instance-checked only |
| `sum_A` | instance-checked only |
| `one_char` | not refined |
| `th_le` | inside a 17,981-line file |
| `ch_balance` | the explicit formula |
| `ch_top` | not refined |
| `poleData` | core only: `real_pole_residue_pos` |
| `iteratedDeriv_laplace` | not refined |
| `landau_finite` | compactness |
| `landau_pole_asym` | not refined |

## OUTCOME

**Stop condition met:** 39/53 refined (≥ 2/3), machine-counted in Rocq. No
lemma was found false. The audit verdict is unchanged: **PASS-STATIC /
PENDING**. The refined fraction measures scaffolding coverage, not
correctness of the deep inputs listed above.

**SUMMARY ok 16 / warn 1 (2/3 by item count, not by content) / bug 0.**
