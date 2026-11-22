<!-- doc-kind: finding
date: 2026-11-21
Provenance: 7707c1f
Theorems: `AlpogeRealsQED.v : landau_growth_contra`, `AlpogeRealsQED.v : landau_window_contra`, `AlpogeRealsQED.v : landau_kernel_max`, `AlpogeRealsQED.v : landau_tails_pow`, `AlpogeRealsQED.v : add_one_le_exp`, `AlpogeRealsQED.v : exp_upper`, `AlpogeSkeleton.v : twelve_proved_are_refined`
-->
# Alpöge main line: 12 refined lemmas proved over Stdlib's reals (three-axiom allowlist)

Requested: take 12 of the 39 refined lemmas and prove them to this corpus's
standard, with only the three allowed axioms. **Done: 12/12.** All are proved
over Stdlib's `R`, with Stdlib's `exp` and `sqrt`. There are no abstract
operations and no "Mathlib fact" hypotheses. Every `Print Assumptions` is a
subset of `docs/axiom-allowlist.txt`:
- `ClassicalDedekindReals.sig_not_dec`
- `ClassicalDedekindReals.sig_forall_dec`
- `FunctionalExtensionality.functional_extensionality_dep`

`scripts/audit_axioms.sh` passes on the file's build log.

External subject: mirror `CocoSgt/riemann-hypothesis-lean` @ `7cbf7a0`, read
from source; nothing was built.

## The twelve (`docs/h1-vacuity/AlpogeRealsQED.v`)

Each theorem is the Lean lemma itself, up to representation:
- ℂ appears as pairs of reals, with `sqrt` distance;
- Finset sums appear as list sums;
- the development's abstract parameters appear as section variables, as in
  Lean.

The premises are exactly the Lean premises.

| # | Lean lemma (file) | axioms used |
|---|---|---|
| 1 | `landau_growth_contra` (LandauGrowthContra) | all 3 |
| 2 | `landau_window_contra` (landauWindow) | all 3 |
| 3 | `landau_kernel_max` (LandauKernelMax) | all 3 |
| 4 | `landau_tails_pow` (landauTails) | all 3 |
| 5 | `eFamC_of_cls` (ZeroFreeAllOfTopG) | `sig_forall_dec`, `fun_ext` |
| 6 | `landau_window_re_pos` (landauWindow) | all 3 |
| 7 | `eq_ofReal_sub_of_dist_le_of_le_sub_re` (LandauDichotomy) | all 3 |
| 8 | `landau_nearest_equi` (LandauNearest) | all 3 |
| 9 | `exists_small_eps` (TopWin) | `sig_forall_dec`, `fun_ext` |
| 10 | `level_family`: `wt_pos`, the Gm sum, the ZeroFree iff (LevelFamily) | `sig_forall_dec` (+ `fun_ext`) |
| 11 | `sigA_le`, with `chr_bounded`'s ±1 split (SigALe) | `sig_forall_dec`, `fun_ext` |
| 12 | `hypV_of_cls` (ZeroFreeAllOfTopG) | `sig_forall_dec`, `fun_ext` |

`AlpogeSkeleton.v : twelve_proved_are_refined` checks by computation that
each of the twelve is a refined item of the 53-item ledger, and that they are
distinct.

## Finding: Stdlib's `ln` / `Rpower` are outside the allowlist

`Print Assumptions` shows that the following all carry
**`Classical_Prop.classic`**, which is not allowlisted:
- `ln` (through `ln_exists`), and with it `Rpower`;
- `exp_increasing`;
- `exp_ineq1_le`, `exp_ln`, `ln_exp`, `Rpower_plus`, `Rle_Rpower`.

The first draft of this file used them and failed the standard. As a result:

- **exp facts re-derived inside the allowlist.** These come from Stdlib's
  series `E1 x N → exp x` (`E1_cvg`), `growing_ineq` and `Rle_cv_lim`:
  - `exp_le_mono` and `exp_lt_mono`;
  - `add_one_le_exp` (`1 + x ≤ exp x` for **every** real `x`);
  - `exp_upper` (`(1−y)·exp y ≤ 1`, from the partial-sum invariant
    `(1−y)E1 y N + y^{N+1}/N! ≤ 1`);
  - `pow_div_fact_le_exp` (`x^k/k! ≤ exp x`).
- **`landau_growth_contra` without `ln`.** Lean takes `η = log(e/d)/2`. The
  statement only asserts that some `η > 0` works, so here
  `η = (1 − d/e)/2`, with `exp(2η) ≤ e/d` from `exp_upper`.
  - This also discharges the step "`e^{ηU} ≤ s^k`" that
    `LandauWindowCore.v` left as a translation.
  - `landau_window_contra` then holds in Lean's exact form, with
    `exp (η·U)`.
- **Lemmas whose statements mention `Real.log` or `rpow` were not chosen.**
  These are `windowHyp_of_rpow_eventually`, `level_of_tiedWin` (it uses
  `x^θ`) and the `windowHypU_of_windowHyp` auxiliaries. They cannot be
  stated over Stdlib's `ln` within the allowlist without first building an
  allowlist-clean logarithm, which was not done.

## OUTCOME

**QED (12/12)**, within the corpus's three-axiom standard. The axiom audit
passes and there are no `Admitted`. The finding about Stdlib's `ln` / `Rpower`
applies to the corpus generally: any future module that uses them leaks
`Classical_Prop.classic`.

The Alpöge audit verdict is unchanged: **PASS-STATIC / PENDING**.

**SUMMARY ok 12 / warn 1 (Stdlib ln/Rpower/exp_increasing carry classic) / bug 0.**
