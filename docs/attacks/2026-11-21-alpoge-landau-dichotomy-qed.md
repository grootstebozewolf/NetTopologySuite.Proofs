<!-- doc-kind: finding
date: 2026-11-21
Provenance: dd86816
Theorems: `LandauDichotomyQED.v : window_ineq_discrete`, `LandauDichotomyQED.v : on_axis`, `LandauDichotomyQED.v : dichotomy_rebuilt`, `LandauDichotomyQED.v : nearest_equi`, `LandauDichotomyQED.v : nearest_rebuilt`
-->
# Alpöge main line: `landau_window`'s case split and majorant inequality, rebuilt

Follows `2026-11-21-alpoge-main-line-sign-correction.md`, which located the
main line's sign step in `landau_window` and machine-checked its final
contradiction (`LandauWindowCore.v : window_contra`) and the real-pole residue
sign (`real_pole_residue_pos`). This slice rebuilds the two remaining pieces
of `landau_window`: the case split on where the nearest pole is, and the
majorant inequality. External subject: mirror
`CocoSgt/riemann-hypothesis-lean` @ `7cbf7a0`, read from source
(`…/DedekindLFunctions/LandauTheorems/`); nothing was built.

## How `landau_window` uses its inputs (read from source)

`landau_window` (`landauWindow.lean`, lines 83–168) assumes a pole `ρ₀` with
`Re ρ₀ > θ` and calls `landau_dichotomy`:

1. **Left branch.** Some pole is nearer to the line `Re s = σ` than the
   pole-free disc around `σ` is wide. `landau_nearest` then picks `γ` so that
   `σ + iγ` has a *unique* nearest pole `ρ` (residue `c ≠ 0`). The
   contradiction uses:
   - the **norm** of the k-th Taylor coefficient at `σ + iγ`, which is at
     least `‖c‖/d^{k+1} − M/e^k` (`landau_pole_asym`);
   - the **real part** at `σ`, bounded *two-sidedly* by `M'/e^k` through
     Cauchy's estimate on the pole-free disc (`landau_cauchy`).
2. **Right branch.** The nearest pole to `σ` is **real**, some
   `β ∈ (θ, σ)` alone in a disc. The contradiction uses the real part at `σ`,
   which is at least `Re c/(σ − β)^{k+1} − M/e^k` with **`Re c > 0`**
   (`PoleData`'s real-pole clause), together with norm `≥ 0`.

In both branches the upper bound is `landau_window_key`. That comes from
`landau_window_ineq`, whose only use of the window majorant is the pointwise
inequality `|g| + g ≤ 2R` (from `g ≤ R`, `0 ≤ R`). That inequality bounds
**norm at `σ + iγ` plus real part at `σ`**, never the norm alone.

**Consequence.** The positive real-pole residue, `S·(−1/(ρ(ρ−1))) > 0` from
`poleData`, is consumed **only in the right branch**, where the nearest pole
is real. The left branch needs no residue sign, only `c ≠ 0`. This is the
shape of Landau's classical theorem: a one-sided bound forces a singularity
on the real axis. It sharpens the correction finding's three-part
description of the sign.

## Rocq (`docs/h1-vacuity/LandauDichotomyQED.v`, Stdlib over `Q`)

The five results below are *Closed under the global context*.

| theorem | mirrors | OUTCOME |
|---|---|---|
| `abs_add_le_twice`, `window_ineq_discrete` | `landau_window_ineq`. With finite sums for integrals, window entries `g ≤ R`, `R ≥ 0`, `w ≤ K·v` (with `K = 1/(σ−θ)^k`), and tail entries `\|g\|w ≤ C₀h`: `Σ\|g\|w ≤ 2K·Σ_win R v − Σ g w + 2C₀·Σ_tail h`. | **QED** |
| `on_axis` | `eq_ofReal_sub_of_dist_le_of_le_sub_re`: `\|w − σ\| ≤ D ≤ σ − Re w` forces `w = σ − D` on the real axis | **QED** |
| `dichotomy_rebuilt` | `landau_dichotomy`, both branches with the same bounds (`D ≤ σ−θ`; `σ−β < r ≤ σ−θ`; `θ < β`; uniqueness in the disc) | **QED** |
| `nearest_equi` | `landau_nearest_equi`: equidistance from `σ + iγ` forces `a = b` unless `γ` is the pair's critical value | **QED** |
| `nearest_rebuilt` | `landau_nearest`: some `σ + iγ` has a unique nearest pole, alone in a disc of radius `≤ D` | **QED** |

**Translations (not re-proved):**
- Distances are squared (`d2`), so radii `D`, `r` appear as `D²`, `r²`. Every
  comparison involved is between nonnegative quantities, so the squared
  statements are equivalent.
- Local finiteness of `Z` (`landau_finite`, from isolated zeros) is a
  hypothesis: a list `F` covering `Z` on a compact region. For
  `landau_nearest` that region is the box `[σ−D, σ] × [Im ρ₁ − 2D, Im ρ₁ + 2D]`.
  The box contains Lean's `closedBall (σ + i Im ρ₁) (D + ε)`, lies in
  `Re s > 0`, and avoids square roots in the triangle inequality.
- For `landau_window_ineq`: the triangle inequality for the complex Laplace
  integral, the split of `Ioi 0` into window and tail, and
  `landau_kernel_max` (`u^k e^{−(σ−θ)u}/k! ≤ (σ−θ)^{−k}`).

## Two observations from the rebuild

- **The case split needs no excluded middle.** `landau_dichotomy` applies
  classical `by_cases` to `∃ ρ₁ ∈ Z, σ − Re ρ₁ < d`, an existential over the
  infinite set `Z`. The proof only ever uses that split on `ρ₀` and on the
  members of the finite set `F`. `dichotomy_rebuilt` therefore decides it
  over the list `ρ₀ :: F` (`split_list`). This is harmless in Lean, since
  classical logic is inside its three-axiom budget, but it shows the step is
  constructive.
- **Lean's division by zero is harmless in `landau_nearest`.** The set of
  excluded `γ` values is the image of `F × F` under
  `N/(2(Im a − Im b))`. When `Im a = Im b`, Lean's `x/0 = 0` makes the
  condition read `γ ≠ 0`. `nearest_equi` states the condition only when
  `Im a ≠ Im b` and still proves `a = b`: two equidistant points with equal
  imaginary parts and real parts below `σ` coincide whatever `γ` is. So the
  extra exclusion of `γ = 0` costs nothing and hides no case.

## OUTCOME

**QED.** `landau_window` now has its elementary content machine-checked end
to end, inside the three-axiom budget (no axioms used):
- the case split (`dichotomy_rebuilt`, `nearest_rebuilt`);
- the majorant inequality (`window_ineq_discrete`);
- the contradiction (`window_contra`);
- the residue sign (`real_pole_residue_pos`).

The analytic translations listed above stay unverified: Cauchy estimates,
pole asymptotics, Laplace integrals, and local finiteness of zeros. The audit
verdict is unchanged: **PASS-STATIC / PENDING** (no Lean build, no
`#print axioms`).

**SUMMARY ok 5 / warn 0 / bug 0.**
