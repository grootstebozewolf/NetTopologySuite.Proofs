<!-- doc-kind: finding
date: 2026-11-15
Provenance: c575ff389b37bf4b9e1cc0fc2dc08c82d6c17d5a
Theorems: `ClothoidResidual.v : clothoid_fprime_pos_branch`, `ClothoidFPrimeCore.v : clothoid_fprime_core_pos`, `ClothoidResidual.v : clothoid_residual_strictly_increasing_on_branch`, `ClothoidResidual.v : clothoid_residual_unique_root`, `RelateClothoid.v : clothoid_L_unique_on_branch`, `LipIntUnit.v : lint_ftc_eval`
Supersedes: docs/hypothesis-ledger-2026-11.md
Supersedes: docs/clothoid-open-questions-triage.md
-->
# Clothoid residual: the full branch |κL| ≤ π is unconditional (2026-11)

**Scope of the supersession.** Both superseded findings stand as written
except for what they say about `ClothoidFPrimePos`:

- [`hypothesis-ledger-2026-11.md`](hypothesis-ledger-2026-11.md), item 6:
  "only the full branch `|κL| ≤ π` (`ClothoidFPrimePos`) is open".
- [`clothoid-open-questions-triage.md`](clothoid-open-questions-triage.md):
  the Residual and Relate rows ("C on `ClothoidFPrimePos`", "on-branch C"),
  question 1 ("stays the named premise"), route (D) ("open") and open item 8.

**Question.** Is `ClothoidFPrimePos` — `0 < L`, `|κL| < π` ⇒ `0 < f'(L)`
for the chord residual `f(L) = L²(P² + Q²) − d²` — true, and provable on the
3-axiom R baseline without `MVT`, `Rolle`, `RiemannInt` or Coquelicot?

**Answer.** Yes. `ClothoidResidual.v : clothoid_fprime_pos_branch` proves it,
and the premise is removed from the four theorems that took it.

## What was wrong with the recorded route

The header of `ClothoidResidual.v` gave the intended discharge as "while the
total turning is below π, every tangent has a positive component along the
chord". That is not sufficient. With `v` the heading relative to the chord,
`f' > 0` is `∫ (cos v − v sin v) > 0` under `∫ sin v = 0`, and:

- a two-point heading distribution at `±β` gives `cos β − β sin β`, negative
  for `β > 0.87`;
- a monotone two-step weight on the window `[−1.09, 2.05]` gives `−0.23`.

Both satisfy the stated condition. A proof has to use that the heading is
quadratic in the parameter. Two further candidates were checked numerically
and rejected: the bound `I ≥ (1 − c) cos v₁ + c cos v₀` from sign matching
(reaches only `|κL| < π/2`), and `I ≥ cos(κL/2)` (false by `0.018` near
`k₀ = 0`, `κL ≈ 2.03`).

## The proof that landed

Unit parameter `x ∈ [0, 1]`, heading `u = p x + D x²/2`, `p = L k₀`,
`D = L (k₁ − k₀)`, total turning `W = p + D/2`. Centre on the midpoint:
`u = W/2 + b + e`, `b = W (x − 1/2)` odd and `e = D x (x − 1)/2` even about
`1/2`. With `A = ∫ cos b cos e`, `B = ∫ cos b sin e` and their `e`-weighted
versions `Ae`, `Be`:

1. `f'/(2L) = cos(W/2) · A + (A · Be − B · Ae)`, from two integrations by
   parts and the vanishing of four integrals odd about `1/2`.
2. On the branch `|b| < π/2` and `|e| < π/4`, so `A > 0` and `cos(W/2) > 0`.
3. `A · Be − B · Ae = ∫ cos b · (e − θ) · (n(e) − n(θ))` with `θ` the
   `cos b`-weighted mean of `e` and `n(y) = A sin y − B cos y` nondecreasing
   on `[−π/4, π/4]`; the integrand is pointwise nonnegative.

The circle (`D = 0`) gives `cos(W/2) · sin(W/2)/(W/2)`, zero at `|W| = π`:
the open bound is sharp, and the same identity holds on the larger region
`|W| < π`, `|D| < 4π`.

Stdlib `atan` (`atan_bound`, `tan_atan`) prints `Classical_Prop.classic`,
so the chord direction is not taken as an angle; `θ` is a weighted mean.

Support added in `LipIntUnit.v`: the second form of the fundamental theorem
for `lint` (`lint_ftc_eval`, from `lip_ftc` and `deriv_zero_const`) and
invariance under `x → 1 − x` (`uint_refl`). Neither existed.

## Evidence

- Toolchain: Rocq 9.2, Stdlib 9.2.0, Flocq 4.2.2. PR #1025, branch head at
  the Provenance commit.
- `Print Assumptions` on `clothoid_fprime_pos_branch`,
  `clothoid_fprime_core_pos`,
  `clothoid_residual_strictly_increasing_on_branch`,
  `clothoid_residual_unique_root` and `clothoid_L_unique_on_branch`:
  `sig_not_dec`, `sig_forall_dec`, `functional_extensionality_dep` only.
- Numerical cross-checks before formalising: 200,000 random `(k₀, k₁, L)`
  with `|κL| < π`, minimum of `f'/(2L)` `5.8e-5` (near the circle as
  `|κL| → π`); the identity in step 1 agrees with direct quadrature to
  `5e-12` on 400 samples.
- `check_admitted.sh`: 0 Admitted. `audit_axioms.sh` on a sequential build
  of the changed modules and their eight transitive dependents: OK.
- Not run locally: the full-corpus build and `check_ledger_assumptions.py`.

## Still open

Nothing on the R side of the residual. Halley's "≤ 4 iterations" stays
circular (item 5 of the superseded finding), and there is no binary64
Fresnel evaluator.

SUMMARY ok=5 warn=0 bug=1 — `ClothoidFPrimePos` proved on the full open branch; four headline theorems lose the premise; one recorded proof route (tangent-along-chord) was insufficient and is replaced.
