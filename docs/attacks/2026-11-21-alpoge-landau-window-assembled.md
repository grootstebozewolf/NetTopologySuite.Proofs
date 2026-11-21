<!-- doc-kind: finding
date: 2026-11-21
Provenance: c8a481a
Theorems: `LandauWindowRebuilt.v : landau_window_rebuilt`, `LandauWindowRebuilt.v : sqrt_gap`, `LandauWindowRebuilt.v : landau_window_hyps_consistent`
-->
# Alpöge main line: `landau_window` assembled end to end in Rocq

Follows `2026-11-21-alpoge-landau-dichotomy-qed.md`. That slice and the sign
correction checked the separate pieces of `landau_window`:
- `window_contra`;
- `real_pole_residue_pos`;
- `window_ineq_discrete`;
- `dichotomy_rebuilt`;
- `nearest_rebuilt`.

This rung composes them into **the theorem itself**, following the glue of
`landauWindow.lean`, lines 83–168. External subject: mirror
`CocoSgt/riemann-hypothesis-lean` @ `7cbf7a0`, read from source; nothing
was built.

## Statement

`docs/h1-vacuity/LandauWindowRebuilt.v : landau_window_rebuilt` (Stdlib,
`Q`) is *Closed under the global context*. It assumes `0 < θ < σ` and proves
**`∀ ρ ∈ Z, Re ρ ≤ θ`**, the conclusion of Lean's `landau_window`, from these
named hypotheses:

| hypothesis | Lean source | content |
|---|---|---|
| `Hle` | `landau_pole_re_le` (with `2 < σ`) | every pole has `Re ρ < σ` |
| `LF` | `landau_finite` | `Z` is finite on every box in `Re s > 0` |
| `HA` | definition | `A k γ = ‖(−1)^k Φ^{(k)}(σ+iγ)/k!‖ ≥ 0` |
| `KEY` | `landau_window_key` | `(A k γ + B k)·(σ−θ)^k ≤ C·s^k` for arbitrarily large `k`, at every rate `s ≥ 1`. This is `e^{ηU} ≤ s^k` for `U ≤ k`, as in `LandauWindowCore.v`. |
| `CAUCHY` | `landau_cauchy` | on a pole-free disc about `σ`: `B k ≥ −M/e^k` |
| `POLE1` | `landau_pole_asym` (norm) | at an isolated pole of `σ+iγ`: `A k γ ≥ cn/d'^k − M/e^k` with **`cn > 0`** |
| `POLE2` | `landau_pole_asym` (real part) plus `PoleData`'s real-pole clause | at an isolated real pole `β`: `B k ≥ cr/(σ−β)^k − M/e^k` with **`cr > 0`** |

**Glue, as in Lean:**
1. Case split with `dichotomy_rebuilt`. In the left branch, find the unique
   nearest pole with `nearest_rebuilt`.
2. Pick radii `d' < e` strictly between the pole distance and the isolation
   radius.
3. Pick a rate `s` with `s·d' < e`.
4. Combine the bounds (`glue_complex` / `glue_real`) and close with
   `window_contra`.

**One new elementary lemma, `sqrt_gap`.** For `0 ≤ a < b` there is a
rational `q` with `a < q² < b`; the proof is a grid search, with no axioms.
Lean's radii (`d = ‖z − ρ‖`, `r`, `D`) are real, while `window_contra` needs
rational radii. `sqrt_gap` supplies them, which is what makes the
squared-distance encoding of the previous slice composable. In Lean the
same choice is `e = (d + r)/2`.

**Consistency.** `landau_window_hyps_consistent` shows the hypothesis set is
not contradictory: an empty `Z` with zero coefficients satisfies it. That is
a consistency witness only. It is **not** evidence that the hypotheses hold
for `Φ = Laplace(Gm)`.

## What the assembly confirms

- **The residue sign is used once, in `POLE2`.** Only the real-nearest-pole
  branch needs `cr > 0`. `POLE1` needs only `cn > 0`, i.e. `c ≠ 0`. The
  assembled proof goes through with exactly these hypothesis shapes, which
  machine-checks the previous slice's reading.
- **The window majorant enters only through `KEY`.** Its pointwise core,
  `|g| + g ≤ 2R`, is `window_ineq_discrete`.
- **No excluded middle.** The `Re ρ₀ > θ` contradiction is decided with
  `Qlt_le_dec`, and the case split is decided over the finite list.

## Not re-proved (analytic translations)

- **`KEY`:**
  - the Laplace integrals behind it;
  - `landau_kernel_max`;
  - `landau_tails`;
  - the passage from `e^{ηU}` to `s^k`.
- **`CAUCHY`:** Cauchy's estimate.
- **`POLE1`, `POLE2`:**
  - the pole asymptotics (`landau_pole_asym`);
  - the monotonicity step `‖c‖/d^{k+1} ≥ (‖c‖/d')/d'^k` for `d ≤ d'`.
- **`LF`:** isolated zeros imply finiteness on compacts.
- **`PoleData` itself:** `poleData.lean`, i.e. the Laplace transform of `Gm`
  is meromorphic, with poles at the zeros and residues given by the
  multiplicities.

## OUTCOME

**QED.** Lean's `landau_window` is rebuilt as one Rocq theorem with zero
axioms, conditional on the seven named analytic inputs above.

**Where this sits on the main line.** `level_of_tiedWin_rebuilt` consumes
`FormBAt` as a hypothesis, and `ch_core_rebuilt` supplies the √X window
bound. This rung now covers the step inside `formB`, i.e. `landau_window`.
One link is still **not assembled**: the rest of `formB`
(`zeroFree_of_rpow_window`, `lemmaL`, `WindowHypUOfWindowHyp`,
`WindowHypOfRpow`). That link turns `HasWindows {Gm ≤ x^θ}` into
`WindowHypU` and the zeros into `PoleData` poles. So the skeleton is checked
piecewise, not yet as a single composed Rocq theorem.

The audit verdict is unchanged: **PASS-STATIC / PENDING** (no Lean build,
no `#print axioms`, analytic inputs not re-proved).

**SUMMARY ok 3 / warn 0 / bug 0.**
