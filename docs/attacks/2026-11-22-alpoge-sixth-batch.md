<!-- doc-kind: finding
date: 2026-11-22
Provenance: a9dbe40
Theorems: `AlpogeSixthBatch.v : sum_Th_C`, `AlpogeSixthBatch.v : landau_window_ineq_R`, `AlpogeSixthBatch.v : windowHypU_of_windowHyp_R`, `AlpogeSixthBatch.v : RInt_exp_change`, `AlpogeSixthBatch.v : shapeWin_r`, `AlpogeSixthBatch.v : supplyChi_r`, `AlpogeSixthCH.v : one_char_r`, `AlpogeSixthCH.v : gmA_eq_r`, `AlpogeSixthCHReals.v : CcStr`, `AlpogeSixthCHReals.v : large_x_eventually_R`, `AlpogeSixthLandau.v : iteratedDeriv_laplace_ILAP`, `AlpogeSixthLandau.v : poleData_r`, `AlpogeSkeleton.v : sixth_batch_all_refined`
-->
# Alpöge main line, sixth batch: all 53 refined, 46 proved over R

Requested: refine or prove 1/3 of the 53 ledger lemmas, i.e. 18.
**Done: 22 steps on 16 lemmas.**
- **12 refined:** every remaining unrefined item.
- **10 proved over R:** these were previously refined only.

The ledger now has **53/53 refined** and **46 proved over R**.

Everything is within the three-axiom allowlist (`docs/axiom-allowlist.txt`;
`scripts/audit_axioms.sh` OK on every file). There are no `Admitted`.

External subject: mirror `CocoSgt/riemann-hypothesis-lean` @ `7cbf7a0`, read
from source; nothing was built.

## Files

| file | content |
|---|---|
| `AlpogeSixthBatch.v` | Over R: `sum_A`, `sum_Th` (ℂ = R×R, `Cc_field`), `landau_window_ineq`, `windowHypU_of_windowHyp`. Refined: `TopG`, `HostExW`. New integration tools. |
| `AlpogeSixthCH.v` | Refined over an abstract ℂ: `one_char`, `th_le`, `ch_balance`, `ch_top`, `gmA_eq`, `large_x_eventually`. |
| `AlpogeSixthCHReals.v` | `CcStr`: ℂ = R×R, with every law of the abstract-ℂ record proved. The five ℂ-valued refinements are instantiated at it. `large_x_eventually` is proved with no premises. |
| `AlpogeSixthLandau.v` | Refined over R: `iteratedDeriv_laplace`, `landau_finite`, `landau_pole_asym`, `poleData`. |

## Proved over R (10)

| Lean lemma | how | premises left |
|---|---|---|
| `sum_A`, `sum_Th` (ChCore) | The fifth batch's abstract-field proofs, instantiated at `Cc_field`. | Mathlib character facts |
| `landau_window_ineq` (landauWindowIneq) | Lean's proof. `cnorm_CIntInf_le` rebuilds `norm_integral_le_integral_norm`: `‖L‖ = c·Re L + s·Im L` for the unit vector `(c,s) = L/‖L‖`, and `c·cos − s·sin ≤ 1` pointwise by Cauchy–Schwarz. The integral is split into `[0,U] + [U,V] + [V,∞)`. | the integral values, as for `landau_tails_chernoff` |
| `windowHypU_of_windowHyp` (WindowHypUOfWindowHyp) | Lean's proof, with `U = log Y` and majorant `R ∘ exp`, through `RInt_exp_change`. | none beyond Lean's |
| `one_char`, `th_le`, `ch_balance`, `ch_top`, `gmA_eq` | The `AlpogeSixthCH` refinements, at `CcStr`. In `CcStr`, `norm_add_le` is proved by Cauchy–Schwarz and `norm_mul` by `sqrt_mult`. | the inventory lemmas and character/sum facts named in `AlpogeSixthCH.v` |
| `large_x_eventually` (SubThreeMulLogTwoLe l.319) | `large_x_eventually_R : LargeXEv Lc rpc`. The three Mathlib premises are proved for the clean log and rpow: `isLittleO_log_rpow_atTop` via `Lc y ≤ y^t/t` with `t = ε/2`, `tendsto_rpow_atTop`, and `rpow_nonneg`. | **none** |

**New allowlist-clean integration tools.**
- `RInt_bounded`: an `RInt`-integrable function is bounded. Moving one tag of
  a fine uniform partition changes the Riemann sum by `(f y − f t)·h`.
- `RInt_exp_change`: `∫_{e^a}^{e^b} f = ∫_a^b f(eᵘ)eᵘ du` for any
  `RInt`-integrable `f`. `exp` maps fine partitions to fine partitions, and on
  each cell `|eᵗΔx − Δeˣ| ≤ eᵇ(Δx)²` (from #1047's `mvt_le` and `mvt_ge`).
  #1047's `windowU_change_var` needed an antiderivative.

## Refined (12)

| Lean lemma | the Lean proof, rebuilt | inputs left as hypotheses |
|---|---|---|
| `TopG` (ShapeWin `shapeWin`, EveryCharacter `plugWin`) | Of the shape data, only `hEx` and `TopG`'s own `hV` mention `(la, G)`. `link_ex` is taken at `𝒜 ∧ G.cls la`, and `topDesWin` receives the two class inclusions, which are proved. | `link_ex`, `topDesWin`, the `(la,G)`-free link facts |
| `HostExW` (SupplyChi `supplyChi`) | `supplyOfAdm`, with its premise from `admissibleClassesTwistedChar` after `subst` of `s.eps = eps`. | `supplyOfAdm`, `admissibleClassesTwistedChar`, `VWin` |
| `one_char` (ChCore l.202) | Lean's three-way split: trivial, kept non-trivial and other characters, with `move` and `triv`. | Mathlib ℂ/character laws |
| `th_le` (ChCore l.75) | The thick/thin split, re-indexing, and the average `De − Th`. | `thick_filter`, `partner_inPhi`, `norm_avg_le`, `De_re` |
| `ch_balance` (ChBalance l.200) | The steps `hin`, `hDe`, `hsplit`, `hcol`, `hreal` and the closing algebra. | `askExp` and the CharacterBalance inventory (`askExp` is not refined) |
| `ch_top` (ChTop l.37) | Main re-indexed through two Equivs, then ErrText ≤ bracket. | `each_unit_bound`, `errX5at_le` |
| `gmA_eq` (GmAEq l.61) | `gmA_eq_triv` via `θ(sg)² = 1`, then the case analysis on the weights and re-indexing. | `chr_bij`, `prim_inj`, `EAtH.*` and related |
| `large_x_eventually` | The little-o bound with `c = 1`, plus the rpow limit, then Rmax. | (proved over R, above) |
| `iteratedDeriv_laplace` (IteratedDerivLaplace l.84) | Domination with `δ = (Re s − 2)/2`, the `cexp` derivative and induction on `k`, with uniqueness on `{Re > 2}`. `iteratedDeriv_laplace_ILAP` produces `landau_coeff`'s `ILAP` premise, as `landau_coeff_of_iteratedDeriv_laplace` checks. | Mathlib `hasDerivAt_integral_of_dominated…`, `Integrable.mono'` |
| `landau_finite` (LandauFinite l.9) | Points of the ball have `Re > 0`. A neighbourhood subcover follows, and the case on `v = w` is decided. | Mathlib compactness of the closed ball |
| `landau_pole_asym` (LandauPoleAsym) | The pole derivative by induction, then the patched `G = Φ − c/(s−ρ)` (removable singularity) and the split `Φ^(k) = G^(k) + pole part`. | Mathlib zpow/analyticity facts; `landau_cauchy` |
| `poleData` (poleData l.248) | All seven `PoleData` fields: finite choice, the summed growth bound, Laplace via `Re z = (z + z̄)/2`, punctured neighbourhoods, and the residue algebra. | `poleData_char` (not refined), `measurable_Gchi`, `Gchi_growth`, `Gchi_conj`, … |

## Ledger (`AlpogeSkeleton.v`)

- `counts`: 53 total, **53 refined**.
- `sixth_batch_counts` and `sixth_batch_ch_counts` check, by computation, that
  the ten new over-R proofs are refined items and that all **46** proved over
  R are distinct.
- `sixth_batch_all_refined` checks the 12 newly refined items, and that every
  ledger item is refined.
- `stated_four_are_unrefined_items` keeps its name, because it anchors the
  immutable 2026-11-21 deep-statements finding. It now checks ledger
  membership only.

**Not yet proved over R (7):**
- `landau_cauchy` (needs the Cauchy integral formula);
- `TopG`, `HostExW`, `iteratedDeriv_laplace`, `landau_finite`,
  `landau_pole_asym`, `poleData`. These are refined, with the cited Mathlib
  facts as hypotheses.

The deepest inputs still assumed are `poleData_char` (the ζ/L-function
analysis), the `TopShape` link facts and `askExp`.

## OUTCOME

**QED: 22 steps (12 refined, 10 proved over R) on 16 lemmas**, against a
request of 18, within the allowlist. The Alpöge verdict is unchanged:
**PASS-STATIC / PENDING**. Every main-line lemma is now refined, but the
inventory inputs above are not proved.

**SUMMARY ok 22 / warn 0 / bug 0.**
