<!-- doc-kind: finding
date: 2026-11-22
Provenance: 998bed3
Theorems: `AlpogeSixthBatch.v : sum_A_trivial_C`, `AlpogeSixthBatch.v : sum_Th_C`, `AlpogeSixthBatch.v : landau_window_ineq_R`, `AlpogeSixthBatch.v : windowHypU_of_windowHyp_R`, `AlpogeSixthBatch.v : RInt_exp_change`, `AlpogeSixthBatch.v : shapeWin_r`, `AlpogeSixthBatch.v : supplyChi_r`, `AlpogeSkeleton.v : sixth_batch_counts`
-->
# Alpöge main line, sixth batch: refine or prove a third of 53 (in progress: 43/53 refined, 40 proved)

Requested: refine or prove 1/3 of the 53 ledger lemmas (18). This finding
records the batch as it lands. It covers this file's 6 items; the remaining
refinements are in flight.

Everything is within the three-axiom allowlist (`docs/axiom-allowlist.txt`;
`scripts/audit_axioms.sh` OK).

External subject: mirror `CocoSgt/riemann-hypothesis-lean` @ `7cbf7a0`, read
from source; nothing was built.

## Proved over R (`docs/h1-vacuity/AlpogeSixthBatch.v`)

| Lean lemma | how | premises |
|---|---|---|
| `sum_A`, `sum_Th` (ChCore.lean) | `Cc_field`: ℂ = R×R is a field, so the abstract-field refinements of `AlpogeFifthBatch.v` instantiate at ℂ (`sum_A_trivial_C`, `sum_A_nontrivial_C`, `sum_Th_C`). | the Mathlib character facts, as before |
| `landau_window_ineq` (landauWindowIneq.lean) | Lean's proof over R. `cnorm_CIntInf_le` rebuilds `norm_integral_le_integral_norm`: `‖L‖ = c·Re L + s·Im L` for the unit vector `(c,s) = L/‖L‖`, and `c·cos − s·sin ≤ 1` pointwise (Cauchy–Schwarz). The split of `(0,∞)` is `[0,U] + [U,V] + [V,∞)` (`RInt_chasles`, `RIntInf_chasles`, boundedness from `hC`). | the integral values (as for `landau_tails_chernoff`) |
| `windowHypU_of_windowHyp` (WindowHypUOfWindowHyp.lean) | Lean's proof over R, with `U = log Y` and majorant `R ∘ exp`. The change of variables needs no antiderivative (below). | none beyond Lean's |

**New allowlist-clean integration tools.**
- `RInt_bounded`: an `RInt`-integrable function is bounded. One tag of a fine
  uniform partition is moved, which changes the Riemann sum by `(f y − f t)·h`.
- `RInt_exp_change`: `∫_{e^a}^{e^b} f = ∫_a^b f(e^u) e^u du` for any
  `RInt`-integrable `f`. `exp` maps fine partitions to fine partitions, and on
  each cell `|e^t Δx − Δe^x| ≤ e^b (Δx)²` (from #1047's one-sided `mvt_le` /
  `mvt_ge`). #1047's `windowU_change_var` needed an antiderivative.

## Refined from the Lean proof (inventory lemmas as hypotheses)

| Lean lemma | the Lean proof, rebuilt | inventory inputs |
|---|---|---|
| `TopG` (ShapeWin.lean `shapeWin`, EveryCharacter.lean `plugWin`) | `shapeWin_r`: of the `TopShape` data, only `hEx` (`ExS`) and `TopG`'s own `hV` mention `(la, G)`. `link_ex` is applied at `𝒜 ∧ G.cls la`. `topDesWin` gets the two class inclusions, which are proved (`⟨hc.1.1, hc.2⟩`, `hc.1.2`). `topG_of_hyps` is `plugWin`'s use via `shape_of`. | `link_ex`, `topDesWin`, the `(la, G)`-free link facts (`link_gl`, `link_brest`, …, `link_alt`) |
| `HostExW` (SupplyChi.lean `supplyChi`) | `supplyChi_r`: `supplyOfAdm` with its admissibility premise discharged by `admissibleClassesTwistedChar`, after `subst` of `s.eps = eps`. `hostExW_main_r` is `plugWin`'s `hS`. | `supplyOfAdm` (= `supplyOfAdmOf hostOfField`), `admissibleClassesTwistedChar`, `VWin` |

## Ledger (`AlpogeSkeleton.v`)

`TopG` and `HostExW` are flipped to refined: **43 of 53**. `sixth_batch_counts`
checks that the four new over-R proofs are refined items, records their
modules (`overR_src6`), and checks that the **40** items proved over R are
distinct. `stated_four_are_unrefined_items` keeps its name, because it anchors
the immutable 2026-11-21 deep-statements finding, but it now checks only ledger
membership.

## OUTCOME

**QED for these 6 (4 proved over R, 2 refined)**, within the allowlist; no
`Admitted`. The Alpöge verdict is unchanged: **PASS-STATIC / PENDING**.

**SUMMARY ok 6 / warn 0 / bug 0.**
