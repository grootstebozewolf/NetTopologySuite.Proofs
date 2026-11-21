<!-- doc-kind: finding
date: 2026-11-21
Provenance: 43d9ba2
Theorems: `WinSeamRebuilt.v : core_gm_rebuilt`, `WinSeamRebuilt.v : onWindows_rebuilt`, `WinSeamRebuilt.v : win_rebuilt`, `WinSeamRebuilt.v : main_line_from_tiedWin`
-->
# Alpöge main line: the `WIN` seam closed

Follows `2026-11-21-alpoge-formb-main-line-composed.md`. That finding left
two seams in `main_line_rebuilt`:
- `LW`, which meets `landau_window_rebuilt` at `KEY`;
- `WIN`, the windows at exponent `1/2 + Kε`, which was taken as a single
  hypothesis.

This slice **derives `WIN`** from the inputs the Lean main line actually
uses. External subject: mirror `CocoSgt/riemann-hypothesis-lean` @ `7cbf7a0`,
read from source; nothing was built.

## Where `WIN` comes from on the main line (read from source)

`zeroFreeAll_of_topG` (`CharacterBoxes/ZeroFreeAllOfTopG.lean`) calls
`zeroFreeOn_of_tiedWin_cyc` with three arguments:

- **`h112`, i.e. `ChebyshevInequalityOnWindows`:**
  - It is `level_gm_le_on_family_scales`, which is
    `windowInequality_of_artinInputs tiedCore_of_chainTied`.
  - That is a quantifier wrapper around **`core_gm`** (`CoreGm.lean`).
  - `core_gm` calls `ch_core` with `C = max(eD+eL, 0) + 3`, bounds each
    coset gap by `ch_top`, and then does exponent bookkeeping (see below).
- **`hB`, i.e. `formB`:** rebuilt in the previous slice.
- **`h`, i.e. `ChebyshevInequalityAtWindowScale`:**
  - It comes from `TopG` (with `HostExW`); `eFamC_of_cls` supplies the
    `EFamC` bound.
  - `TopG` is discharged upstream (`shapeWin` / `TopShape`), as traced in
    the merged audit (R3).

**`core_gm`'s bookkeeping, lines 46–76.** Write `E = eD + eL`, which is
nonnegative by the Core bounds. Then:
1. From `ch_core`: `Gm ≤ x^{1/2+(E+6)ε} + Sig`.
2. From `sigA_le`: `Sig ≤ 4o·x^{1/2+ε}`.
3. Eventually `1 + 4o ≤ x^ε`.
4. Since `x^{1/2+ε} ≤ x^{1/2+(E+6)ε}`, these give
   `Gm ≤ (1+4o)·x^{1/2+(E+6)ε} ≤ x^ε·x^{1/2+(E+6)ε} = x^{1/2+(E+7)ε}`.

## Rocq (`docs/h1-vacuity/WinSeamRebuilt.v`, Stdlib over `Q`)

The four results below are *Closed under the global context*.

| theorem | mirrors | OUTCOME |
|---|---|---|
| `core_gm_rebuilt` | `core_gm`: from the `ch_core` output (`CH`), `sigA_le` (`SIG`) and eventual `1+4o ≤ x^ε` (`EVX`), derive `Gm ≤ x^{1/2+(eD+eL+7)ε}`. The threshold depends only on the constants. | **QED** (conditional) |
| `onWindows_rebuilt` | `windowInequality_of_artinInputs`. The constants come from `EFamC` (`C`) and the Tied bounds (`K, cHH, eK`), *then* `core_gm`'s threshold, *then* `x`. The order matches Lean, and `max x1 (max x0 xE)` covers all three thresholds. | **QED** |
| `win_rebuilt` | `WIN` from `AtWindowScale` and `onWindows_rebuilt`, with `K = max(eD+eL+7, 0)` | **QED** |
| `main_line_from_tiedWin` | `main_line_rebuilt` with `WIN` discharged: **ZeroFreeAbove (1/2)** | **QED** (conditional) |

**New named inputs:**

| input | Lean source |
|---|---|
| `CH` | `ch_core`, plus `ch_top` per coset and `gmA_eq` (rebuilt in part as `ch_core_rebuilt`) |
| `SIG` | `sigA_le` |
| `EVX` | `tendsto_rpow_atTop` |
| `ARTIN` | `tiedCore_of_chainTied` (destructuring of `ChainTied`) |
| `ATWS` | `ChebyshevInequalityAtWindowScale`, from `TopG` |
| `pw_add` | `Real.rpow_add` |

The `formB` inputs of `FormBRebuilt.v` are unchanged.

## A small mismatch, bridged

Lean's `exists_small_eps` (`TopWin.lean`, l.59) picks `ε` with
`C·ε ≤ δ` using `|C| + 1`, so it accepts a constant `C = eD + eL + 7` of
either sign. `LeanSkeletonRebuild.v : level_of_tiedWin_rebuilt` assumes
`K ≥ 0`. `win_rebuilt` closes the gap:
- it takes `K = max(eD+eL+7, 0)`;
- it restarts the windows at `x ≥ max(x1, 1)`;
- it uses that `x^a` is monotone in `a` for `x ≥ 1`.

This is a property of the earlier Rocq rebuild, not a defect in Lean: on
the main line, `E ≥ 0` anyway.

## Remaining seams

- **`LW` at `KEY`.** `landau_window_key` turns `WindowHypU` into `KEY`
  through `landau_window_ineq` (core checked as `window_ineq_discrete`),
  `landau_coeff` and `landau_tails`. The last two are not re-proved.
- **`CH`.** This is `ch_core`, partly rebuilt (`ch_core_rebuilt` checks the
  averaging and the size bound). The connection from that rebuild to the
  per-host statement `CH` is not composed.
- **`ATWS`, i.e. `TopG`.** This is the deep input: family-connectedness of
  host classes, discharged upstream through `shapeWin` / `TopShape` from
  `GLq.Green`. It is not rebuilt.

## OUTCOME

**QED.** `WIN` is no longer a single assumption. It is derived from
`core_gm`'s inputs, the Artin-input bridge and `AtWindowScale`, and
`main_line_from_tiedWin` gives ZeroFreeAbove (1/2) as one closed Rocq
theorem with zero axioms.

The deepest remaining assumption is now explicit: **`TopG`**, supplying
`ChebyshevInequalityAtWindowScale`. The audit verdict is unchanged:
**PASS-STATIC / PENDING**.

**SUMMARY ok 4 / warn 0 / bug 0.**
