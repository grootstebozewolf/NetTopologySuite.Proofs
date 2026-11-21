<!-- doc-kind: finding
date: 2026-11-21
Provenance: b4ad510
Theorems: `CoreSliceQED.v : sum_Th_instance`, `CoreSliceQED.v : sum_A_instance`, `CoreSliceQED.v : wrong_normalisation_fails`, `CoreSliceQED.v : ch_core_exponent`, `CoreSliceQED.v : ch_core_CH`, `CoreSliceQED.v : ch_core_inputs_small_eps`, `CoreSliceQED.v : main_line_from_core`
-->
# Alpöge main line: the core slice re-derived (QED)

Stop condition requested: QED or QEX. **Reached: QED.** No counterexample
was found. One QEX *control* confirms that the orthogonality check
discriminates.

The subject is `ch_core` (`…/LandauTheorems/ChCore.lean`, l.343) and its use
in `core_gm` (`PrimitiveCosets/CoreGm.lean`). External subject: mirror
`CocoSgt/riemann-hypothesis-lean` @ `7cbf7a0`, read from source; nothing was
built.

## What was open

The merged `2026-11-21-alpoge-ch-core-qed.md` rebuilt `ch_core` as
`core ∘ GrowthSizeBound` (`LeanSkeletonRebuild.v : ch_core_rebuilt`), but left
three things open:
- the **orthogonality identity** `sum_Th` was a hypothesis (`ortho`);
- the **exponent translation** to `x^{1/2+(C+3)ε}` was left in exponential
  atoms;
- the non-vacuity witness used `ε ≈ 3.17`, not a small `ε`.

Separately, `2026-11-21-alpoge-win-seam-closed.md` assumed the per-host
statement `CH` that `core_gm` takes from `ch_core`.

## Rocq (`docs/h1-vacuity/CoreSliceQED.v`, Stdlib over `Q`)

All seven results are *Closed under the global context*.

| theorem | content | OUTCOME |
|---|---|---|
| `sum_Th_instance` | `sum_Th` (l.56), checked in a concrete model. See the model description below the table. | **QED** |
| `sum_A_instance` | `sum_A` (l.28) for every character, `s ∈ A0` and `t`: the sum over `A0` is `\|A0\|·ψ(e1 t)` on `PsiA A0`, and 0 elsewhere | **QED** |
| `wrong_normalisation_fails` | control: with `\|H\|/\|A0\|` in place of `\|A0\|`, the identity fails at `A0 = {0}`, so the check is not vacuous | **QEX (control)** |
| `ch_core_exponent` | with `s = x^{1/2}`, `e = x^ε`, `e2 = x^{ε/2}`, `e8 = x^{ε/8}`, `c = x^{Cε}`: `growth_size_bound`'s bound `e8³(s·c·e²·e2·e8)` **is** `x^{1/2+(C+3)ε}`, since `3/8 + 2 + 1/2 + 1/8 = 3` | **QED** |
| `ch_core_CH` | `core_gm`'s per-host statement `CH`, derived from `ch_core_rebuilt` with `C = eD+eL+3` (as `core_gm` instantiates `ch_core` with `max(eD+eL,0)+3`) and `ch_core_exponent` | **QED** (given `CORE_IN`) |
| `ch_core_inputs_small_eps` | `ch_core_rebuilt`'s inputs are jointly satisfiable with exponent-consistent atoms at `ε = 1/8`, `x = 2^{128}`, `C = 3`. See the witness values below the table. | **QED** |
| `main_line_from_core` | `WinSeamRebuilt.v : main_line_from_tiedWin` with `CH` discharged by `ch_core_CH`, giving **ZeroFreeAbove (1/2)** | **QED** (conditional) |

**The model for `sum_Th_instance`:**
- `E0 × H = (ℤ/2)⁴`, with `E0 = (ℤ/2)²` as in ChCore's `e1`.
- All 16 characters, which are real (±1).
- `A0 = {0,(1,0)}` and `A0 = {0}`, with `T2 ⊆ A0`, and every `t ∈ H`.
- An **arbitrary** `GPsi`. The proof goes coefficient by coefficient: sum
  interchange is proved abstractly, then the 16 coefficients are compared
  by computation.
- This confirms the normalisation `|A0|·b·δ2/2`, with `δ2 = |T2|/|H|` and
  `|PhiSet| = 2|H|`.

**The witness values for `ch_core_inputs_small_eps`:**
- `s = 2^64`, `e = 2^16`, `e2 = 2^8`, `e8 = 4`, `c = 2^48 = e³`.
- `n = 2^64` (so `|H| ≥ √x`), `nT = 2^61`, `m = 2^48`, `k = 2^176`.

**`CORE_IN`** is what `core_gm` extracts by destructuring `CoreAtH` / `EAtH`
(l.30–58): `hostFactsS`, `charsA`, `ch_top` per coset, and `gmA_eq`. It says
that beyond a threshold depending only on the constants, each host supplies
`ch_core`'s inputs with the atoms above and `G = Gm − Sig`, and that
`eD + eL ≥ 0`.

## What the re-derivation shows

- **The orthogonality step is sound in the instances checked.** Averaging
  over the subgroup `A0` isolates exactly the characters trivial on `A0`
  (`PsiA A0`), with weight `|A0|`. The `T2`-average contributes `δ2/2`
  through `|PhiSet| = 2|H|`.
- **The exponent bookkeeping closes.** The `+3` in `x^{1/2+(C+3)ε}` is
  exactly `3ε/8` (the `26 ≤ e8³` threshold) + `2ε` + `ε/2` + `ε/8`.
- **The core's arithmetic forces `|H| ≥ x^{1/2}`.** Combining
  `s ≤ e·m`, `s²m ≤ k` and `e·k ≤ n²s` gives `n² ≥ s² = x`. This is the
  "√X balance" again, now visible as a lower bound on the host group's
  size, which `TopG` must supply. It holds in the small-`ε` witness.

## Remaining seams (unchanged)

- **`CORE_IN`:** the analytic per-host inputs (`ch_top`, `ch_balance`,
  `charsA`, `one_char`).
- **`ATWS` (`TopG`).**
- **The representation bridge** between `LW` and `landau_window_full`.

## OUTCOME

**QED.**
- The core slice is re-derived: orthogonality checked concretely with a
  discriminating control, the exponent closed, and non-vacuity shown at a
  small `ε`.
- `CH` is discharged from `ch_core`.
- `main_line_from_core` gives ZeroFreeAbove (1/2) as one closed Rocq
  theorem with zero axioms, conditional on `CORE_IN`, `ATWS` and the `formB`
  / Landau inputs.

The audit verdict is unchanged: **PASS-STATIC / PENDING**.

**SUMMARY ok 6 / warn 0 / bug 0.**
