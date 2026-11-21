<!-- doc-kind: finding
date: 2026-11-21
Provenance: c4979f8
Theorems: `FormBRebuilt.v : poly_le_qpow`, `FormBRebuilt.v : formB_rebuilt`, `FormBRebuilt.v : main_line_rebuilt`
-->
# Alpöge main line: `formB` rebuilt, and the main line composed into one Rocq theorem

Follows `2026-11-21-alpoge-landau-window-assembled.md`. That finding named one
unassembled link: the rest of `formB`, which turns the windowed growth bound
into the input of `landau_window`. This slice rebuilds that link. It then
composes it with `level_of_tiedWin_rebuilt` (`LeanSkeletonRebuild.v`, Part 6)
into one theorem. External subject: mirror `CocoSgt/riemann-hypothesis-lean`
@ `7cbf7a0`, read from source; nothing was built.

## The link, read from source

`UpperTheory.Comparison₂.formB` (`PrimitiveCosets/Imports.lean`) obtains
`F` and `hG : Gm F = Λ.Gm`, `hZ` from `level_family Λ`. It then calls
`zeroFree_of_rpow_window F` with `δ = la − 1` and `C = 1`. The steps from
there:

1. **`windowHyp_of_rpow`.**
   - Majorant: `R y = |C|·y^θ`.
   - Window integral: `∫_Y^{Y^{1+δ}} R y·y^{−θ−1} dy = |C|·δ·log Y`.
   - `windowHyp_of_rpow_eventually` then gives `|C|δ·log Y ≤ Y^η` for
     large `Y`. Its proof is Mathlib's `Real.log_le_rpow_div`.
2. **`windowHypU_of_windowHyp`.** Change of variables `y = e^u`, with
   window `[log Y, (1+δ) log Y]`.
3. **`lemmaL`.**
   - `poleData F` supplies the pole data, and `landau_window` gives
     `Re ρ ≤ θ` on
     `zeroSet F = {ρ | 0 < Re ρ, ∃ i, L(χᵢ, ρ) = 0 ∨ L(χᵢ, ρ̄) = 0}`.
   - A zero with `θ < Re s < 1` lies in `zeroSet F`, which gives the
     contradiction.
   - `Re s ≥ 1` is handled by `charFamily_LFunction_ne_zero_of_one_le_re`.

**Why windows suffice.** The majorant's window integral grows like
`δ·log Y = δ·U`, linearly in the log variable `U`. `WindowHypU` asks only for
`≤ e^{ηU}` for every `η > 0`. So the growth bound is needed only on windows
`[Y, Y^{la}]`, which is exactly what the √X chain provides.

## Rocq (`docs/h1-vacuity/FormBRebuilt.v`, Stdlib over `Q`)

The three results below are *Closed under the global context*.

| theorem | mirrors | OUTCOME |
|---|---|---|
| `poly_le_qpow` (with `bernoulli2`) | the discrete core of `windowHyp_of_rpow_eventually`: for `K ≥ 0` and `s > 1`, `K(n+1) ≤ s^n` for all large `n`. For `Y ∈ [e^n, e^{n+1})`, `log Y ≤ n+1` and `Y^η ≥ s^n` with `s = e^η`. | **QED** |
| `windowHyp_of_rpow_rebuilt`, `lemmaL_rebuilt`, `formB_rebuilt` | `formB`, giving `FormBAt la` in exactly the shape `level_of_tiedWin_rebuilt` consumes | **QED** (conditional, see below) |
| `main_line_rebuilt` | `level_of_tiedWin ∘ formB`, which yields **ZeroFreeAbove (1/2)**, as one theorem | **QED** (conditional) |

**Named inputs of `formB_rebuilt`:**

| input | Lean source |
|---|---|
| `INT_rpow` | the window integral of `y^θ·y^{−θ−1}` is `δ·log Y` (calculus) |
| `EV` | `windowHyp_of_rpow_eventually` (its discrete core is `poly_le_qpow`) |
| `LW` | `landau_window ∘ windowHypU_of_windowHyp`, with `poleData F` |
| `NV1` | `charFamily_LFunction_ne_zero_of_one_le_re` |
| `LEVEL` | `level_family` (`ZeroFree F θ` gives `ZeroFreeAbove θ`) |
| `pw_wd`, `pw_nonneg` | `x^a` is a function of `a` (Lean rewrites `1 + (la−1) = la`), and is nonnegative |

`main_line_rebuilt` adds `level_of_tiedWin_rebuilt`'s inputs:
- `pw_mono`;
- `WIN`, the windows at exponent `1/2 + Kε`, i.e. Lean's
  `ChebyshevInequalityOnWindows` and `ChebyshevInequalityAtWindowScale`;
- `la > 1` (Lean: `la = 3/2`).

## The main line in Rocq, and its seams

The main line's logic, from windows at `1/2 + Kε` to zero-freeness above
`1/2`, is now **one closed Rocq theorem** with zero axioms. Two of its
hypotheses are discharged elsewhere only in part:

- **`LW`.** `LandauWindowRebuilt.v : landau_window_rebuilt` proves its
  conclusion from `KEY`, `CAUCHY`, `POLE1`, `POLE2`, `LF`. The step from
  `WindowHypU` to `KEY` is `landau_window_key`. Its pointwise core is
  `window_ineq_discrete`, but the Laplace-coefficient identity
  (`landau_coeff`) and `landau_tails` are not re-proved. So `LW` is not
  formally composed with `landau_window_rebuilt`: the two meet at `KEY`.
- **`WIN`.** `ch_core_rebuilt` and `growth_size_bound`
  (`LeanSkeletonRebuild.v`) check the core averaging and the √X chain-length
  bound. The derivation of the window statement from them is not composed.

**Analytic translations, not re-proved:**
- calculus (`INT_rpow`);
- the log/rpow inequality (`EV`, beyond its discrete core);
- change of variables;
- `poleData` (the Laplace transform of `Gm` is meromorphic with poles at the
  zeros);
- nonvanishing on `Re s ≥ 1`;
- `level_family`.

## OUTCOME

**QED.**
- `formB` is rebuilt.
- The main line from the window bound to `ZeroFreeAbove (1/2)` is a single
  composed Rocq theorem (`main_line_rebuilt`) inside the three-axiom budget
  (no axioms used).
- It is conditional on the named inputs above.
- Its two seams (`LW` at `KEY`, `WIN` at the window statement) are
  identified.

The audit verdict is unchanged: **PASS-STATIC / PENDING** (no Lean build,
no `#print axioms`, analytic inputs not re-proved).

**SUMMARY ok 3 / warn 0 / bug 0.**
