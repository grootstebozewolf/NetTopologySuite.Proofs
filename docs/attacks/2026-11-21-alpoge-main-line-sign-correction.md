<!-- doc-kind: finding
date: 2026-11-21
Provenance: b7cc174
Theorems: `LandauWindowCore.v : window_contra`, `LandauWindowCore.v : real_pole_residue_pos`, `LeanSkeletonRebuild.v : level_of_tiedWin_rebuilt`, `LeanSkeletonRebuild.v : no_real_zero_right_of_theta`
-->
# Correction: the Alpöge main line's sign step is `landau_window`, not `landau_entire`

Corrects `2026-11-20-alpoge-grh-lean-audit.md`, slices 2, 2b, 3 (R3a) and 13.
That finding was merged and is immutable. External subject: mirror
`CocoSgt/riemann-hypothesis-lean` @ `7cbf7a0`, read from source; nothing was
built.

## What the audit said, and what the source says

**Audit (slices 2/13).** The positivity step is `Landau.lean :
landau_family / zero_free_of_Chebyshev_growth`. That is Landau's theorem for
Mellin transforms of `H = C·x^θ − G ≥ 0`, with `σ(σ−1) < 0` in the strip.
Slice 13 corrected an earlier "coefficient sign" reading to this one.

**The main line, traced through `FormB`:**
1. `zeroFreeAll_of_topG` (`…/CharacterBoxes/ZeroFreeAllOfTopG.lean`) calls
   `zeroFreeOn_of_tiedWin_cyc` with `hB := fun ψ _ => UpperTheory.Comparison₂.formB _`.
2. `zeroFreeOn_of_tiedWin_cyc` calls **`level_of_tiedWin`**
   (`…/TotientGaloisClasses/TopWin.lean`), which consumes
   **`Λ.FormBAt la`**:
   `∀ θ ∈ (0,1), HasWindows {x | Gm x ≤ x^θ} la → ZeroFreeAbove θ`, the
   **windowed** form, where the bound is needed only on windows `[Y, Y^la]`.
3. `formB` (`…/PrimitiveCosets/Imports.lean`) calls `zeroFree_of_rpow_window`,
   then `lemmaL`, then **`landau_window`**
   (`…/DedekindLFunctions/LandauTheorems/landauWindow.lean`, 170 lines).

**`Landau.lean` is off the main line.** `zero_free_of_Chebyshev_growth` is
used only by `level_of_tiedAll`, which is used only by `zeroFreeOn_of_tiedAll`,
and that has **no callers** (ripgrep over all 175,187 files). It is imported,
because every file is, but the main theorem's proof term does not go through
it. Build-level confirmation would need the dependency graph from a build,
which is audit step 7 and was not run.

## The actual mechanism (`landau_window`)

- **Data** (`PoleData g Φ Z`). `Φ` is the Laplace transform of `g`
  (`g = Gm` in log variable `u`). It is meromorphic on `Re s > 0` with simple
  poles at `Z`, and **at real poles the residue has positive real part**
  (`ρ.im = 0 → 0 < c.re ∧ c.im = 0`).
- **Window majorant** (`WindowHypU g θ δ`). For every `η > 0` there are
  arbitrarily large `U` and an `R` with `g ≤ R`, `R ≥ 0` on `[U, (1+δ)U]`, and
  `∫ R·e^{−θu} ≤ e^{ηU}`.
- **High derivatives** (`landau_window_key`). For some `σ > 2`, the `k`-th
  Taylor coefficients `(−1)^k Φ^{(k)}(·)/k!` at `σ + iγ` (norm) and at `σ`
  (real part) are bounded by `C·e^{ηU}/(σ − θ)^k`, for some `k ≥ U`.
- **Contradiction** (`landau_dichotomy`, `landau_nearest`,
  `landau_window_contra`, `landau_growth_contra`).
  - A pole with `Re ρ > θ` nearest to the line `Re s = σ` makes those
    coefficients `≳ c/d^k` with `d < e = σ − θ`.
  - But `(e/d)^k` outgrows `e^{ηU}` once `η < log(e/d)`, with `U ≤ k`.

**Where the sign lives.** It is in the **majorant positivity** (`R ≥ 0`,
`g ≤ R` on windows) together with the **positive residues at real poles**
(the `Re` term at real `σ`). It is not in a Mellin identity with `H ≥ 0`
over all `x ≥ 1`. The method is Landau's high-derivative (Taylor-coefficient)
argument, which lets the growth bound be **windowed**. The windowed bound is
exactly what the √X chain supplies (only on `x ∈ Win`, with `la = 3/2`).

## Rocq

| theorem | mirrors | OUTCOME |
|---|---|---|
| `LandauWindowCore.v : window_contra` | `landau_window_contra` + `landau_growth_contra`: with `0 < c`, `0 < d`, `1 ≤ s`, `s·d < e`, the inequality `c·e^k ≤ (\|M\| + \|C\|·s^k)·d^k` cannot hold for arbitrarily large `k`. Proof by Bernoulli growth of `(e/(sd))^k`. | **QED, zero axioms**. The translation `e^{ηU} ≤ s^k` for `U ≤ k`, with `s = e^η` and `η` small, is not re-proved. |
| `LeanSkeletonRebuild.v : no_real_zero_right_of_theta` | the sign step of `landau_entire` | still correct **for that lemma**, but **that lemma is off the main line**. Its comment ("the DEFINITE SIGN inside landau_entire / landau_family") is accurate about those lemmas and should not be read as the main line's sign. |

## Corrections to the merged audit

| slice | earlier reading | corrected reading |
|---|---|---|
| 2 (R2), 2b | positivity step = `landau_family` / `zero_free_of_Chebyshev_growth` | the main line uses **`landau_window`** through `FormBAt`. `Landau.lean`'s route has no callers on the main line. |
| 3 (R3a) | "windowed Landau: … `FormB`, a windowed form of R2" | `FormB` is **not** derived from R2. It is proved independently by `landau_window`, a different argument (high derivatives, majorant on windows). |
| 13 | the sign is `H ≥ 0` plus Mellin plus `σ(σ−1) < 0` | true of `landau_entire`, which is off the main line. On the main line the sign is **`R ≥ 0` on windows plus positive real-pole residues**, inside a Taylor-coefficient contradiction. The factor **`σ(σ−1) < 0` does reappear** there, inside the residue (see "Ladder rung" below). Slice 13 had the right ingredient in the wrong lemma. |
| 13 addendum | the Euler product enters via `hsumL` | on the main line the Euler product enters through `PoleData` for `g = Gm`: Laplace identity, poles at zeros, residues equal to multiplicities. `hsumL` is in the off-line `Landau.lean`. The Davenport–Heilbronn reading is unchanged in substance. |

## Ladder rung: where the real-pole residue sign comes from (`poleData`)

`…/LandauTheorems/poleData.lean : poleData`, lines 261–384, read from source:
- **Construction.** `Φ = Σ_i (a_i/2)·(Φ₁(χ_i) + Φ₂(χ_i⁻¹))`. Closure under
  `χ ↦ χ⁻¹` is **built in** through `Re Gchi`.
- **Residue at a zero `ρ`.** `c = S·(−1/(ρ(ρ−1)))`, where
  `S = Σ_i (a_i/2)·(m(χ_i, ρ) + m(χ_i⁻¹, ρ̄))`, weights `a_i > 0`
  (`CharFamily.a_pos`), multiplicities `m ∈ ℕ`, and at least one `m ≥ 1`. So
  `S > 0`.
- **Real `ρ ∈ (0,1)`.** There `ρ(ρ−1) < 0`, so `c > 0`. The factor
  `1/(s(s−1))` is the Mellin kernel of the Riesz weight `(x/n − 1)⁺` in
  `Gchi`.

| theorem | statement | OUTCOME |
|---|---|---|
| `LandauWindowCore.v : real_pole_residue_pos` | For a list of `(a_i, m₁ᵢ, m₂ᵢ)` with all `a_i > 0` and some `m₁ᵢ + m₂ᵢ ≥ 1`, and real `0 < ρ < 1`: `0 < S·(−1/(ρ(ρ−1)))` | **QED, zero axioms**. The residue computation itself (`logDeriv_local`, the `dslope` algebra) is the translation and is not re-proved. |

So, on the main line, the **definite sign** is three things together:
1. positive weights times multiplicities (`S > 0`);
2. `ρ(ρ−1) < 0` in the strip;
3. the window majorant `R ≥ 0`.

These feed the high-derivative contradiction (`window_contra`). The Euler
product enters as the source of `Gchi`'s von Mangoldt sums, whose Laplace
transform is `−L'/L` with poles exactly at the zeros.

## Ladder rung: `level_of_tiedWin` with windows and `FormBAt`

This closes the "shape only" caveat on `zero_free_half` (merged audit,
slice 8; Cursor review at `290d863`).

`LeanSkeletonRebuild.v : level_of_tiedWin_rebuilt` (Part 6, over `Q`) is
*Closed under the global context*. It takes these named hypotheses:
- Lean's `HasWindows S la` (`∀ y, ∃ Y ≥ y, ∀ x ∈ [Y, Y^la], S x`);
- **`FormBAt la`**, which is `landau_window`'s output and exactly the
  windowed statement the main line uses;
- **`WIN`**, Lean's `ChebyshevInequalityOnWindows` and
  `ChebyshevInequalityAtWindowScale` combined: for small `ε`, a window set
  `Win` with `HasWindows Win la` and `Gm x ≤ x^(1/2+Kε)` on `Win` beyond
  `x₁`.

From these it proves **zero-freeness above `1/2`**. The proof follows Lean's:
1. choose `ε` with `Kε ≤ δ/2`;
2. set `θ = 1/2 + δ/2 < Re s`;
3. restart `Win`'s windows beyond `max(y, x₁, 1)` so that they become windows
   for `{Gm ≤ x^θ}`, using monotonicity of `x^a` in `a` for `x ≥ 1`;
4. apply `FormBAt`.

The **translation** is that `x^a` appears as an abstract `pw x a`, monotone
in `a` for `x ≥ 1`. The `1/2` is still the exponent `WIN` supplies, i.e. the
√X window from `ch_core` / `GrowthSizeBound`, as before.

**OUTCOME.** **CORRECTED.**
- The main line's definite sign is located in `landau_window`. Its
  elementary contradiction core is machine-checked (`window_contra`).
- The `Landau.lean` route analysed in slices 2/13 is shown, by caller search,
  to be off the main line.
- The audit verdict is unchanged: **PASS-STATIC / PENDING**.

**SUMMARY ok 4 / warn 1 (slices 2/2b/3/13 of the merged audit misattributed the main-line sign step) / bug 0.**
