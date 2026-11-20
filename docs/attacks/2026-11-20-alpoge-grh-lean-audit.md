<!-- doc-kind: finding
date: 2026-11-20
Provenance: external artifact, static audit only (no build)
Theorems: none in this repo — subject is a third-party Lean 4 development
-->
# Alpöge RH/GRH Lean claim: static audit

**Subject.** The Lean 4 development published by Levent Alpöge on 2026-11-20
(announcement `https://alpo.ge/remark.pdf`). It claims RH, and GRH for
Dirichlet L-functions, "formalized without assumptions".

**Artifact audited.** The GitHub mirror `CocoSgt/riemann-hypothesis-lean` at
commit `7cbf7a0c32fca1badf05931879a37c3f8a2b03b4`, cloned shallow. Details:

- 175,187 `.lean` files, about 17.4 M lines.
- Toolchain `leanprover/lean4:v4.33.1`.
- Mathlib pinned at `0df444a360eaa60ab8c11dca51a86af692955474`
  (2026-08-21).

The mirror says it reproduces the author's archive byte for byte, with
SHA-256 `9631b4f0…49c7fc`. **Not verified here:** neither alpo.ge nor the
release tarball was downloaded.

**Environment.** Claude Code cloud container with 4 cores, 15 GB RAM and
56 GB free disk. A full `lake build Main` is not feasible in this
environment, so nothing below is a kernel check.

| step | claim | OUTCOME | artifact |
|---|---|---|---|
| 1 | Headline `riemannHypothesis : RiemannHypothesis` uses Mathlib's own definition. | PASS: `Mathlib/NumberTheory/LSeries/RiemannZeta.lean:185` at the pinned commit is `∀ s, riemannZeta s = 0 → ¬∃ n : ℕ, s = -2 * (n + 1) → s ≠ 1 → s.re = 1/2` | mathlib4 @ `0df444a3` |
| 2 | The four auxiliary statements say what their names claim. | PASS (by reading): `src/Statements.lean` imports **only** `Mathlib`. GRH is stated for every χ mod N, including imprimitive χ, on `0 < re s < 1`. Imprimitive Euler-factor zeros sit on `re s = 0` and are correctly excluded. A primitive-only variant is also stated, as is non-vanishing on `re s > 1/2` (excluding `χ = 1, s = 1`). | `src/Statements.lean` |
| 3 | No shadowing or aliasing of the statement constants. | PASS: no redefinition or `export` of `RiemannHypothesis`, `riemannZeta` or the four `Statements` names. The repo's `LFunction`/`IsPrimitive` defs are namespaced, and `Statements.lean` cannot see them. | ripgrep over `src/` |
| 4 | Static scan for unproved content. | PASS (text-level): 0 hits each for `sorry`, `admit`, `axiom` declarations, `native_decide`, `decide +native`, `ofReduceBool`, `unsafe`, `implemented_by`, `@[extern]`, `opaque`, `#eval`, `initialize`, `debug.skipKernelTC`, `addDeclWithoutChecking`/`addDeclCore`, `unsafeCast`, `setEnv`, `trustCompiler`. This independently reproduces the mirror README's table. | ripgrep over `src/` |
| 5 | Metaprogramming does not bypass the kernel. | PASS (by reading): there is one `addDecl` user, `Formalism/HermitianCurvature/HermitianCurvatureProofs/CutCptCopy.lean`. It copies declarations with constants renamed, and the copies go back through the kernel. The five `run_cmd`/`modifyEnv` uses (`src/BuildAid/D1–D5.lean`) only touch the library-suggestion deny list. There are 67 files with `macro`/`elab`/`syntax` and 16 `run_tac` uses (sampled: `revertAll`; `kexactB`/`kcopy` term elaborators). These build terms, which the kernel still checks. 4 files set `maxHeartbeats 0`, which affects performance only. | files named |
| 6 | The final chain does not leave a "literature" hypothesis open. | PASS (by reading): `UpperTheory.FinalTheorems.everyCharacter` fills `OpenLiteratureStatements` with `⟨h, recTExists, h⟩`, where `h := UpperTheory.Gal.Int.galoisLocalGlobalStrong_recParameter`, a theorem. RH follows via `Formalism.VW.rh_of_every`. Names such as `Published.*`, `LocalFrameAxioms` and `…OfAdmitted` are hypotheses-as-data that must be discharged. Steps 7–8 are what rule out a gap; the names alone do not. | `Development/AutomorphicArithmetic/CharacterBoxes/MainConclusion.lean`; `Supplements/Kernels/MainTheorems.lean` |
| 7 | `lake build Main` succeeds. | NOT RUN (resources). Third-party reports say A. Sutherland's independent build succeeded; not reproduced here. | — |
| 8 | `#print axioms` on the five `Main.lean` theorems shows only `propext`, `Classical.choice`, `Quot.sound`. | NOT RUN (needs step 7) | — |
| 9 | Independent kernel replay (`lean4checker` or comparator). | NOT RUN here. The comparator pass is reported by third parties. | — |
| 10 | Mirror = author's archive (SHA-256). | NOT RUN | — |
| OUTCOME | Static audit of statement fidelity and escape hatches | **PASS-STATIC / PENDING.** No defect found in the statements or in the visible trust surface. Steps 7–10 decide the claim, and none ran here. This is not a verification of RH. The mathematics, about 17 M lines and described as 250k+ pages written out, has no human review yet. | this table |

**SUMMARY ok 6 / warn 0 / bug 0 / not-run 4**

## What would turn PENDING into a verdict

1. **Steps 7–9 on a large machine.** Log time and peak memory, and record
   the exact `#print axioms` output.
2. **Step 10 against `alpo.ge` parts 01–14.**
3. **A QEX probe in the spirit of `docs/h1-vacuity/`.** Check that the
   heavy intermediate notions (`UpperTheory.Top.VWin`,
   `GalStar.Row0b`, `GlobalTheory.GLq.Green`) are not vacuously satisfiable
   in a way that makes the chain trivial. If the kernel accepts the proof,
   this cannot make RH false. It would, however, show where the real content
   sits, which is useful for human review.

## Slice 2: where off-line zeros are excluded (read from source, 2026-11-20)

`remark.pdf` (alpo.ge) and YouTube are both blocked by this session's
network policy. The chain below was therefore traced in the Lean source of
the mirror @ `7cbf7a0`. It is a reading of statements and proof skeletons,
not a check of the mathematics.

| rung | statement (paraphrase) | where |
|---|---|---|
| R0 | `RiemannHypothesis` ⇐ `EveryCharacter` (no `L(χ,s)` zero for `Re s > ½`) via the reflection `s ↔ 1−s` | `Formalism/GammaFactorNonvanishing/CritLine.lean : Formalism.VW.rh_of_every` |
| R1 | `EveryCharacter` ⇐ `ZeroFreeAll` (same, per primitive character `PChar`) plus imprimitive reduction | `Development/AutomorphicArithmetic/CharacterBoxes/EveryCharacter.lean` |
| R2 | **Positivity / Landau step.** `Gm(y) := Gz(y) + Σ_ψ wt ψ · Re gChi(ψ,y)` is a weighted Riesz-mean von Mangoldt sum `Σ Λ(n)(y/n−1)` twisted by a conjugation-closed character family (involution `τ`, `c (τ i) = (c i).inv`, multiplicities `k`). If `Gm(y) ≤ y^θ` eventually, then no zero has `Re s > θ`. | `Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/Landau.lean : landau_family, zero_free_of_Chebyshev_growth`; defs in `…/ExplicitFormulaErrorOfHostConditions.lean`, `…/Analytic.lean`, `Formalism/StatementOC.lean` |
| R3 | The growth bound is supplied by `TopG` + `HostExW` (`la = 3/2`), i.e. family-connectedness of host classes | `Development/AutomorphicArithmetic/CharacterBoxes/ZeroFreeAllOfTopG.lean` |
| R4 | `VWin := ∀ ψ, VWinAt ψ 401`: for fields `E` cut out by `ψ` and auxiliary primes `q ≡ 3 (8)`, `d ≡ 7 (16)` (`WinPair`), the weighted lengths of Galois-cohomology (Sha-type) groups satisfy `Σ_{l∈S} log l · Σ_e shaLen ≤ √(exp(x^ε))` | `Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean` |

**Mapping to the attack vector (this repo's ladder, chat 2026-11-20).**

- *Step 3, the invariant `I ≥ 0`:* **match.** `I` is the non-negativity of
  the Dirichlet coefficients of a conjugation-symmetric combination of
  `−L'/L`. Landau's lemma turns that into the statement that a real
  singularity governs growth. An off-line zero with `Re ρ > θ` would force
  `Gm` to grow like `y^{Re ρ}`, contradicting R2's upper bound.
- *QEX (Davenport–Heilbronn):* **consistent.** The coefficients are
  `Λ(n)χ(n)`, which exist only because of the Euler product. A function with
  only a functional equation has no such expansion, so R2 cannot apply to
  it.
- *Symmetric pairs:* **match.** `landau_family` is stated over a
  family closed under `χ ↦ χ̄`, the conjugation half of the quartet.
- *Where ½ enters:* the reflection R0, and the `√` in R4's bound.
- *Step 4 (compact region, certified numerics):* **no match.** The argument
  is symbolic throughout. Its finite or arithmetic input is cohomological
  (R4), not interval arithmetic.
- *Open:* R3–R4 carry the real weight (about 17 M lines below them). Whether
  `TopG` / `VWin` are where the "Stepanov multiplicity via theta lifts"
  lives cannot be told from names. That is the next slice, and the natural
  `docs/h1-vacuity/`-style target. Check that `HostExW`, `FamilyClassConnected`
  and `VVle` are not satisfiable for trivial reasons.

**SUMMARY (slice 2) ok 4 / warn 0 / bug 0 / open 1**

### Slice 2b: what `remark.pdf` says, and where it slots in

Provenance: a summary of `https://alpo.ge/remark.pdf` supplied by the user in
chat on 2026-11-20. The agent could not fetch it (DNS blocked) and has not
read it. Points relevant here:

- The argument descends from Stepanov's function-field method.
- Multiplicity is supplied by chains of theta lifts, of length on the order
  of the von Mangoldt sum being considered.

**Where it slots in (interpretation).** Stepanov's method yields **only an
upper bound**: an auxiliary function that vanishes to high order caps a
point count. R2 needs exactly that. `ChebyshevGrowthImpliesZeroFree`
assumes only the one-sided bound `Gm(y) ≤ y^θ`. Landau positivity does the
rest, because non-negative coefficients make a one-sided bound enough. In
Bombieri–Stepanov, the lower bound has to come from a separate
twist/averaging trick. Here the conjugation-closed weighted family in
`landau_family` plays that role. Expected location of the Stepanov /
theta-lift step: R3–R4 (`TopG`, `VWin`). Not yet confirmed in source.

## Slice 3: where the ½ exponent is produced (read from source, 2026-11-20)

Traced down from R3 (`zeroFreeAll_of_topG`) in the mirror @ `7cbf7a0`. This
is a reading of statements, not a check of the mathematics.

| rung | statement (paraphrase) | where |
|---|---|---|
| R3a | Windowed Landau: if `Gm(x) ≤ x^(1/2 + (eD+eL+7)ε)` holds on a family's windows (lacunary, `la = 3/2`) for every small `ε`, the level is zero-free on `Re s > ½`. This is `level_of_tiedWin`, plus `FormB`, a windowed form of R2. | `Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/TopWin.lean` |
| R3b | That window inequality ⇐ `ChainTied` per window point. `ChainTied` packages a chain datum `Dd` whose local fields are divisor **ranks**, **slopes** `mu`/`muMax` of a lattice and its dual, and degree data. These are Arakelov / Harder–Narasimhan quantities, the natural home of a Bost slope inequality. | `Formalism/SharpRestriction/GlobalSchurBounds/TieGlobal.lean : ChainTied, TieLocal`; `Development/AutomorphicArithmetic/PrimitiveCosets/LevelGmLeOnFamilyScales.lean` |
| R3c | `core_gm`: `CoreAtH` + `EAtH` ⇒ `Λ.Gm x ≤ x^(1/2 + (eD+eL+7)ε)` | `Development/AutomorphicArithmetic/PrimitiveCosets/CoreGm.lean` |
| **R3d** | **`ch_core`, the analytic engine.** Hypotheses include chain length **`m ≤ x^(1/2+ε/2)`**, multiplicity/degree **`x·m ≤ k`**, and a per-element *gap* bound `gapA … ≤ x^(Cε)·errorBracket`, where `gapA = Σ_t Σ_j (ASK − Re MAIN)` is the arithmetic count minus its main term. Conclusion: `GmA ≤ x^(1/2+(C+3)ε) + SigA`. | `Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChCore.lean:343`; defs in `…/DedekindLFunctions/SplitInertia.lean` |

**Reading (interpretation, not confirmed by the author's text).**

- R3d has the Stepanov parameter balance: a chain of length `m ≈ √x`
  ("chains of theta lifts of length about √X") against a multiplicity
  `k ≥ x·m`.
- In Stepanov's method for curves, an auxiliary polynomial of degree about
  √q gives `#C(F_q) ≤ q + O(√q)`. Here, the `m ≤ x^(1/2)` constraint
  is literally where the exponent ½ in `Gm(x) ≤ x^(1/2+…)` comes from.
- The per-chain-element upper bound (`gapA`) is fed by rank and slope data
  (R3b). That is where the Bost slope inequality plausibly enters; not yet
  traced.
- Combined with slices 2/2b: Stepanov gives a one-sided `Gm ≤ x^(½+ε)`,
  Landau positivity turns it into a zero-free `Re s > ½`, and the reflection
  `s ↔ 1−s` puts the zeros on the line.

**Next target.** The proof of the `gapA` bound, and how `ChainTied` is
inhabited (`TopG` → `forall_goal_of_shape_of_hyps`, `VWin` → `supplyChi`).
That is where the theta lifts must be constructed. It is also the place for
an `h1-vacuity`-style probe: are `CoreAtH` / `ChainTied` inhabited only by
the genuine chain, or by something degenerate (for example `m = 0`, empty
`TT`)? Note that `x·m ≤ k` with `m = 0` is trivially satisfiable, so
`SizesA` / `RestSize` must exclude it.

**SUMMARY (slice 3) ok 4 / warn 1 (degenerate-`m` question open) / bug 0**

## Slice 4: the gap bound, the degenerate-`m` question, and an internal QEX (2026-11-20)

Read from the mirror source @ `7cbf7a0`, statements only.

| item | finding | where |
|---|---|---|
| warn (slice 3): `m = 0` | **Resolved.** `RestSize` requires `x^(1/2 − ε) ≤ m`. Combined with `ch_core`'s `m ≤ x^(1/2 + ε/2)`, the chain length is pinned at `m ≈ √x`. It also requires `k ≤ n²·x^(1/2−ε)`, which with `x·m ≤ k` forces `n = |H| ≳ x^(1/2)`. No empty or degenerate chain passes these hypotheses. | `Formalism/SizeWindowBrackets/SChain.lean : RestSize` |
| gap bound | `ch_top` gives `gapA = ASK − Main ≤ x^(CErr·ε)·errorBracket` from `each_unit_bound_statement`, a proof of `PointwiseBoundVariant`. Its hypotheses: `HidaSetting`, `DIV` (divisor degree bound), `Slopes` / `SlopesN` (upper and lower slope bounds of lattice `M` and quotient `N`), `QuotientSlopeBoundsWith`, `LossBounds`, **`SlopeIneq`**, `HHBound`, `FParams`. | `Development/AutomorphicArithmetic/DedekindLFunctions/LandauTheorems/ChTop.lean`; `Formalism/SizeWindowBrackets/ChainSlopeWindows/LevelOfCongruence.lean:175`; `Formalism/SizeWindowBrackets/QuotientSlopeBoundsWith.lean:72` |
| **slope inequality** | `SlopeIneq` (paraphrase): `s − log|W| − (1−δ)⁻¹·(4·uF·log(1 + HH/uF) + (η + 4√e)·HH) ≤ μ_CC`. That is: a section count `s`, minus an entropy term `log|W|`, minus a height loss, bounds the slope of the dual lattice. This is the shape of a Bost-type slope inequality (Arakelov slope vs. evaluation height). A general Harder–Narasimhan `SlopeIneq` is also stated separately. | `Formalism/RankGapBounds/MeanBoundSecondForm.lean:151`; `Formalism/HarderNarasimhan/Statement.lean:91` |
| **internal QEX** | The author proves `error_sizes_weak_false : ¬ ErrorFormsWeakWindowsFalse`. The error-form bound **fails** under the weaker window hypothesis (`etaBar ≤ 1`, `eBar ≤ 1`). It needs the strong form, which carries `(etaBar + 4√eBar)·x^cHH·b ≤ K·x^ε·nT·a`. The `4√e` there is the same term as in `SlopeIneq`. The development records its own QEX for the weakening, in the same QED/QEX style as this repo. | `Formalism/SizeWindowBrackets/ErrorFormsWeakWindowsFalse.lean`; `Formalism/SizeWindowBrackets/ChainSlopeWindows/SubThreeMulLogTwoLe.lean:471` |

**The proof's main line as now traced (statements only):**

```
SlopeIneq (Bost-type) + slope/divisor bounds
  → ASK − Main ≤ x^{O(ε)}·err   per chain element      (each_unit_bound_statement, ch_top)
  → Gm(x) ≤ x^{1/2+O(ε)}         chain length m ≈ √x    (ch_core, core_gm)
  → zero-free Re s > ½           Landau positivity      (zero_free_of_Chebyshev_growth, level_of_tiedWin)
  → RH / GRH                     reflection s ↔ 1−s     (rh_of_every)
```

**Next target.** Where `SlopeIneq` and the `Slopes` hypotheses are
*discharged* for the actual chain, via `ChainTied` → `TieLocal` (ranks and
slopes of `div.Nu`, `fm.lat`). This is where the theta-lift lattices must
appear, and where the arithmetic content (about 17 M lines) actually lives.

**SUMMARY (slice 4) ok 4 / warn 0 (m=0 resolved) / bug 0**
