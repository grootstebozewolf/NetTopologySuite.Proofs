<!-- doc-kind: finding
date: 2026-11-20
Provenance: cbd557921d7f4e8c24b40a17734ff2c8c1751b45
Theorems: `LeanSkeletonRebuild.v : critLine`, `LeanSkeletonRebuild.v : zero_free_half`, `LeanSkeletonRebuild.v : no_real_zero_right_of_theta`, `LeanSkeletonRebuild.v : growth_size_bound`, `TowerOrderLawQED.v : ord_large_J`, `TowerOrderLawQED.v : ord_dvd`, `TowerOrderLawQED.v : ord_d`, `SphereNoRelQED.v : orbit_one`, `SphereNoRelQED.v : window_two`
-->
# Alpöge RH/GRH Lean claim: static audit

> External subject: third-party Lean 4 development, mirror `CocoSgt/riemann-hypothesis-lean` @ `7cbf7a0`. `Provenance` pins this repository's commit at which the Rocq probes named in `Theorems` were compiled.

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

## Slice 5: cross-check against the text of `remark.pdf` (2026-11-20)

**Provenance.** The full text of the note was pasted into chat by the user,
who presented it as `remark.pdf`. The agent still cannot reach alpo.ge (the
proxy returns 403), so the text is **user-supplied, not fetched**.
Quotations below are from that paste. This replaces the slice-2b summary as
the source for the author's claims.

| author's claim (quote / paraphrase) | source-code counterpart | verdict |
|---|---|---|
| "a descendant of Stepanov's … multiplicity is hard to find over the integers" | the overall shape of `ch_core` (slice 3) | consistent |
| "for the von Mangoldt sum of length X, Claude's suggested length of chain of theta lifts … was √X" | `RestSize`: `x^(1/2−ε) ≤ m`; `ch_core`: `m ≤ x^(1/2+ε/2)` | **exact match** (slices 3–4) |
| timeline 5: "switch to Λ aka Σ_{n≤X} Λ(n)·(X/n−1)⁺ − X log X + (1+γ)·X" | `Formalism/StatementOC.lean : Gz x = Sz x − x log x + (1+γ)x`, with `Sz x = Σ Λ(n)(x/n − 1)`; also `Formalism.HC.An.G` | **exact match**, symbol for symbol (slice 2) |
| timeline 5: "Guinand–Weil had the sign" | the positivity step is formalized as Landau's theorem (`landau_family`, `zero_free_of_Chebyshev_growth`); the name `Guinand` never appears | consistent in role. The *sign* is the positivity input; the Lean route goes through Landau. Slice 2's label "Landau positivity" stays, with the author's framing noted. |
| timeline 4/6/7: "W(S) ≥ 0 via a determinant … Stepanov with multiplicity one"; "W(…) ≥ 0 gives > 1−η"; GGP periods | `PositivityTheory/`; 266 files mention GGP | consistent; not traced |
| timeline 8: "Iterated theta lifts U(X0) → U(X1) → ··· → U(Xm) between totally definite unitary groups … wins multiplicity m" | `UnitaryGroupThirdPlaceHypotheses`, `DefiniteSideCondition`, `ThetaPairLifts/` (slice 2 chain) | consistent; construction not traced |
| timeline 12: "Seesaw … Bessel period … Rallis" | 3,624 files match Rallis/seesaw; 3,143 match Bessel | present |
| timeline 13: "Bost slope inequality" | `SlopeIneq` in `Formalism/RankGapBounds/MeanBoundSecondForm.lean:151` (slice 4) | **match** (shape) |
| timeline 11/19: "Iwasawa tower … specifically using Behrend!!" | `Formalism/BehrendSets/` (`BehrendVariance`, `TranslateMean`); 14,585 files mention Iwasawa | present |
| timeline 17: "for the classes in H¹(o_E[1/ℓ], Q_ℓ/Z_ℓ(−e)) that we couldn't kill by twisting, fight for a significant weakening of Vandiver" | `VWin`: `Σ_{l∈S} log l · Σ_{1≤e<t} shaLen(ld l, e) ≤ √exp(x^ε)` over fields cut out by ψ (`ExistsPageN.lean`). The name `Vandiver` never appears. | **match** in content. Reading `VWin` as the "Vandiver window" is an inference. |
| timeline 14: "one would stop at 2/3 a priori … need for 'division'" | not located | open |
| "formalized … without assumptions" | static scan clean (steps 4–6); `#print axioms` not run here | unchanged: PENDING |

**Relation to this repo's attack vector.** The note names the invariant: a
*definite sign*, first via a determinant ("W(S) ≥ 0 via a determinant") and
the "definite sign of the left-hand side of qN = Mk + R". It is the analogue
of the question we posed ("what is to RH what orientation is to
coordinates?"). Orientation is also the sign of a determinant. The analogy
holds at the level of the **positivity mechanism**, not the
compact-region/certified-numerics step, which the proof does not use.

**Out of scope, not assessed.** The note's remarks on other groups'
results (Ehrhart, Navier–Stokes, Siegel), the timing, and personal matters.

**SUMMARY (slice 5) ok 9 / warn 0 / bug 0 / open 2** (cost-of-lift "2/3"
step not located; mirror-vs-archive hash still not checked)

## Slice 6: where the slope inequality is supplied for the real chain (2026-11-20)

Read from the mirror source @ `7cbf7a0`, statements and proof skeletons only.

| link | finding | where |
|---|---|---|
| `ChainTied` producer | `linkCore` turns family-level properties into `ChainTied` at every large window point. The properties are `CountF`, `SlopesMF`, `SlopesNF`, `LatF`, `NodesF`, **`FrameF`**, `LossFS`, `CharF`, `WinF`, `ChosenTT/QD/Thin`, `LinkIRR` and `LinkDIV`. | `Formalism/SharpRestriction/GlobalSchurBounds/LossesSmallShares.lean:39` |
| `SlopeIneq` source | Inside `linkCore`, `liftZP_newton : (M.data …).SlopeIneq := M.data_SlopeIneq … hfr`. `hfr` is unpacked from `FrameF` / `Frame_at`. `Frame_at D η e` is the slope inequality itself, stated per datum `D` (`s − log|Word| − (1−δ)⁻¹(4uF·log(1+HH/uF) + (η+4√e)HH) ≤ μ_dual`), with family-uniform `(etaB + 4√eB)·x^CH ≤ 6`. | `…/GlobalSchurBounds/QuadraticLogDerivCongr.lean:188, 258, 699` |
| `FrameF` proof | `frameF_of` derives it from `FrameRealF` (archimedean frame data), `LatF` (lattices), `ChosenProviso`, `ChosenCode` and `NuFullF`. At the call site, `FrameRealF` comes from `frameRealF_of''`, which uses ramification-rank (`ramRankF_of`, crystalline comparison) and matrix-coefficient (`matKF_of`) inputs. | `…/GlobalSchurBounds/TopDensityNGeSixteen.lean:606`; call site `LossesSmallShares.lean` (end) |
| theta inputs | The same call site discharges the slope bounds (`SlopesMF`) via `flipTwoThree.KudlaFamilyStatement` (theta norm, theta condition, stabiliser, injectivity, norm bound). Kudla is the theta-correspondence literature, consistent with remark timeline 8–10 (norms of lifts, divisibility). | `LossesSmallShares.lean`; `Formalism/SharpRestriction/LevelLetterCocycles/StatementFamilies/` |
| naming check: `FamilyTheoremThreeAdmitted` | **Benign.** "Admitted" means *admissible representation* (`Adm3`), not Coq's `Admitted`. It is a `Prop` proved by `stabiliser_family_of_definite` from discrete-series lowest-K-type and Weyl-dimension inputs. | `…/StandardLattice.lean:621`; `…/TheoremThreeFamilyOfFormalDegreeInput.lean:118` |

**Status of the trace.** The main line is now followed from `RiemannHypothesis`
down to the point where the Bost-type slope inequality (`Frame_at`) is
*proved* per datum from lattice, frame and ramification inputs. Below this
point the development fans out into the bulk of the 17 M lines:
theta-lift norms, Kudla-type statements, crystalline comparison and
discrete-series formulas. A per-lemma trace from here is no longer a
meaningful slice by hand. The remaining questions are global ones, answered
by steps 7–9 (build, `#print axioms`, kernel replay), plus the author's
promised write-up for the mathematics.

**SUMMARY (slice 6) ok 4 / warn 0 / bug 0**. Cumulative static trace: no
defect found. Verdict unchanged: **PASS-STATIC / PENDING** (steps 7–10).

## Slice 7: the "stop at 2/3 a priori" item and "division" (2026-11-21)

Closes the slice-5 open item (remark timeline 14: "precise computation of the
'cost' of each lift, showing that one would stop at 2/3 a priori … need for
'division'"). Read from the mirror source @ `7cbf7a0`.

- **No 2/3 exponent is formalized.** There is no `x^(2/3)`; the only
  `two_thirds` hits are `Real.eulerMascheroniConstant_lt_two_thirds`. That is
  expected: the final argument does not stop at 2/3, so the a-priori bound
  never appears as a theorem.
- **"Division" is formalized** as `division_rows_rational_lattice D`. On each
  chain level `i ≤ m`, the Frobenius/Hecke-type operator factors as
  `FFop = Dop ∘ Gs`, with `Gs ∘ GsD = T − Nm`. The Hermitian pairing scales
  as `ipC(FFop φ, FFop ψ) = T^(N_i)·ipC(φ, ψ)`. In words: each lift step
  admits a division by `T`, up to a norm term. It is proved for every datum
  (`UnusedSlot33.division_rational_lattice`, via `finiteModel_of_heckeEstimate`
  and `finite_order_of_totally_real`), and feeds `linkCore` as `s59`
  (audit slice 6).
  - `Development/AbelianVarietyTheory/Definitions/GlobalTwisting/LevelChainSharpColumnValuationOwnChainIff.lean:349`
  - `Formalism/SharpRestriction/GlobalSchurBounds/GlobalRankLatticeProofs/UnitTraceSumBounds/DivisionRationalLattice.lean`
- **Where the cost appears (interpretation).** `ch_core`'s error bracket
  contains `nT·aE·(1 + m²/k)`. The chain cost is quadratic in the chain
  length `m`, and it is divided by the multiplicity/degree `k ≥ x·m`.
  Without that division (`k = O(1)`), the standard balance `X/m + m²` is
  optimal at `m ≈ X^(1/3)`, with error `X^(2/3)`. That is the "stop at 2/3 a
  priori". With `k ≥ x·m`, the quadratic cost becomes `m/x`, and `m ≈ √X`
  becomes affordable.

| item | OUTCOME |
|---|---|
| "2/3 a priori" | **Not formalized, by design** (superseded). Its mechanism is explained by the `m²/k` term. |
| "need for division" | **Located and proved**: `division_rows_rational_lattice` |

**SUMMARY (slice 7) ok 2 / warn 0 / bug 0 / open 0** for the remark
cross-check. The audit verdict is unchanged: **PASS-STATIC / PENDING**. The
remaining opens are the build, `#print axioms`, kernel replay and the archive
hash.

## Slice 8: Rocq rebuild of the logical skeleton from the Lean types (2026-11-21)

Owner instruction: do not install Lean. Read the types and rebuild from Rocq
lemmas within the three-axiom budget (Lean's `propext`, `Classical.choice`,
`Quot.sound`).

**Probe:** `docs/h1-vacuity/LeanSkeletonRebuild.v` (Stdlib, scalars in `Q`,
so the Stdlib-Reals axioms are avoided). The deep facts are **section
hypotheses**, each mirroring a named Lean/Mathlib declaration. The steps
between them are re-proved.

| Rocq theorem | mirrors (Lean) | hypotheses = trusted imports | OUTCOME |
|---|---|---|---|
| `critLine` | `Formalism.VW.critLine` | `L = Λ/Γ` with `Γ ≠ 0` on `Re s > 0` (`LFunction_eq_completed_div_gammaFactor`, `gammaFactor_ne_zero`); FE `Λ(χ,s)=0 → Λ(χ⁻¹,1−s)=0` (`completedLFunction_one_sub`); `prim χ → prim χ⁻¹` (`conductor_inv`); **`EveryCharacter`** | **QED, zero axioms** |
| `rh_strip_of_every` | `Formalism.VW.rh_of_every` (strip form, χ = 1 mod 1) | same | **QED, zero axioms** |
| `exists_small_eps` | `TopWin.lean : exists_small_eps` (for `K ≥ 0`) | none | **QED, zero axioms** |
| `zero_free_half` | `level_of_tiedWin` shape | `zero_free_of_Chebyshev_growth` (Landau); `ch_core`/`core_gm` growth exponent `1/2 + Kε` for all small `ε` | **QED, zero axioms** |

**What this establishes.** Given the trusted imports and the two
development-internal outputs (`EveryCharacter` and the growth bound), the
glue the Lean development uses to reach RH/GRH is sound. It is re-derived
independently of Lean's elaborator and kernel, in a second proof assistant.
The reflection argument matches Lean's, including the choice of the
`Or.inr` (`s ≠ 1`) branch. `Print Assumptions`: *Closed under the global
context* for both main theorems.

**What it does not establish.** The hypotheses themselves. In particular,
`EveryCharacter` and the growth bound are the 17 M-line content. The Mathlib
facts (functional equation, Γ non-vanishing) are standard but are assumed
here, not re-proved. Scalars are `Q`; the real-variable content only enters
through the hypotheses, which is enough for order reasoning but not a
re-proof of analysis.

**SUMMARY (slice 8) ok 4 / warn 0 / bug 0**. Verdict unchanged:
**PASS-STATIC / PENDING**, now with an independent Rocq check of the top-level
glue.

## Slice 9: Rocq rebuild of the tower order law `OrdLargeJ` (2026-11-21)

**Lean type** (`Formalism/BehrendSets/StatementE.lean`):
`OrdLargeJ : ∀ s J l (hl : Coprime l 2^(s+2)), 2 ≤ l → orderOf (frob s l hl) ≤ J → 2^(s+2) ≤ J·(l+1)`,
with `frob` in `(ℤ/2^(s+2))ˣ ⧸ ⟨−1⟩`.

**Translation (definitional).** `frob^k = 1 ⇔ l^k ≡ ±1 (mod 2^(s+2))`. Coprime
to a power of 2 means odd.

**Probe:** `docs/h1-vacuity/TowerOrderLawQED.v`, with **no section
hypotheses**.

| Rocq theorem | statement | OUTCOME |
|---|---|---|
| `lte` | `l` odd, `l ≥ 2`, `k ≥ 1`: `2^n ∣ l^k−1 ⇒ 2^n ≤ k(l+1)`, and `2^n ∣ l^k+1 ⇒ 2^n ≤ l+1` (strong induction on `k`, lifting-the-exponent style) | **QED, zero axioms** |
| `ord_large_J` | integer form of `OrdLargeJ` for every exponent `N` (Lean: `N = s+2`) | **QED, zero axioms** |

**Meaning.** This is the fact behind "every small prime has a long Frobenius
orbit" (root-only ticket, slice 2). With `2^s ≈ x^(2+8ε)`, every prime
`l ≤ x` has orbit length `≳ x^(1+8ε)`. It is now checked independently of
Lean, with nothing assumed beyond the definitional translation above.

**SUMMARY (slice 9) ok 2 / warn 0 / bug 0**. Verdict unchanged:
**PASS-STATIC / PENDING**. Independently re-derived in Rocq so far: the top-level
glue (slice 8), the tower order law (slice 9), and the thick-set construction
(`SphereNoRelQED.v`, root-only ticket).

## Slice 10: Rocq rebuild of the exact order law `OrdDvd` (2026-11-21)

**Lean type** (`Formalism/BehrendSets/StatementE.lean`):
`OrdDvd : ∀ s l j (hl : Coprime l 2^(s+2)), orderOf (frob s l hl) ∣ 2^j ↔ (l ≡ 1 ∨ l ≡ −1 [ZMOD 2^(s+2−j)])`.

**Integer form** (with `frob^(2^j) = 1 ⇔ l^(2^j) ≡ ±1 (mod 2^(s+2))`, and
`N = s+2`): for odd `l` and `1 ≤ j`,
`(2^N ∣ l^(2^j)−1 ∨ 2^N ∣ l^(2^j)+1) ↔ (2^(N−j) ∣ l−1 ∨ 2^(N−j) ∣ l+1)`.
Truncated subtraction is used, as in Lean. The case `j = 0` is the identity.

**Probe:** `docs/h1-vacuity/TowerOrderLawQED.v` (same file as slice 9), with
**no section hypotheses beyond `l` odd**.

| Rocq theorem | statement | OUTCOME |
|---|---|---|
| `val_exact` | `2^n ∣ l^(2^(j+1))−1 ⇔ 2^n ∣ (l²−1)·2^j` (exact 2-adic valuation, induction on `j`) | **QED, zero axioms** |
| `sq_minus_one` | `2^(m+1) ∣ l²−1 ⇔ 2^m ∣ l−1 ∨ 2^m ∣ l+1` | **QED, zero axioms** |
| `ord_dvd` | integer form of `OrdDvd`, all `N`, all `j ≥ 1`, including the edge `N ≤ j+1` | **QED, zero axioms** |

**Meaning.** Together with `ord_large_J` (slice 9), the tower's **explicit
degree function on primes** (root-only ticket, slice 2) is now independently
verified in both directions. These are exactly the facts that make the
ℤ₂-tower the number-field stand-in for `F_{qⁿ}/F_q`.

**SUMMARY (slice 10) ok 3 / warn 0 / bug 0**. Verdict unchanged:
**PASS-STATIC / PENDING**.

## Slice 11: Rocq rebuilds of `OrdD` and `OrbitOne` (2026-11-21)

| Lean type | Rocq theorem (integer form) | probe | OUTCOME |
|---|---|---|---|
| `StatementE.lean : OrdD` (`d % 16 = 7 → orderOf (frob s d) = 2^(s−1)`) | `ord_d`: for `s ≥ 3`, `d^(2^(s−1)) ≡ ±1` and `d^(2^(s−2)) ≢ ±1 (mod 2^(s+2))`. Corollary of `ord_dvd`, since `v₂(d+1) = 3` and `v₂(d−1) = 1`. | `TowerOrderLawQED.v` | **QED, zero axioms** |
| `Statement.lean : OrbitOne` (a short orbit, `addOrderOf h ≤ 8L`, meets `thick n T u` at most once) | `orbit_one`: if `g ∣ n`, `n ≤ 8L·g`, `0 ≤ t < n/(8L)` for both points, `g ∣ x−y`, and `x ≡ t₁+u`, `y ≡ t₂+u (mod n)`, then `x ≡ y (mod n)` | `SphereNoRelQED.v` | **QED, zero axioms** |

**Group translations (definitional, not re-proved).**
- `OrdD`: the order of `frob` is a power of 2 because `OrdGrp s` is cyclic
  of order `2^s`. So "divides `2^(s−1)` but not `2^(s−2)`" means "equals
  `2^(s−1)`". The edge case `s = 2` (`j = 0`) is excluded in the integer
  form.
- `OrbitOne`: the orbit `{t₀ + i·h}` is a coset of `g·ℤ/n` with
  `g = gcd(h,n) = n/addOrderOf h`.

**Meaning.** `ord_d` is why the auxiliary prime `d ≡ 7 (16)` is "inert-like"
(root-only ticket, slice 2). `orbit_one` is the first half of the Behrend
collision control: points of `T + u` lie within `n/(8L)` of each other, and
points of a short orbit are at least `n/(8L)` apart. `WindowTwo` (long
orbits: at most 2 hits per window) is the remaining half, and it is where
`NoRel` / collinearity is used.

**SUMMARY (slice 11) ok 2 / warn 0 / bug 0**. Verdict unchanged:
**PASS-STATIC / PENDING**.

## Slice 12: Rocq rebuild of `WindowTwo`, composed with the sphere set (2026-11-21)

**Lean type** (`Formalism/BehrendSets/Statement.lean`):
`WindowTwo : (∀ t ∈ T, 8Lt < n) → BehrendFree (2L) T → 2L < addOrderOf h → #{i ∈ [j, j+2L) : t₀ + i•h ∈ thick n T u} ≤ 2`.

**Integer form proved** (`SphereNoRelQED.v : window_two`): no three indices
`j ≤ i₁ < i₂ < i₃ < j+2L` all land in `T + u (mod n)`. Hypotheses:
- `0 ≤ t` and `8Lt < n` on `T`;
- **`NoRel` at coefficient size `2L`**, in place of `BehrendFree (2L)`;
- `a·h ≢ 0 (mod n)` for `0 < a ≤ 2L`, which is `2L < addOrderOf h`.

**Proof.**
- Three hits give `n ∣ a(t₃−t₁) − b(t₂−t₁)` with `a = i₂−i₁ < b = i₃−i₁ < 2L`.
- The size bounds give `|·| < n`, so `a(t₃−t₁) = b(t₂−t₁)`.
- If the `t`'s are distinct, that is a `NoRel` relation (collinearity),
  which contradicts the hypothesis.
- If two `t`'s are equal, then `n ∣ a·h` or `n ∣ b·h`, which contradicts the
  order of `h`.

**Finding.** Lean's `WindowTwo` assumes `BehrendFree`. The relation it needs
to exclude is exactly the `NoRel` relation (`j(s₂−s₁) = i(s₃−s₁)`), which is
what `HostThickExists` actually produces. This rebuild shows `NoRel` suffices.

**Composition** (`thick_set_window_two`). The sphere set of
`thick_set_exists`, built with coefficient bound `2L`, has
`d^K ≤ (K(d−1)²+1)·|T|` and satisfies the `WindowTwo` conclusion for every
`n` with `8Lt < n` and every `h` of order `> 2L`. *Closed under the global
context.*

| Rocq theorem | OUTCOME |
|---|---|
| `window_two` | **QED, zero axioms** |
| `thick_set_window_two` (sphere set ⇒ window-two) | **QED, zero axioms** |

**Status of the Behrend collision layer.** It is now rebuilt end to end in
Rocq, with zero axioms:
1. existence with polynomial density (`thick_set_exists`);
2. short orbits hit at most once (`orbit_one`);
3. long orbits hit at most twice per window (`window_two`).

The remaining definitional translations are orbit = coset and
card ≤ 2 = no three distinct.

**SUMMARY (slice 12) ok 2 / warn 0 / bug 0**. Verdict unchanged:
**PASS-STATIC / PENDING**.

## Slice 13: correction. What the positivity actually is, plus its Rocq rebuild (2026-11-21)

**Erratum to slices 2, 2b and 5.** Those slices described the positivity
as "non-negativity of the Dirichlet coefficients of a conjugation-symmetric
combination of `−L'/L`". **That is wrong for the Lean proof.** Reading
`landau_family` / `landau_entire` in full
(`…/TotientGaloisClasses/Landau.lean:115, 380`):

- `landau_family` has **no** coefficient-sign hypothesis. `S` is any finite
  family closed under `χ ↦ χ⁻¹`, and `R ≠ 0` is arbitrary.
- The non-negative object is **`H(x) := C·x^θ − (R·Gz(x) + Σ_S Gchi(x)) ≥ 0`**
  (`hH`). That is the one-sided growth bound itself.
- `landau_entire` is Landau's theorem for **Mellin transforms of
  non-negative functions**. With `P = ζ₁^R·∏_S L(χ)`, the transform satisfies
  `M(σ) = (P'/P(σ) − (a+bσ))/(σ(σ−1)) + C/(σ−θ) = ∫₁^∞ H(x)·x^(−σ−1) dx ≥ 0`
  (`hM`, `PhiP`).
- Closure under `χ ↦ χ⁻¹` is used only to make `P'/P` **real on the real
  axis** (`hi`, `him`), not to make coefficients positive.
- **The sign mechanism.** At a real zero `σ₀ ∈ (θ,1)` of `P` of order
  `m ≥ 1`, `P'/P(σ) = m/(σ−σ₀) + O(1)` tends to `+∞`, while `σ(σ−1) < 0`. So
  `M(σ) → −∞`, which contradicts `M ≥ 0`. The analytic part of
  `landau_entire` (the `lan` iteration) pushes the abscissa down to `θ`.

The overall reading stands: a one-sided bound plus a definite sign gives a
zero-free half-plane. But the sign lives in `H ≥ 0` and the negativity of
`σ(σ−1)` in the strip, not in Dirichlet coefficients. The remark's
"Guinand–Weil had the sign" fits this better than the earlier "Landau
positivity of coefficients" label did.

**Rocq rebuild** (`LeanSkeletonRebuild.v`, Part 3,
`no_real_zero_right_of_theta`). Over `Q`, the identity is cleared of the
positive denominators `u = σ−σ₀`, `σ−θ` and `σ(1−σ)`. The hypothesis is
`(m + r·u)(σ₀+u−θ) ≤ C·u·s(1−s)` (with `s = σ₀+u`, `|r| ≤ B`) for all small
`u > 0`. Under that hypothesis, `0 < θ < σ₀ < 1` and `m > 0` give `False`.
Proof: choose `u ≤ m(σ₀−θ)/(2(B(σ₀−θ)+|C|+1))`. Then the left side is
`≥ m(σ₀−θ)/2`, while the right side is `≤ |C|·u`, which is less than that.

| Rocq theorem | mirrors | OUTCOME |
|---|---|---|
| `no_real_zero_right_of_theta` | sign step of `landau_entire` (real zero ⇒ `M < 0`) | **QED, zero axioms** |

The **translation** (not re-proved) consists of: the Mellin identity
`hM`/`PhiP`, the local expansion of `P'/P` at a zero, and the analytic
continuation iteration `lan` / `landauEq`. These are complex analysis and
stay as trusted Mathlib-level content.

**SUMMARY (slice 13) ok 1 / warn 1 (erratum to slices 2/2b/5, now corrected) / bug 0**.
Verdict unchanged: **PASS-STATIC / PENDING**.

### Slice 13 addendum: where the Euler product enters (2026-11-21)

With the sign relocated to `H ≥ 0`, the Davenport–Heilbronn lesson (symmetry
alone is insufficient) still holds, through a different door. The Mellin
identity needs `Σ_S LSeries(Λ(n)·Re χ(n)) = −P'/P` on `Re s > 1` (`hsumL`,
via `lseries_re`). That is the logarithmic derivative of an **Euler product**.
A function with only a functional equation has no such von Mangoldt
expansion, so `Gz` / `Gchi` would not be its Mellin partners, and the step
from the one-sided bound to zero-freeness would not start.

## Slice 14: Rocq rebuild of the √X balance `GrowthSizeBound` (2026-11-21)

**Lean** (`Formalism/SizeWindowBrackets/GrowthBoundGivesRiemannHypothesis.lean:119`,
proved as `proposition_size_bound`,
`…/ChainSlopeWindows/LipschitzWeightAndMinimum.lean:507`):
`SizeWindows C ε x n nT nT2 m b k aE Err → nT·m·b·((nT2/n)/2)·(Gx − 4x^(1/2+ε)) ≤ Err + 2nT·m·b/x → Gx ≤ x^(1/2+(C+3)ε)`.

This is the lemma that **forces** `m ≈ √x`. After dividing by the main term
`D = nT·m·b·(nT2/n)`, the error splits into:

| term | size | constraint it needs |
|---|---|---|
| `aE`-term `c·nT·aE(1 + m²/k)` | `≈ x^(Cε)·x/m` | `m ≥ x^(1/2−ε)`, i.e. `s ≤ e·m` |
| `2nmb`-term `c·m·2n·m·b·x^ε` | `≈ x^(Cε)·m` | `m ≤ x^(1/2+ε/2)`, i.e. `m ≤ s·e₂` |
| `q₂`-term (`nT2·k·b`…) | `≈ x^(Cε)·x^(1/2+…)` | `k ≤ n²·x^(1/2−ε)` |
| `2nT·m·b/x` | `≈ x^ε/x` | (small) |

Both of the first two terms are `x^(1/2+O(ε))` only when `m = x^(1/2±O(ε))`.
This is the formal content of the remark's "length of chain … √X (And yet,
what else could it be?)".

**Rocq** (`LeanSkeletonRebuild.v`, Part 4, `growth_size_bound`). Over `Q`,
with exponential atoms `s = x^(1/2)`, `e = x^ε`, `e₂ = x^(ε/2)`,
`e₈ = x^(ε/8)`, `c = x^(Cε)`. The target is
`x^(1/2+(C+3)ε) = e₈³·(s·c·e²·e₂·e₈)`. Divisions are named quotients
(`q₁ = m²/k`, `q₂`, `ρ = nT2/n`, `w = 1/x`). Every `SizeWindows` conjunct
appears as a hypothesis, **including Lean's `26 ≤ x^(3ε/8)`**. The bound is
assembled as `4 + 8 + 8 + 4 + 4/3 = 25⅓ ≤ 26`. *Closed under the global
context.*

| Rocq theorem | OUTCOME |
|---|---|
| `growth_size_bound` | **QED, zero axioms** |

The **translation** (not re-proved) is the exponent algebra
`x^(a+b) = x^a·x^b` and monotonicity of `x^·` for `x ≥ 3`. That is how
`SizeWindows`' real powers become the atoms.

**SUMMARY (slice 14) ok 1 / warn 0 / bug 0**. Verdict unchanged:
**PASS-STATIC / PENDING**. The main line now has Rocq rebuilds of:
the √X balance (14), the definite sign (13), the ε-selection and reflection
(8), the tower order laws (9–11) and the thick-set layer (root-only ticket,
12). The Mathlib analysis and the slope/theta content of `ch_top` /
`Frame_at` remain trusted.
