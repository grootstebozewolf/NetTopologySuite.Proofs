<!-- doc-kind: hunt-ticket
date: 2026-11-20
Provenance: external artifact — CocoSgt/riemann-hypothesis-lean @ 7cbf7a0 (mirror of Alpöge's Lean archive); companion to `2026-11-20-alpoge-grh-lean-audit.md`
Theorems: none in this repo — claims about a third-party Lean 4 development
-->
# Root-only multiplicity: does ζ need the canopy?

**Question.** In the claimed RH/GRH proof, the ζ case is extracted from the
general one. Does the ζ case *need* the general (auxiliary-character,
auxiliary-field) machinery? Or is there a "root-only" route to the √X
multiplicity that sees only ζ?

This ticket tests the owner's intuition from chat (2026-11-20): a stable
root-level route connects to the root of the canopy rather than only to the
generalized canopy. It records what the current proof actually uses at the
root. That gives the claim a QED/QEX shape.

## What the ζ case uses today (read from source, statements only)

| layer | what ζ needs | where |
|---|---|---|
| extraction | only `χ = 1 mod 1`: `rh_of_every` applies `EveryCharacter` at `N = 1` and rewrites with `LFunction_modOne_eq` | `Formalism/GammaFactorNonvanishing/CritLine.lean` |
| positivity (Landau) | **root-only.** `Level.cyc ψ := Level.ofSub (zpowers ψ.χ)`; for ψ = 1 the family is `{1}`. The sign mechanism needs no other L-function. | `Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ExplicitFormulaErrorOfHostConditions.lean:121` |
| √X growth bound (`ChainTied` → `ch_core`) | **canopy.** The chain lives in host data with conductor `QS·q·d` (`InertiaGaloisSymmetry/OfChar.lean : cyc`), auxiliary primes `q ≡ 3 (8)`, `d ≡ 7 (16)` with `log q ≈ Y^(ε/5)` (`WinPair`), theta lifts with Hecke characters, and the Kudla-type, crystalline and discrete-series inputs of audit slice 6 | audit slices 3–6 |
| Vandiver-type input (`VWin`) | **canopy, growing.** Even for ψ = 1, `IsChiField ψ e q d E` cuts `E` out of a cyclotomic field with `2^(e+2) ∣ N`, where `PageN` forces `2^e ≈ x^(2+8ε)`. So it is a 2-power **Iwasawa tower** whose height grows like `(2+8ε)·log₂ x`, with quadratic conditions at `q`, `d`. The bound is on `Σ_l log l · Σ_e shaLen` over those fields. | `Development/AutomorphicArithmetic/CharacterBoxes/ExistsPageN.lean` |

So, in the current proof, **the sign is root-level and the multiplicity is
not**. For ζ alone, the √X multiplicity is bought with fields of degree
≈ x² and auxiliary primes of size exp(x^(ε/5)).

## Claims

| id | claim | OUTCOME |
|---|---|---|
| R1 | The positivity (Landau) step for ζ uses only ζ | **QED (by reading)**: family `Level.cyc 1 = {1}` |
| R2 | The current √X multiplicity for ζ uses auxiliary characters and fields | **QED (by reading)**: conductor `QS·q·d`, `WinPair`, `IsChiField` with a 2-power tower |
| R3 | **Root-only multiplicity.** A chain of length ≈ √X with multiplicity `k ≥ X·m` satisfying `ch_core`'s hypotheses can be built from ζ-level (or ℚ-level) data alone, with no auxiliary characters or growing fields | **OPEN** |
| R3-QED | Witness: a construction meeting `RestSize` + `SizesA` + `gapA` bounds without `q`, `d` or the tower | open |
| R3-QEX | Obstruction: a ζ-only datum class provably *cannot* meet `RestSize` (`x^(1/2−ε) ≤ m`, `k ≤ n²·x^(1/2−ε)`). For example, `n = |H| ≳ x^(1/2)` forces a group that ζ alone does not supply. That would show the canopy is essential, as the Euler product is in the Davenport–Heilbronn lesson. | open |

## First probe (cheap, falsifiable)

`RestSize` + `ch_core` force `|H| = n ≳ x^(1/2)` (audit slice 4). Ask:

- What finite abelian group `H` does the actual chain use for ψ = 1? Trace
  `ChainTied`'s `(Fm.D x i0).R.A` back to its definition.
- Is its size driven by `q`, `d` or the tower?

If `H` is forced to come from the auxiliary conductor, R3 is reduced to "find
a ζ-level group of size ≳ √x carrying the same divisor/slope data". That is a
sharper target than "simplify the proof".

## Probe result: the group `H` (2026-11-20, read from source)

- In `ChainTied`, `H = (Fm.D x i0).R.A = φ.A` for a `Formalism.HC.Frame` φ.
  It is a finite abelian group carrying a **surjection**
  `φ.h : φ.A →+ HGrp e`.
- `HGrp e := (ZMod 2^(e+2))ˣ ⧸ ⟨−1⟩ ≅ Gal(ℚ(ζ_{2^(e+2)})⁺/ℚ)`, which is cyclic
  of order `2^e`. It is the `e`-th layer of the **cyclotomic ℤ₂-extension of
  ℚ**.
  - `Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ZsmulGeneratorEqZeroOfProjection.lean : Frame`
  - `Formalism/FrobeniusOrbits/Statement.lean:24 : HGrp`
- `PageN` forces `2^e ≈ x^(2+8ε)`, so `|H| ≥ 2^e ≈ x²`. That comfortably
  meets `RestSize`'s `n ≳ √x`. The **size** of `H` is driven by the 2-power
  tower, not by the auxiliary primes `q`, `d`.

**What this says about R3.**

1. The group the multiplicity lives on is **ℚ-canonical**: a layer of the
   cyclotomic ℤ₂-tower of ℚ, with no auxiliary choice. In that narrow sense the
   chain's "space" is root-level.
2. Its characters, however, are the even Dirichlet characters of 2-power
   conductor. Using `H` means using that whole family of L-functions. The
   canopy re-enters as the dual of `H`.
3. **Function-field analogy** (remark timeline 11: "Iwasawa tower via
   analogy to pigeonhole on F_{qⁿ}/F_q"). The tower plays the role of the
   constant-field extensions `F_{qⁿ}`. Over function fields, a Stepanov bound
   at a single `n` does not give RH: one needs all `n` (or the rationality of
   ζ) to pass from a `√q` bound to the eigenvalues. By that analogy the tower
   is **essential**, not decorative. That leans R3 towards QEX *for routes
   without a tower*, and re-aims R3-QED at the question: does ζ admit a
   tower-free substitute for "all n"?

**OUTCOME** OPEN, sharpened. R1 and R2 are QED by reading. The `H` probe
shows the multiplicity group is the ℤ₂-tower layer
(`|H| ≥ 2^e ≈ x^(2+8ε)`). The function-field analogy suggests R3-QEX for
tower-free routes. A root-only route must supply a substitute for
constant-field extension, not merely avoid auxiliary characters.

## Slice 2: what the tower does, the "all n" substitute (2026-11-20)

Read from `Formalism/BehrendSets/{Statement,StatementE}.lean` in the mirror
@ `7cbf7a0`. This is a reading of statements; the interpretation is marked.

| fact (paraphrase) | name |
|---|---|
| `OrdGrp s := (ℤ/2^(s+2))ˣ/±1`, cyclic of order `2^s`. `frob s l` is the Frobenius of a prime `l` in it. | `OrdGrp`, `frob`, `OrdCard` |
| Explicit order law: `ord(frob l) ∣ 2^j ⇔ l ≡ ±1 (mod 2^(s+2−j))` | `OrdIff`, `OrdDvd` |
| Short orbits need large primes: `ord(frob l) ≤ J ⇒ 2^(s+2) ≤ J·(l+1)`. With `2^s ≈ x^(2+8ε)`, every prime `l ≤ x` has orbit length `≳ x^(1+8ε)`. | `OrdLargeJ`, `ShortOrdLarge` |
| The auxiliary prime `d ≡ 7 (16)` has maximal order `2^(s−1)` (inert-like) | `OrdD` |
| Primes with short orbits are sparse: `Σ log l / l^2` and `Σ log l / l` over them are bounded | `ShortOrdSq`, `ShortOrdLin`, `OrdSqJ` |
| A **Behrend-free** "thick" set `T ⊂ ℤ/n` (no nontrivial `α x₁ + β x₂ + γ x₃ = 0` with coefficients `≤ 2L`), of size `n/(8L)·exp(−C√(log n · log L))`. Each orbit window of length `2L` meets a translate of `T` **at most twice**, and short orbits at most once. Random-subset selection (`Select`, `BadOrbit`) controls the rest. | `BehrendFree`, `ThickSet`, `WindowTwo`, `OrbitOne`, `Select` |

**Interpretation.** The tower supplies a **degree function on primes**:
`deg(l) := ord(frob l)` in a cyclic 2-group. It is explicit (by `OrdIff`)
and large for every prime up to `x`. This is the number-field stand-in for
"pass to `F_{qⁿ}` with `n` so large that every closed point of small norm has
large degree". That is the pigeonhole on `F_{qⁿ}/F_q` from remark timeline
11. The Behrend set then caps how often a Frobenius orbit can hit the
chosen positions. That cap is a bounded multiplicity of collisions, which is
what keeps the √X chain's multiplicity count honest. Behrend is the
"precise choice of the Iwasawa tower" of timeline 19, which the author
expects to be unnecessary.

**Consequence for R3 (by reasoning, not code).** Whatever replaces the
tower must give primes an explicit, long-orbit "degree" in a finite group,
compatible with Frobenius. If the replacement is **abelian over ℚ**, then by
class field theory (Kronecker–Weber) it is a subfield of a cyclotomic field.
Its Frobenius degrees are read off Dirichlet characters, so the canopy comes
back automatically.

| id | claim | OUTCOME |
|---|---|---|
| R3a | The tower's role is an explicit long-orbit degree function on primes `≤ x` (with Behrend collision control) | **QED (by reading)** |
| R3b | Any *abelian* tower-free substitute for R3a is cyclotomic, so it is not root-only | **QEX-leaning (by Kronecker–Weber; argument, not formalized)** |
| R3c | A root-only route must use a **non-abelian** (or non-Galois) degree structure, or avoid degree functions entirely (a different source of multiplicity) | **OPEN, the sharpened target** |

**OUTCOME** OPEN. R3 is narrowed to R3c. Abelian substitutes lead back into
the canopy (R3b). Note that a non-abelian degree structure would bring in
higher-rank L-functions, which is a bigger canopy, not a smaller one. That is
weak evidence that "root-only" may be the wrong goal, and that "smallest
sufficient canopy" (for example, a single cyclotomic layer without Behrend) is
the better-posed simplification target.

## Slice 3: is Behrend load-bearing? (smallest-sufficient-canopy probe, 2026-11-20)

**Import closure** (script: Python over `import` lines; Mathlib, Lean and Std
excluded). `Main.lean` transitively imports **all 175,187** `.lean` files
(17,374,215 lines); none is unreachable. Import reachability is not
proof-term dependency. Measuring which declarations the proof terms actually
use needs a build (audit steps 7–8), so "how much of the 17 M lines is
really used" stays open.

**Behrend on the main line (read from source).**

- `linkCore` receives `WinF` from
  `size_windows_of_thick_density Fm cT2`, which needs
  `ThickSetDensityEventually`.
  (`…/GlobalSchurBounds/LossesSmallShares.lean:315`,
  `…/WeightVectorSmallSharesSeven.lean:41`)
- That density comes from `thickFrame2`-type statements, which call
  `Formalism.FrobeniusOrbits.hostThickExists`. That is a Behrend-type
  existence proof: a set `T ⊂ [0, n/(4L))` with `NoRel T L`, meaning no
  `j(s₂−s₁) = i(s₃−s₁)` with `0 < |i|,|j| ≤ L` and `i ≠ j`, and
  `|T| ≥ n·exp(−C√(log n·log L))/L`.
  (`Development/AutomorphicArithmetic/ThickFrames/ThickFrame2Large.lean:37`;
  `Formalism/FrobeniusOrbits/HostThickExists.lean`;
  `…/FrobeniusOrbitsProofs/ThickExists.lean:181`)
- What is actually demanded downstream: with `Lw ≤ CL·log x`, a `NoRel`
  set `T2` with **`|T2| ≥ x^(−ε)·ord`**. This is `RestSize`'s
  `x^(−ε) ≤ nT2/n`. Behrend's loss `exp(−C√(log n·log log x))` is
  `x^(o(1))`, which is far better than the `x^(−ε)` needed.
- `Formalism/BehrendSets/` itself is imported only by
  `Formalism/GL3MeanSquares/HookFormulaTorsion/DifferenceStableUnderAction.lean`.
  The main-line use is the `FrobeniusOrbits` copy.

**Can something simpler than Behrend do it? (argument, not code)**

- *Random set with deletion:* **fails.** It has about `n²L²` relation
  triples, so density `δ` leaves `≈ n²L²δ³` bad triples against `nδ`
  points. That forces `δ ≲ 1/(√n·L)`, a density of `n^(−1/2)`, far below
  `x^(−ε)`.
- *Powers / lacunary sets* (for example `{(3L)^i}`): `NoRel` holds, but
  the size is only `O(log n)`. **Fails** badly.
- *Naive digit restriction:* it prevents carries but not relations within a
  digit. It is **not sufficient by itself**.
- So a *structured* set with no linear relations is genuinely needed:
  density `x^(−ε)` against relations with coefficients up to `log x`.
  Behrend's sphere trick is the standard route. The exponent `√` loss is
  overkill, but **some** Behrend-/Salem–Spencer-type construction appears
  necessary.

| id | claim | OUTCOME |
|---|---|---|
| S1 | Behrend-type `NoRel` sets are on the main line (feeding `WinF` → `linkCore` → `ChainTied`) | **QED (by reading)** |
| S2 | The requirement is only density `x^(−ε)` at coefficient size `O(log x)`. Behrend's `exp(−C√…)` quality is not needed. | **QED (by reading `RestSize`, `thickFrame2`)** |
| S3 | Unstructured constructions (random deletion, lacunary) cannot meet S2 | **QED-leaning (counting argument above; not formalized)** |
| S4 | A construction simpler than Behrend meets S2 | **OPEN.** This is a small, self-contained, formalizable target: a pure additive-combinatorics lemma with no RH content. It is the first concrete "smallest canopy" simplification candidate. |

**OUTCOME** OPEN. The Behrend step is load-bearing in kind, but over-powered
in quality. S4 is a cheap, well-posed probe. A positive answer would simplify
the formalization, but it would **not** shrink the canopy (the ℤ₂-tower stays).

## Slice 4: S4 answered. Behrend's sphere *is* the simple construction (2026-11-20)

**Observation.** Write `s = Σ_k a_k b^k` with digit vector `a ∈ [0,d)^K`.
If `2(|i|+|j|)·d < b`, the relation `j(s₂−s₁) = i(s₃−s₁)` has no carries. It
holds **iff** it holds coordinate-wise: `j(a₂−a₁) = i(a₃−a₁)`. With
`i ≠ j` and `i, j ≠ 0`, that says the three digit vectors are **collinear**.
`NoRel` is therefore a "no three collinear points" condition, an
orientation-zero predicate in this repo's own vocabulary. Behrend's choice
(all digit vectors on one sphere `|a|² = r`) works because a sphere is
strictly convex.

**Probe (QED, machine-checked):** `docs/h1-vacuity/SphereNoRelQED.v`,
Stdlib only, `Print Assumptions` → *Closed under the global context*.

- `sphere_no_collinear`: distinct points of one integer sphere satisfy no
  `j(a₂−a₁) = i(a₃−a₁)` with `i, j ≠ 0`, `i ≠ j`. This is pure algebra:
  expand `|a₁+u|² = |a₁|²`, then `j(j−i)·|u|² = 0`.
- `eval_zero_digits`: balanced base-b digits with `2B < b` that evaluate to 0
  are all 0.
- `sphere_digits_norel`: the two combined. Numbers whose digit vectors lie on
  one sphere satisfy `NoRel` whenever `2(|i|+|j|)·d < b`.

**Density with crude parameters (argument, not formalized).** Take
`L ≈ log x`, base `b ≈ (8L)^(1/ε')`, digits `[0, d)` with `d ≈ b/(8L)`, and
`K = log N / log b` digits. Pigeonhole over the `≤ K·d²` sphere radii gives
a sphere slice of size `≥ d^K/(K·d²)`. Relative to `N = b^K`, the density is
`(8L)^(−K)/(K d²) = N^(−ε')·N^(−o(1))`. That meets the `x^(−ε)` demand of S2
**without** Behrend's √-optimisation.

| id | claim | OUTCOME |
|---|---|---|
| S4 | A construction simpler than optimised Behrend meets S2 | **Answered.** The construction is the same (the sphere), but parameter choice and analysis are much simpler: a fixed large base `(8L)^(1/ε')` instead of the √ trade-off. Correctness is **QED** in Rocq; the density count is an argument. |
| S5 | Something *structurally* different from strict convexity avoids `NoRel` relations at density `x^(−ε)` | OPEN (and probably not worth pursuing: S3 rules out unstructured sets, and strict convexity is the minimal structure that kills collinearity) |

**Takeaway.** The "Behrend!!" step that Alpöge expects to be unnecessary is,
at its core, **orientation**: a no-three-collinear condition guaranteed by
strict convexity. The optimised Behrend bound is unnecessary. The geometric
idea is not.

**OUTCOME** OPEN overall (R3c stands). S4 answered with a machine-checked
core.

### Slice 4b: density formalized (2026-11-20)

`SphereNoRelQED.v` now also proves `sphere_slice_large`: some sphere slice
`S_r ⊂ [0,d)^K` has `(K(d−1)² + 1)·|S_r| ≥ d^K`. It uses a generic pigeonhole
(`pigeon`) over the enumerated cube (`allvec`, `|allvec K d| = d^K`). Both
`sphere_digits_norel` (correctness) and `sphere_slice_large` (density) are
*Closed under the global context*.

The only remaining unformalized step is the final arithmetic: with
`b ≈ (8L)^(1/ε')` and `d ≈ b/(8L)`, the slice's density in `[0, b^K)` is
`N^(−ε'−o(1))`.

| id | claim | OUTCOME |
|---|---|---|
| S4 | correctness and density of the crude sphere construction | **QED** (Rocq) except the final exponent arithmetic, which is routine |

### Slice 4c: packaged `thick_set_exists` (2026-11-20)

`SphereNoRelQED.v : thick_set_exists` is an integer analogue of the external
`Formalism/FrobeniusOrbits/HostThickExists.lean : HostThickExists`. Given
`1 ≤ L` and `4Ld < b`, there is a duplicate-free `T ⊂ [0, b^K)` with
`NoRel T L` and `d^K ≤ (K(d−1)²+1)·|T|`. With `b = c·d`, that is
`|T| ≥ b^K / (c^K·(Kd²+1))`, a **polynomial** loss in place of
`exp(−C√(log n·log L))`. *Closed under the global context.*

The only prose step left is reading `c^K = N^(log c / log b)`, i.e. choosing
`b ≈ (8L)^(1/ε')`.

| id | claim | OUTCOME |
|---|---|---|
| S4 | a crude sphere construction meets the downstream demand (density `x^(−ε)`, `L = O(log x)`) | **QED** (Rocq, `thick_set_exists`) modulo the exponent reading above |
