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
