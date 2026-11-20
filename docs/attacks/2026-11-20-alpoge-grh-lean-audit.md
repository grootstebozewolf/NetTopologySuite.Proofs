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
