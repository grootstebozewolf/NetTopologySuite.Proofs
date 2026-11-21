<!-- doc-kind: finding
date: 2026-11-21
Provenance: ebe823e
Theorems: `LeanSkeletonRebuild.v : masullo_right_of_half`, `LeanSkeletonRebuild.v : masullo_critLine`
-->
# Masullo's GRH draft ("The Music of the Primes") against the Alpöge main line

**Subject.** A. M. Masullo, *The Music of the Primes* (draft of 2026-11-20,
940 pp.).
- Announced by R. Vakil at
  `math216.wordpress.com/2026/11/20/hurried-announcement-alessandro-masullo-grh/`.
- Read from the copy mirrored unmodified in the public formalization project
  `mccorvie/riemann-masullo` @ `4a5f441`. The PDF's sha256 is
  `e039d3f6…97bf5`, as recorded there. We used `paper/the-music-of-the-primes.txt`,
  a `pdftotext` extraction.
- The blog host itself is blocked from this container. The text was **not**
  fetched from Vakil's site, and nothing here was checked against the PDF
  layout.

**Scope.** Strategy comparison only, using the questions that structured the
Alpöge audit (`2026-11-20-alpoge-grh-lean-audit.md`). Read: Chapter 1 (§§1.1,
1.4, 1.5, 1.7), the Chapter 13 skeleton, the statement of Theorem 12.5.1.1, and
the project's README / ERRATA. **Not read:** the 400+ pages of Chapters 2–12
where the trace formula is proved.

## What the draft claims and how GRH is deduced

- **Claim.** GRH for Hecke L-functions of unitary characters over **every
  number field**. That is wider than Alpöge's release, which covers Dirichlet
  L-functions; the project's `Statements.lean` adds `DedekindZetaZerosOnLine`
  and `HeckeLZerosOnLine` for this.
- **Engine: a trace formula** (Theorem 12.5.1.1, restated as Theorem 13.3.1.1).
  - It holds on Hardy–Sobolev spaces `W^{s,2}_I(C_F)`. These are completions
    of exponentially decaying Schwartz–Bruhat functions on the idele class
    group under `‖φ‖ = (∫ |φ|² max(|g|^{2a}, |g|^{2b}) (1+|log|g||²)^{s/2})^{1/2}`,
    with base `I = [a, b]`.
  - The geometric side is the Weil/Connes local terms (archimedean integrals,
    plus `Σ_v log q_v Σ_m χ(π_v^m) q_v^{-m/2} φ(q_v^{±m})`).
  - The **spectral side sums only the zeros `ρ` with `ρ − 1/2` in the strip
    `C_I`**, weighted by `N_spec(ρ) = min(N(ρ), [F:Q])` (§13.3.1).
- **Deduction (§1.4.2–1.4.5).**
  1. Take `I = [−a, a]` and test functions `φ_z(t) = t^{−z}` on `(1, ∞)`,
     mollified.
  2. Montel's theorem gives a holomorphic limit, and the finite-place sum
     tends to `L'_f/L_f(s + 1/2, χ)`.
  3. So `L'_f/L_f(s+1/2, χ)` is holomorphic on `Re s > a`, apart from
     `s = 1/2` in the trivial-character case.
  4. Since `a > 0` is arbitrary, there are no zeros with `Re s > 1/2`, and the
     functional equation handles `Re s < 1/2`.
- **Relation to Connes.** §1.5.1 says Connes' spectral interpretation is the
  special case `I = {0}`, with Connes' `δ` equal to the Sobolev degree `s`. The
  stated novelty is computing the trace through **periodic/orbital Schauder
  bases** on orbital subquotients of spaces of adelic θ-functions. This
  replaces Meyer's operator-theoretic Euler products, which only converge in
  the finer bornological topology, and under which all zeros, wherever they
  lie, contribute.

## Comparison on the audit's four questions

| question | Alpöge (Lean, with Claude) | Masullo (draft) |
|---|---|---|
| **Definite sign?** | Yes, explicitly: `H = C·x^θ − G(x) ≥ 0` together with Landau's theorem for Mellin transforms, and `σ(σ−1) < 0` in the strip (audit slice 13) | **None as a separate step.** The weight `max(\|g\|^{2a}, \|g\|^{2b})` confines the trace formula's spectral side to the strip `C_I`. The whole burden is the **validity of the trace formula on `W_I` for arbitrarily small `a`**. Positivity is not invoked in the deduction (§1.4.5). |
| **Where the Euler product enters** | Mellin identity `hsumL` (slice 13 addendum) | The finite-place geometric terms, whose sum "approximates `L'_f/L_f`" (§1.4.3–1.4.4), plus an "approximate, weaker version of the Euler product convergence" (§1.5.1). Both pass the Davenport–Heilbronn test in kind: each uses the Hecke L-function's Euler product. |
| **Multiplicity / "all `qⁿ`" stand-in** | theta-lift chain of length `√X` (`ch_core`, the `GrowthSizeBound` window); ℤ₂-tower degree function (`OrdDvd`, `OrdLargeJ`) | **Different meaning.** "Multiplicity" is isotypic multiplicity of Schauder bases (Ch. 4.6), and the zero multiplicity `N(ρ)` is capped at `[F:Q]` on the spectral side. No tower and no chain. Archimedean places and the ℚ-linear independence of `log p` are credited instead (§1.7.1), as the reason the method gives "yes" for number fields but not function fields. |
| **Rebuildable finite piece?** | several (`TowerOrderLawQED.v`, `SphereNoRelQED.v`, `LeanSkeletonRebuild.v`) | Only the §1.4.5 deduction (holomorphy on `C_{>a}` for all `a > 0` ⇒ zero-free `Re s > 1/2`) is an order-theoretic skeleton, the same shape as `zero_free_half`. The core is topological vector space and analysis (nuclear LF-spaces, Schauder bases, trace-class operators). |

**Reading (not a theorem).** The two claims are **structurally different
routes**:
- Alpöge proves a *one-sided growth bound* (`Gm(x) ≤ x^{1/2+ε}`) by arithmetic
  multiplicity, then converts it with a sign.
- Masullo asserts a *spectrally confined trace formula*. Connes showed that a
  trace formula of this kind on his `L²_δ` is equivalent to RH, through Weil
  positivity, so its validity carries essentially all of the content.

Masullo's route therefore stands or falls with Theorem 12.5.1.1. That is
exactly where the public concerns sit (below).

## Status, as the sources say

- **Unfinished by the author's account.** Chapter 13 is a skeleton: §§13.1–13.2
  are bare headings, and §13.3 only restates the trace formula. The
  formalization project notes the chapter "does not yet state its main
  theorem". The preface (per ERRATA) mentions "several glitches" being fixed
  with B. Conrad.
- **Concerns about the main theorem.** The concerns about Theorem 12.5.1.1 come
  from the Lean Zulip thread "Formalising Masullo's proof of GRH" (per the
  project README; details not posted). News coverage reports an objection about
  a Markushevich-basis claim on p. 444. The draft uses "Markushevich" 83 times;
  the specific objection was not checked here.
- **Formalization so far.** It has reached only the appendices and early
  chapters. ERRATA lists 11 "false as stated" items and 27+ imprecisions, all in
  standard background (restricted products, nuclear spaces, trace-class
  lemmas). Examples:
  - F8: `Σ_φ |⟨Tφ,φ⟩|` depends on the basis, e.g. for `T = diag(1,−1)`.
  - F9: `|AT|_Tr = |TA|_Tr` fails.

  None of the listed items touches the trace formula. Most were AI-reported,
  and none is specialist-reviewed (per ERRATA's own `Checked` column).

## OUTCOME

**READ / NOT ASSESSED.**
- The strategy is located: a Connes-type trace formula on Hardy–Sobolev spaces
  with exponential weights, computed through orbital Schauder bases.
- The deduction of GRH from the trace formula (§1.4) is short and standard in
  shape.
- No judgement is made on Theorem 12.5.1.1, which carries the content. The
  draft is unverified and unfinished, as the author says.
- Compared with Alpöge's claim: neither is an accepted theorem. Alpöge's is
  machine-checkable but unread; Masullo's is readable but unfinished and
  unformalized.

**SUMMARY ok 3 / warn 2 / bug 0.**
- ok: strategy located; Euler-product test passed in kind; deduction skeleton
  identified.
- warn: Chapter 13 is unfinished; the main theorem is publicly disputed.

Possible next probe: rebuild the §1.4.5 deduction in `LeanSkeletonRebuild.v`
style (holomorphy of `L'/L` on `C_{>a}` for every `a > 0`, plus the functional
equation, gives zero-freeness off the line) from named hypotheses. It would be
cheap, and it would make the comparison with `zero_free_half` exact.

## Slice 2: the §1.4.5 deduction rebuilt in Rocq (2026-11-21)

`LeanSkeletonRebuild.v`, Part 5. The Trace Formula consequence enters as a
named hypothesis `TF`: for every `a > 0`, a zero at `w` with
`Re w > 1/2 + a` is impossible (a zero would be a pole of `L'/L`), unless
`χ` is trivial and `w = 1`. The functional equation enters as in Part 1.

| Rocq theorem | mirrors | OUTCOME |
|---|---|---|
| `masullo_right_of_half` | "since `a > 0` is arbitrary" (§1.4.5): choose `a = (Re w − 1/2)/2` | **QED, zero axioms** (conditional on `TF`) |
| `masullo_critLine` | "by the functional equation the same holds over `C_{<1/2}`" | **QED, zero axioms** (conditional on `TF`, FE) |

**What the side-by-side shows.**

| | Alpöge glue (`zero_free_half`, `critLine`) | Masullo glue (`masullo_critLine`) |
|---|---|---|
| assumed core | `ch_core` growth `Gm(x) ≤ x^(1/2+Kε)` for all small `ε`, plus Landau (sign) | `TF`: a zero-free `Re w > 1/2 + a` for every `a > 0` |
| where `1/2` enters | the growth exponent | the centre of the strip `I = [−a, a]` |
| sign step | yes (`no_real_zero_right_of_theta`) | none |
| reflection | identical | identical |

The two glues are equally short. In both, `1/2` is an **input**: Alpöge
derives it from the √X window (`growth_size_bound`, where the window is itself
a hypothesis), and Masullo builds it into the weights. The difference lies
entirely in the assumed core. `TF` for all `a > 0` is already the statement
"zero-free right of `1/2 + a` for every `a`", so `masullo_right_of_half` is
almost definitional. That makes concrete the reading above: Masullo's route
puts essentially all of the content in Theorem 12.5.1.1, while Alpöge's splits
it into a growth bound and a sign.

**SUMMARY (slice 2) ok 2 / warn 0 / bug 0.**
