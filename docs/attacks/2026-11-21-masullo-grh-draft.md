<!-- doc-kind: finding
date: 2026-11-21
Provenance: 0a8eb14
Theorems: `LeanSkeletonRebuild.v : masullo_right_of_half`, `LeanSkeletonRebuild.v : masullo_critLine`, `MarkushevichBoundQEX.v : block_qex`, `MarkushevichBoundQEX.v : no_uniform_bound`, `MarkushevichBoundQEX.v : small_gap`, `MarkushevichBoundQEX.v : psi_unbounded`, `MarkushevichBoundQEX.v : direct_sum_qex`
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

## Slice 3: the p. 444 Markushevich inference (QEX), and where it is used (2026-11-21)

**The claim.** Terminology 10.2.1.2(2), p. 444, defines a Markushevich basis
`{(x_m, f_m)}` of a Banach space as "Regular, if and only if
`{x_m} ⊂ E` is strictly bounded away from `0 ∈ E`. **In particular,
`{f_m} ⊂ E'_β` is bounded.**"

**It is used.**
- Corollary 10.2.1.4 (p. 444) and Corollary 10.2.2.3 (p. 447) conclude
  "regular and bounded, hence normalized" for the draft's spectral bases
  `η_{χ,t,m}(g) = χ(g)|g|^{it}_F (log|g|_F)^m`.
- p. 451 (§10.3, spectral nuclearity): "The existence of C is ensured by the
  Markushevich basis … and hence its bi-orthogonal sequence {ψ}, being
  normalized (see Terminology 10.2.1.2), which implies that C can be chosen to
  be independent of m′ … (k, j)".
- p. 468 (§10.4.3, the spectral side of the Trace Formula) cites the same
  normalization (Corollary 10.2.1.4).

**QEX (machine-checked).** `docs/h1-vacuity/MarkushevichBoundQEX.v`
(Stdlib, `Q`, no hypotheses), *Closed under the global context*:

| Rocq theorem | statement | OUTCOME |
|---|---|---|
| `block_qex` | For every `B ≥ 0` there is a biorthogonal pair in `Q²`: `x₁ = (1,0)`, `x₂ = (1,ε)`, `f₁ = (1,−1/ε)`, `f₂ = (0,1/ε)`, with `ε = 1/(B+1)` and `1 ≤ ‖x_i‖² ≤ 2`, yet `f₂(e₂) = B+1 > B` on the unit vector `e₂`. | **QED, zero axioms**. The ℓ² direct sum of these blocks (`ε_k → 0`) is a bounded, regular Markushevich basis with unbounded `{f_m}`, so **the inference is false in general**. The direct-sum assembly is standard and not re-proved. |
| `close_pair_lower` / `no_uniform_bound` | If `f(x) = 1`, `f(x') = 0` and `\|f(v)\| ≤ B·N(v)`, then `1 ≤ B·N(x − x')`. A biorthogonal system with pairs at arbitrarily small distance has no uniform bound. | **QED, zero axioms** |

For **Schauder** bases the inference does hold, through the basis constant
(`‖f_m‖ ≤ 2K/‖x_m‖`). The draft's own Remark 10.2.1.5 says these spectral
bases are **not** Schauder bases.

**Application to the draft's basis (argument, not formalized; for a
specialist to check).**
- For `s > 1`, `‖η_{χ,t,0} − η_{χ,t',0}‖_{−s,2}² = ∫ |e^{itu} − e^{it'u}|² (1+u²)^{−s/2} du ≤ ∫ min(4, |t−t'|²u²)(1+u²)^{−s/2} du`,
  which tends to `0` as `|t − t'| → 0`, uniformly in `t`.
- So on any line that carries infinitely many zeros whose ordinates have
  **arbitrarily small gaps**, `no_uniform_bound` applies, and the
  bi-orthogonal norms `‖ψ_{χ,t,0}‖` are unbounded.
- The critical line is such a line, unconditionally: Selberg's positive
  proportion gives `N₀(T) ≫ T log T` zeros on it up to height `T`, so the
  average gap tends to 0.
- Whether the "a-lines" in §§10.2–10.4 include a line of that kind depends on
  the draft's normalization of `s` (`χ|·|^s` versus a `ρ − 1/2` shift). That was
  not determined here.
- If they do, the uniform constant `C` claimed on p. 451 does not exist as
  stated, and the step needs another justification.

This independently confirms that the publicly reported p. 444 objection is a
**genuine gap in the stated inference**. Whether it is **fatal** depends on
whether pp. 451/468 can be repaired, for example with truncations that keep
`t` gaps bounded below, or weighted constants. That is not assessed.

**SUMMARY (slice 3) ok 2 / warn 1 (gap in a used inference; repairability not assessed) / bug 0.**

## Slice 4: the gap bites at `a = 1/2`, where the Trace Formula is computed (2026-11-21)

This answers the question slice 3 left open.

**1. The `a`-line basis is indexed by zeros on `Re s = a`.** Theorem 10.2.1.1
(p. 440) takes `t ∈ ℝ` "such that `ρ_{χ,t} := χ|·|_F^{a+it}` is a zero of
`L(s, χ)`". That is Tate's parametrization (Notation 10.2.1.1:
`χ|·|^z_F`, `z ∈ ℂ`), so the critical line is **`a = 1/2`**.

**2. The Trace Formula is computed at `a = 1/2`.**
- p. 487: the trace calculation "will, in turn, be possible upon further
  assuming `a = 1/2` and `s ≥ 2[F:Q]`".
- p. 519 (§12.5): "in the special case the parameter `a` is chosen to be
  `a = 1/2` … This is also where the necessity of the choice `a = 1/2` is
  explained".
- pp. 435–438: the Fourier transform extends continuously only for
  `a = 1/2`.
- p. 466: the spectral side uses Theorems 10.2.1.1 and 10.3.1.1 for these
  bases.

**3. What `C` must bound.** (10.3.1.18), p. 451, needs
`‖η_{χ_k,t_{k,j},m'}‖_{−s,2} · ‖ψ_{χ_k,t_{k,j},m}‖_{s,2} ≤ C` "independent of
`m'` and of `(k, j)`", i.e. **one `C` for all zeros**. The text adds "the
countable set `{η}` … and its bi-orthogonal in `W^{s,2}(C_F)` are both contained
in the closed ball of radius `C^{1/2}`". That uniform `C` makes the
singular-value bounds (10.3.1.20)–(10.3.1.22) independent of the zero, and
those bounds give the convergence `A_K → A_{(k,j)}` and the spectral
nuclearity that §10.4.3 feeds into the Trace Formula (p. 468).

**4. At `a = 1/2` no such `C` exists** (argument, not formalized; every step
is standard, but a specialist should check):
- (i) `|⟨ψ, η⟩_{s,2}| ≤ ‖ψ‖_{s,2}‖η‖_{−s,2}` (Cauchy–Schwarz with reciprocal
  weights). So `f = ⟨ψ_t, ·⟩` satisfies `close_pair_lower`'s hypothesis with
  `N = ‖·‖_{−s,2}` and `B = ‖ψ_t‖_{s,2}`.
- (ii) Biorthogonality gives `⟨ψ_t, η_t⟩ = 1` and `⟨ψ_t, η_{t'}⟩ = 0` (same
  `χ`, `m = 0`), so `‖ψ_t‖_{s,2} ≥ 1/‖η_t − η_{t'}‖_{−s,2}`
  (`MarkushevichBoundQEX.v : close_pair_lower`).
- (iii) `‖η_t − η_{t'}‖_{−s,2}² = vol(C_F¹)·∫_ℝ |e^{itu} − e^{it'u}|²(1+u²)^{−s/2} du ≤ vol·∫ min(4, |t−t'|²u²)(1+u²)^{−s/2} du`,
  which tends to `0` as `|t−t'| → 0`, uniformly in `t` (dominated
  convergence, `s > 1`).
- (iv) For `χ = 1` (`ζ`), Selberg gives `N₀(T) ≫ T log T` zeros on
  `Re s = 1/2` up to height `T`. So consecutive ordinates `t < t'` with
  `t' − t → 0` exist (average gap `≪ 1/log T`).
- (v) Hence `sup_t ‖ψ_t‖_{s,2} = ∞` (`no_uniform_bound`), while
  `‖η_t‖_{−s,2}` stays in `[1/C₀, C₀]` (Proposition 10.2.1.3). So **no uniform
  `C` exists** in (10.3.1.18).

**5. Repairability (reading).** The estimates survive only if the
`t`-dependent constant `C_t ≈ ‖ψ_t‖` is beaten by the decay of `φ̂^{(i)}(t)`
(φ ∈ D(C_F), so `φ̂` decays faster than any polynomial on vertical lines).
`C_t` behaves roughly like the reciprocal distance from `η_t` to the span of
its neighbours, which is controlled by gaps between consecutive critical
zeros, and **no unconditional lower bound on those gaps is known**. Such
bounds are tied to questions like the simplicity of zeros. So a repair needs
either an unconditional growth bound for `‖ψ_t‖` (a new input) or a
different route to nuclearity. Neither is supplied on pp. 450–451.

| item | OUTCOME |
|---|---|
| normalization: `a`-lines are `Re s = a` in Tate's parametrization; the TF is at `a = 1/2` | **located** (pp. 440, 435–438, 487, 519) |
| `C` in (10.3.1.18) must be uniform over all zeros | **located** (p. 451) |
| at `a = 1/2`, `sup_t ‖ψ_t‖ = ∞` via `close_pair_lower` + continuity of `t ↦ η_t` + Selberg | **argument** (steps i–v; `close_pair_lower` / `no_uniform_bound` are machine-checked, the rest is standard analysis not formalized) |
| fatal? | **not assessed.** Repair needs unconditional control of `‖ψ_t‖` growth against `φ̂` decay. |

**SUMMARY (slice 4) ok 2 / warn 1 (uniform-`C` step in §10.3 fails as stated at `a = 1/2`; repairability open) / bug 0.**
This sharpens the publicly reported p. 444 objection. The failing inference is
used, at the parameter where the Trace Formula is computed, in the
nuclearity estimate that feeds the spectral side. Whether the proof can be
mended is a question for specialists.

## Slice 5: the slice-4 chain formalized, modulo named analytic inputs (2026-11-21)

`MarkushevichBoundQEX.v` (Stdlib, `Q`), *Closed under the global context*:

| Rocq theorem | statement | OUTCOME |
|---|---|---|
| `small_gap` | pigeonhole: a strictly increasing list `x₀ < … < x_n` in `[0, T]` with `T < n·g` has a consecutive gap `≤ g` | **QED, zero axioms**, no hypotheses |
| `psi_unbounded` | given (ii) biorthogonality `⟨ψ_t, η_t⟩ = 1` and `⟨ψ_t, η_{t'}⟩ = 0` on the zero set, (iii) uniform continuity of `t ↦ η_t` in `N`, and (iv) Selberg-type density (for every `K`, increasing zero ordinates in `[0, T]` with `n > K·T`), **no `B > 0` bounds all `⟨ψ_t, ·⟩` by `B·N`** | **QED, zero axioms** (conditional on (ii)–(iv) as section hypotheses) |

This replaces slice 4's steps (iv)–(v) by a proof. The remaining trusted
inputs are exactly:
- **(ii):** biorthogonality, which is Theorem 10.2.1.1 of the draft itself;
- **(iii):** the dominated-convergence estimate for `‖η_t − η_{t'}‖_{−s,2}`,
  `s > 1`;
- **(iv):** Selberg's `N₀(T) ≫ T log T` for `ζ` on the critical line, which
  makes the count beat `K·T` for every `K`.

**SUMMARY (slice 5) ok 2 / warn 0 / bug 0.**

## Slice 6: prior art. The gap is already reported upstream (2026-11-21)

**Precedence.** The slice 3–5 gap is reported in the formalization project as
issue **mccorvie/riemann-masullo#1169**, "Manuscript gap at (10.3.1.18): close
zeta zeros preclude the uniform biorthogonal bound". It was opened on
2026-11-20T23:35Z by `yikerman`, **before** this finding, and was found here via
`gh api search/issues` after slices 3–5 were written. The argument there
matches slices 3–5 step for step:
- dual-norm identity `‖η_t − η_u‖² = c∫|e^{i(t−u)x} − 1|²/(1+x²) dx` (at `s = 2`);
- dominated convergence;
- many critical-line zeros, hence close pairs (`≫ T log T` against `O_δ(T)`
  for a `δ`-separated set);
- `1 = |(η_t − η_u)(ψ_t)| ≤ ‖η_t − η_u‖‖ψ_t‖`, including for the quotient norm.

**Where #1169 is sharper.**
- It cites **Conrey's Theorem 1** (a positive proportion of *simple*
  critical-line zeros) instead of Selberg. That makes the `m = 0` indexing and
  the distinctness of ordinates explicit.
- It notes that the same close pairs occur in any centred strip of positive
  width, where the factor `e^{−2α|x|}` preserves the convergence. So the gap
  also affects the `I`-based strip bases (Theorem 10.2.2.1), not only the
  `a`-line.

**What this finding adds.**
- An independent reproduction, from reading the draft.
- The location of the inference's source (Terminology 10.2.1.2(2), p. 444)
  and of its other uses (Corollaries 10.2.1.4 and 10.2.2.3, p. 468).
- **Machine-checked cores** in `MarkushevichBoundQEX.v`:
  - `block_qex`: the general inference is false;
  - `close_pair_lower` / `no_uniform_bound`;
  - `small_gap`: the pigeonhole step;
  - `psi_unbounded`: the full chain, with biorthogonality, continuity and
    density as named hypotheses.

**Corrections to slices 3–5.**
- Slice 3's "independently confirms that the publicly reported p. 444
  objection is a genuine gap" stands.
- It should not be read as a new discovery. The specific failure at
  (10.3.1.18) was reported upstream first, in #1169.

**SUMMARY (slice 6) ok 1 / warn 1 (precedence: the gap is upstream #1169; this finding is a reproduction with Rocq cores) / bug 0.**

## Slice 7: wording corrections from the Cursor reviews (2026-11-21)

The earlier text is kept for history. These readings replace it:

| where | earlier wording | corrected reading |
|---|---|---|
| Status / SUMMARY | "the main theorem is publicly disputed" | Concerns are **reported** (Lean Zulip thread, details not posted; news coverage of the p. 444 objection). They were **not read here**, except that slices 3–6 later checked p. 444 against the text layer. |
| comparison table, reading | Alpöge "proves" the growth bound; the claim is "machine-checkable but unread" | Alpöge's development **claims** the one-sided bound in a form a kernel could check. This repo's audit is **PASS-STATIC / PENDING**: it was not built, and `#print axioms` was not run. |
| reading | "Connes showed that a trace formula of this kind is equivalent to RH" | Background **not verified in this finding**. It is a recollection of Connes (1999), cited as context. |
| slice 3 | "`block_qex` … the inference is false in general" | `block_qex` is a **local obstruction** (one biorthogonal pair per bound `B`). The ℓ² direct sum that would be a counterexample basis is standard but **not compiled**. |
| slice 3 | "independently confirms … genuine gap" | What is confirmed: the text-layer quotation of p. 444 matches, and "regular ⇒ `{f_m}` bounded" fails for Markushevich bases (modulo the uncompiled assembly). That pp. 451/468 inherit the gap is the slices 4–5 **argument**, and it was first reported upstream in #1169. |
| probe header | `MarkushevichBoundQEX.v` "no hypotheses" | `block_qex` needs only `0 ≤ B`. `no_uniform_bound` and `psi_unbounded` sit under named section parameters (`fam_sub` / `fam_bound`; `psi_sub`, `bio1`/`bio0`, `eta_cont`, `dense_zeros`). |
| slice 5 | `small_gap` "strictly increasing list" | `small_gap` assumes `0 ≤ x`, `last ≤ T`, `0 ≤ g` and `T < length(l)·g`, and concludes that not every gap exceeds `g`. Strict increase is part of `dense_zeros`, which `psi_unbounded` uses. |
| slice 5 | trusted inputs "(ii)–(iv)" | Add `psi_sub` (additivity of `ψ_t`). `dense_zeros` asks for **distinct** ordinates with tail length `> K·T`. Selberg's or Conrey's counts must be read as counts of distinct ordinates; Conrey's simple zeros (as in #1169) give that directly. |
| slice 4 | "the uniform-`C` step fails as stated" | This is the conclusion of an **argument**, not a compiled refutation of (10.3.1.18). Only `close_pair_lower` was machine-checked at the time; slice 5 then added `small_gap` and `psi_unbounded`, conditional on named inputs. |

**SUMMARY (slice 7) ok 0 / warn 9 (wording corrected) / bug 0.**
Unchanged: Theorem 12.5.1.1 is **READ / NOT ASSESSED**. The Alpöge audit is
**PASS-STATIC / PENDING**. The (10.3.1.18) gap is upstream #1169.

## Slice 8: the direct-sum counterexample compiled (2026-11-21)

This answers the review point that `block_qex` was only a local obstruction.
`MarkushevichBoundQEX.v : direct_sum_qex` (Stdlib, `Q`) is *Closed under the
global context*, with no section hypotheses.

**Space.** Finitely supported sequences of `Q²` blocks (`c₀₀` over blocks).
Single-block vectors are pairs `(k, p)`. The direct-sum inner product is
`ip (k,p) (k',q) = dot2 p q` when `k = k'`, and `0` otherwise.

**Family.** In block `k`, take `ε_k = 1/(k+1)` (i.e. `block_qex` with `B = k`):
- `x(k,0) = (k,(1,0))`, `x(k,1) = (k,(1,ε_k))`;
- `f(k,0) = (k,(1,−(k+1)))`, `f(k,1) = (k,(0,k+1))`.

**Proved in one statement:**
- **global biorthogonality:** `⟨f(k,j), x(k',j')⟩ = 1` iff `(k,j) = (k',j')`,
  and `0` otherwise, across blocks too;
- **uniformly bounded and regular:** `1 ≤ ‖x(k,j)‖² ≤ 2` for all `k`, `j`;
- **spanning:** `(k,(1,0)) = x(k,0)` and
  `(k,(0,1)) = (k+1)·(x(k,1) − x(k,0))`, so `span{x} = c₀₀`;
- **unbounded functionals:** `f(k,1)` takes the value `k+1` on the unit vector
  `(k,(0,1))`, so for every `B` some functional exceeds `B` on a unit vector.

**Translation (standard, not re-proved).** `c₀₀` is dense in `ℓ²`, so this
total, spanning biorthogonal system extends to a Markushevich basis of `ℓ²`.
The vectors are bounded and bounded away from `0`, and `{f_m}` is unbounded.
With that standard step, **"regular ⇒ `{f_m}` bounded" (p. 444) is false for
Markushevich bases**. The slice 7 caveat ("local obstruction only") is
superseded by this theorem.

**SUMMARY (slice 8) ok 1 / warn 0 / bug 0.**
