# Clothoid open questions — Fresnel support, integer regime, linearisation trade-off: research & gap triage

> **Status:** living triage for the three "Open Questions (Honest)" carried
> over from the clothoid lane (the `clothoid-halley-coq` bridge of
> [`audit-phase4-curves.md`](audit-phase4-curves.md) §6.1–6.2 and the S10b
> chord seed of [`issue-67-relateng-triage.md`](issue-67-relateng-triage.md)).
> Q1 and Q3 are scope decisions, not proof gaps; Q2's cheap Qed terminal —
> route (A) — **landed 2026-06-12** as `theories/ClothoidDegenerate.v`
> (see §6/§8). Refresh when a session closes any route below.
>
> Every file:line citation below was verified by direct grep against the tree
> at the time of writing (corpus HEAD = `main` at `80a3230`).

## 1. What the open questions ask

Carried into this corpus by the issue owner (2026-06-12), verbatim:

1. **Full Fresnel integral support** (may need Flocq or rational
   approximation).
2. **Exact integer-parameter regime** (similar to C1 grid-exactness).
3. **Performance vs. linearisation trade-off for NTS.Curve.**

They arise from the clothoid chord seed (`theories/RelateClothoid.v`, S10b)
and the conditional residual theorem (`theories/ClothoidResidual.v`), against
the cross-corpus bridge status in `audit-phase4-curves.md` §6.1–6.2.

## 2. Strategic context already on record

- **Conditional-premise idiom, not Admitted.** `theories/ClothoidResidual.v`
  proves monotone-branch uniqueness of the chord-length residual
  `f(L) = L²(P²+Q²) − d²` **Qed** with the analytic content as three named
  Section hypotheses — `H_deriv` (`ClothoidResidual.v:108`, f′ is the
  derivative of f), `H_fprime_pos` (`:114`, f′(L) > 0 on the branch
  `|κ·L| ≤ π`), `H_mvt` (`:124`, MVT in `MVT_cor2` shape, threaded as a
  premise because Stdlib's `MVT_cor2` pulls `Classical_Prop.classic`, outside
  the three-axiom allowlist). Headlines:
  `clothoid_residual_strictly_increasing` (`:155`) and
  `clothoid_residual_unique_root` (`:184`), plus the branch-interior lemma
  `branch_monotone_inward` (`:135`). Same idiom as
  `hobby_theorem_4_1_conditional` and `overlay_ng_correct_conditional`.
- **The external witness is now public — and relicensed.** The companion
  corpus
  [`grootstebozewolf/clothoid-halley-coq`](https://github.com/grootstebozewolf/clothoid-halley-coq)
  has a public repro (Coq `Clothoid.v` / `Clothoid_L.v` / `ClothoidPolish.v`
  derivative identities, Qed under Coquelicot; C# / Java / TypeScript Halley
  solvers bit-identical on the 9,058-record ProRail dataset; public release
  v1.0.2). Its LICENSE is the **standard, unmodified EUPL-1.2** (verified
  against the raw file, 2026-06-12), with the two ProRail data files under
  CC BY 4.0, copyright Merkator Group 2026 — and its README states the
  proofs are *"provided for integration into formal geometry corpora such
  as NetTopologySuite.Proofs (itself BSD-3-Clause licensed and governed
  exclusively by its own licence)"*. This **supersedes** the
  proprietary-licence description in `audit-phase4-curves.md` §6.1
  (`LicenseRef-Merkator-Proprietary-NoAITraining`), which documented the
  pre-publication state of 2026-05-16. The relicensing that
  `ClothoidResidual.v:65` anticipated ("relicensing collapses these
  hypotheses into real lemmas") has happened: the witness is now an
  open-source artifact anyone can compile and audit.
- **Option B chord-first is architectural, not a perf heuristic.** Every
  algorithm beneath the NTS geometry API consumes `Coordinate[]` via
  `SegmentString`, so curves linearise on entry
  (`audit-phase4-curves.md` §3–4; reconfirmed by the chord-overfitting
  audit).
- **Float evaluation is an interface boundary.** The corpus's standing
  stance (M-LEN/M-AREA rows of `../TRIAGE_NTS_JTS_ISSUES.md`) is exact
  rational/R-side invariants + differential oracle, with float evaluation at
  the boundary. Fresnel evaluation is the same kind of boundary.
- **Differential oracles exist on both sides**:
  `oracle/de9im_clothoid_vectors.txt` (3 chord-regime vectors, this corpus)
  and `golden_vectors.json` (9,058 ProRail records, ≤4 Halley iterations,
  companion corpus — `audit-phase4-curves.md` §6.1).

## 3. Per-question status

| Question | Status | Anchor | Notes |
|---|---|---|---|
| **Q1 Fresnel integrals (R-side)** | **CONDITIONAL (Qed); integrals ABSENT by design** | `ClothoidResidual.v:99-128` | P/Q are never materialised; f, f′, κ are Section Variables and the analytic facts are named hypotheses, externally witnessed Qed in `clothoid-halley-coq/coq/Clothoid_L.v`. Three-axiom footprint preserved (audit footer). |
| **Q1′ Fresnel evaluator (b64)** | **ABSENT (aspirational)** | `Intersect_b64_exact.v:2038-2080` | `HasClothoidIntersect` typeclass is a commented sketch; no closed form exists (transcendental Fresnel residual, `:2046`); Halley-on-L intended; Coquelicot→native-Reals porting estimated 3–5 days for the identities (`:2073`) — *before* any b64 lift. |
| **Q2 Integer-parameter exact regime** | **PARTIAL — degenerate + Scope-A + Halley bound + b64 prefix LANDED (Qed/cond)** | `ClothoidDegenerate.v`; `ClothoidDegenerate_b64.v`; `ClothoidScopeA_b64.v`; `ClothoidResidual_b64_exact.v`; `ClothoidHalley.v`; `ClothoidHalley_b64.v`; precedent `ArcLineIntersect_b64_exact.v` | Polynomial predicates only: the transcendental Fresnel evaluator stays absent. Routes **(A)**, **(C)**, **(C′)**, Scope A.4–A.7 landed (§8–§15). Still open: full intersect evaluator, routes **(B)**/**(D)**. |
| **Q3 Performance vs. linearisation** | **NOT A THEOREM; fidelity layer LANDED** | `Linearise.v:225,361,385`; `CurveLinearise.v:109,126,139` | Operational fidelity is proven: `disjoint_under_linearise` (`Linearise.v:225`) with honest negatives `regime3_counterexample` (`:361`) and `EqualsExact_not_stable` (`:385`); structural closure `chord_approx_ring_closed` / `to_geometry_{outer,hole}_ring_closed` (`CurveLinearise.v:109,126,139`). Runtime throughput is NTS benchmarking territory, out of corpus scope; the *provable* face is chord-count-vs-sagitta bounds and the bounded-iteration (≤4) termination model. |

## 4. Inventory of existing clothoid assets

**R-side (`theories/`, three axioms, Admitted-free):**

- `ClothoidResidual.v` — conditional monotonicity + unique-root corollary +
  `branch_monotone_inward`.
- `RelateClothoid.v` — `ClothoidChord` carrier (`:41`),
  `cl_matrix_*` witnesses (`:59-75`), and the solver link
  `clothoid_L_unique_on_branch` re-export.
- `RelateMatrixClothoid.v` — regime→witness selection `clothoid_fill`
  (`:23`) + three `clothoid_fill_*_eq` lemmas (`:30,34,38`).
- `Azimuth.v` — the cross-corpus bridge block (`:311-348`):
  `turn_sign_eq_cross`, `sin_half_turn_sq`, `miter_ratio_le_iff` are cited
  by the companion paper.

**Flocq layer:** nothing live; `Intersect_b64_exact.v:2032-2090` is comment
only (typeclass sketch + porting-cost notes).

**Oracle:** `oracle/de9im_clothoid_vectors.txt` (3 chord-regime vectors);
the 9,058-record `data/golden_vectors.json` is public in the companion repo
under CC BY 4.0 (derived from ProRail Spoorgeometrie).

**Docs:** `audit-phase4-curves.md` §6.1–6.3; `issue-67-relateng-triage.md`
§7 S10b; `verified-claims.md` clothoid rows.

## 5. The genuine gaps, by nature

1. **Q1 is a stack seam, not a maths gap — and no longer a licence seam.**
   The mathematics is Qed, in a different stack (Coquelicot). With the
   public repro relicensed EUPL-1.2 and its README explicitly providing the
   proofs for integration into this corpus, the former licence gate is
   gone; what remains is purely technical: (i) defining P/Q with Stdlib
   `RiemannInt` and proving differentiation under the integral — Stdlib has
   no parametric-integral differentiation lemma, so this is the genuinely
   hard analytic content, well beyond the "3–5 days mechanical" estimate
   (which assumed Coquelicot's `auto_derive`); (ii) Stdlib's
   `RiemannInt`/MVT machinery pulls `Classical_Prop.classic` — a
   fourth-axiom decision (cf. `category-c-policy.md`); (iii) the
   alternative — taking Coquelicot as a dependency (the witness's native
   stack) — is an ecosystem shift the corpus has so far declined, and
   verbatim adoption of EUPL-1.2 proof scripts into the BSD-3 tree is a
   call for Joost the BDFL (EUPL is copyleft; the README's integration
   note reads as the copyright holder's grant, but the corpus should
   record that decision explicitly when route (D) is taken).
2. **Q2's full version is a category error, honestly named.** Transcendence
   kills any bit-exact full-pipeline integer regime. What exists is one
   exactly-solvable degenerate regime (straight chord) and a Scope-A
   polynomial prefix — worth landing precisely because they are honest about
   where exactness ends.
3. **Q3 is a scope boundary, not a gap.** Fidelity (three regimes,
   `Linearise.v`) and structure (`CurveLinearise.v`) are proven; throughput
   is empirical and belongs to NTS.Curve benchmarking. The formal residue
   here is a quantitative sagitta-density lemma (over `ArcChordApprox.v`'s
   `sagitta_le_arc_radius`, `:228`) and the bounded-iteration termination
   lemma — the latter conditional on Q1's hypotheses, in the
   `ClothoidResidual.v` idiom.

## 6. Risk/cost-ordered options for the next (Coq) terminal

- **(A) Degenerate-chord exact regime (Q2)** — *low risk, high value.*
  ~~κ₀ = κ₁ = 0 ⇒ f(L) = L² − d² with unique positive root L = d~~
  **LANDED 2026-06-12** (`theories/ClothoidDegenerate.v`, Qed, three axioms;
  see §8). The b64 integer-coordinate mirror (the `_small_int` pattern,
  `Orient_b64_exact.v:966`) remains queued as the follow-up slice.
- **(B) Sagitta-density bound (Q3)** — *medium.* "n chords achieve ε" over
  the `ArcChordApprox.v` foundations: the provable face of the performance
  trade-off. Queue behind a concrete NTS.Curve consumer.
- **(C) Scope-A residual-assembly exactness (Q2)** — *medium.* Bit-exact
  polynomial prefix of f given oracle-supplied P/Q values, modelled on
  `ArcLineIntersect_b64_exact.v`; honest that the transcendental stage is
  never claimed.
- **(D) Full Fresnel internalisation (Q1)** — *high / strategic.* The
  licence gate is gone (EUPL-1.2 repro, integration-note grant); what
  remains are the §5.1 scope decisions (Stdlib `RiemannInt` + a `classic`
  fourth-axiom call, a Coquelicot dependency, or recorded adoption of the
  EUPL witness scripts). **Pivot away** unless a downstream consumer
  demands end-to-end machine-checked Halley; the bounded-iteration
  termination lemma can be written conditionally (the `ClothoidResidual.v`
  idiom) without it.

## 7. Recommendation

Hold Q1 at the conditional idiom + the now-public external witness + the
differential oracle — that combination is already stronger than most
"verified" claims in the field, and route (D) buys little until a consumer
asks for it. Route **(A)** — the only near-term Qed terminal — is landed
(§8). Close Q3 as a documented non-goal (this section is that record), with
**(B)** queued behind a consumer.

**What would NOT change under any route:** `ClothoidResidual.v` stays
Qed/three-axiom (routes only *discharge* its hypotheses, never weaken them);
this corpus stays BSD-3-Clause with its three-axiom allowlist (any
fourth-axiom or copyleft-adoption decision is recorded, never silent);
Option-B chord-first; no new `Admitted` (any deferral would have to enter
`admitted-deferred-proofs.txt`, and none is proposed); the oracle remains
differential, never the source of truth.

## 8. Route (A) session — degenerate-chord exact regime (2026-06-12): LANDED

Red/Green/Refactor record for the first route taken off the §6 ladder.

**Red.** Target 1: the degenerate residual `f_deg(L) = L·L − d·d`
(κ₀ = κ₁ = 0 ⇒ P = 1, Q = 0) with all three `ClothoidResidual.v` Section
hypotheses discharged concretely. Target 2: the exact-root headline plus
end-to-end instantiation of the conditional theorems (non-vacuity of the
interface). Predicted tangents, in order: `derivable_pt_lim` fct-notation
unification; square-injectivity shape (fallback `nra`); `PI > 0` plumbing.
Stopping conditions: full success = both targets Qed at three axioms;
tangent-stop = direct (non-interface) proofs only, recorded PARTIAL. The
b64 mirror explicitly out of scope.

**Green — LANDED** (`theories/ClothoidDegenerate.v`, first-shot compile;
none of the predicted tangents bit):

- `degenerate_root_exact`, `degenerate_strictly_increasing`,
  `degenerate_unique_positive_root` — the exact answer, directly: `L = d`
  is the unique positive root, on the nose, no approximation.
- `degenerate_H_deriv`, `degenerate_H_fprime_pos`, `degenerate_H_mvt`,
  `degenerate_branch_trivial` — the three Section hypotheses of
  `ClothoidResidual.v` discharged concretely at κ = 0. The MVT premise is
  discharged **constructively** (witness `c = (a+b)/2`), avoiding
  `MVT_cor2` and hence `Classical_Prop.classic` — the file stays on the
  three-axiom allowlist.
- `degenerate_strictly_increasing_via_interface`,
  `degenerate_unique_root_via_interface`,
  `degenerate_root_is_chord_length` — the Section-closed conditional
  theorems instantiated end-to-end: the conditional interface of
  `ClothoidResidual.v` is **inhabited**, so its hypotheses are not
  mutually unsatisfiable (the corpus's standard non-vacuity check, cf.
  `GeneralTriangleParityRED.v`).

**Refactor.** Registered in `_CoqProject` (host lane — Stdlib-only) and
`_CoqProject.full`; full gauntlet green (`check_admitted`: 7 registered,
unchanged; `audit_axioms` over the augmented output-synced log: allowlist
clean, no `classic`; `check_readme_axioms`: in sync).

**Remaining gaps after this session** (see §9–§11 for closures): the b64
degenerate mirror and Scope-A assembly were queued here; both later landed.
Routes (B) and (D) untouched.

## 9. Route (A) b64 slice — integer-regime mirror (2026-06-12): LANDED

Second RGR iteration off the §6 ladder; closes the first of §8's two
queued follow-ups.

**Red.** Target 1: `b64_degenerate_residual d L := L⊗L ⊖ d⊗d` bit-exact
under `coord_int_safe` (squares ≤ 2⁵⁰, difference ≤ 2⁵¹ < 2⁵³ — every
step inside binary64's integer-exactness window). Target 2: root
exactness composed with the R-side uniqueness theorem. Target 3
(stretch): full sign trichotomy. Predicted tangents: nonlinear Z bounds
(`nia` fallback); `IZR`/`B2R` rewrite plumbing; cross-lane import
friction.

**Green — LANDED** (`theories-flocq/ClothoidDegenerate_b64.v`,
first-shot compile; all three targets including the stretch):

- `b64_degenerate_residual_exact` — `B2R (b64_degenerate_residual d L)
  = degenerate_residual (B2R d) (B2R L)` **on the nose** in the integer
  regime, plus finiteness. Reuses `b64_mult_int_exact` /
  `b64_minus_int_exact` (`Orient_b64_exact.v`) with two small window
  lemmas (`square_int_window`, `square_diff_int_window`).
- `b64_degenerate_root_exact` — for positive integer-regime inputs the
  binary64 residual is zero **iff** `B2R L = B2R d`, composing the
  exactness identity with `degenerate_unique_positive_root` /
  `degenerate_root_exact` from the R-side file.
- `b64_degenerate_sign_trichotomy` — the residual's sign decides the
  exact comparison of L against d (the `_small_int` idiom: full
  exactness inside the window, no claim outside it).

**Refactor.** Registered in `_CoqProject.full`; added to
`docs/audit-exceptions.txt` under the standard Flocq `Bmult`/`Bminus`
`classic` lineage (same rationale as `Orient_b64_exact.v`); gauntlet
green (7 registered Admitted unchanged; axiom audit clean on the
augmented log; README/allowlist in sync).

**Remaining after this slice:** Q2's Scope-A residual-assembly prefix
(route (C)) — see §10–§11.

## 10. Route (C) — Scope-A residual-assembly prefix (2026-06-12): LANDED

Third RGR iteration; closes the last queued Q2 item. With this, every
tractable rung of the §6 ladder short of consumer-gated (B) and
strategic (D) is done.

**Red.** Target 1: generic skeleton — the five-operation binary64
assembly `L⊗L ⊗ (p⊗p ⊕ q⊗q) ⊖ (d⊗d) ⊗ s2` over integer-valued inputs is
bit-exact under per-intermediate window hypotheses. Target 2: concrete
window instantiation (|nL|, |nd| ≤ 2¹², |np|, |nq| ≤ 2¹³, ns2 = 2²⁶;
largest intermediate 2⁵¹ + 2⁵⁰ < 2⁵³). Target 3: sign trichotomy.
Target 4 (stretch): consistency with the route-(A) degenerate slice.
Predicted tangents: degree-4 `nia` obligations; `b64_plus` exactness
lemma possibly missing; fixed-point scaling algebra.

**Green — LANDED** (`theories-flocq/ClothoidScopeA_b64.v`; one tangent
bit — the degree-4 window obligation needed staged intermediate bounds
(`Z.mul_le_mono_nonneg` + `nia` per factor) instead of a one-shot `nia`;
`b64_plus_int_exact` already existed in `Orient_b64_exact.v`):

- `b64_residual_assembly_int_exact` — the generic skeleton, all five
  operations chained through the `_int_exact` lemmas.
- `b64_residual_assembly_exact_window` — the concrete fixed-point
  window: oracle-supplied P/Q approximants scaled by 2¹³, coordinates
  to 2¹², scale square 2²⁶.
- `b64_residual_assembly_sign_decides` — the binary64 sign test decides
  the integer assembly's sign exactly: a solver's only remaining error
  budget is the transcendental approximation |P̂ − P|, |Q̂ − Q|, which
  lives entirely in the oracle-supplied inputs, never in the arithmetic.
- `residual_assembly_degenerate_consistent` — at np = 2ˢ, nq = 0 the
  assembly is 2²ˢ times `degenerate_residual` (route (A)) — same sign,
  same roots; this lemma is allowlist-only (no `classic`).

The transcendental P/Q stage is **never claimed** — stated in the file
header and here, per this doc's Q2 analysis.

**Refactor.** Registered in `_CoqProject.full` and
`docs/audit-exceptions.txt` (Flocq `classic` lineage; the consistency
lemma itself is clean). Gauntlet green (7 registered Admitted unchanged;
axiom audit clean on the augmented log; README/allowlist in sync).

**Ladder state after this session:** (A) merged (#182); (C) landed
(this section); (B) queued behind an NTS.Curve consumer; (D) pivot-away
unless a consumer demands end-to-end machine-checked Halley.

## 11. Route (C) Scope A.0–A.3 slice — residual assembly (2026-06-12): LANDED

Fourth RGR iteration; closes the second of §8's queued follow-ups.
Complements §10's `ClothoidScopeA_b64.v`: that slice proves the
fixed-point *scaled* assembly (`ns2 = 2²⁶` window, sign-decides
trichotomy); this one proves the *direct* integer-window assembly
(`d2` taken as a scalar) and extends it to the derivative `f′`,
feeding the Halley slices in §12–§15.

**Red.** Targets A.0–A.3 from the `Solver.cs` / `Clothoid_L.v` polynomial
prefix: `d2` (chord squared length), `r2 = P²+Q²`, residual
`f = L²·r2 − d2`, and derivative `f′ = 2L·r2 + 2L²(Q·Rm − P·T)`.
Safety windows: arc chord coords `|n| ≤ 2¹¹`; scalar moments `|n| ≤ 2¹²`
with derived bounds through `2⁵¹` on the prime sum. Predicted tangents:
`IZR`/`B2R` rewrite direction on nested sums; `intros`/`destruct` pattern
syntax; associativity mismatch between `2·nL·nL·…` and `2·(nL·nL)·…` in
the prime witness.

**Green — LANDED** (`theories-flocq/ClothoidResidual_b64_exact.v`, Admitted-free):

- `b64_clothoid_d2_exact`, `b64_clothoid_r2_exact`,
  `b64_clothoid_residual_exact`, `b64_clothoid_residual_prime_exact` —
  each pins `B2R` of the `b64_*` assembly to the named R-side witness on
  the nose, plus finiteness, inside the integer windows above.
- `b64_clothoid_residual_unit_moments` — degenerate moments `P=1`, `Q=0`
  fold `r2` to `b64Z 1` (via `B2R_Bsign_inj`), yielding the `L⊗L⊗1 ⊖ d2`
  pipeline shape.

**Refactor.** Registered in `_CoqProject.full`; listed in
`docs/audit-exceptions.txt` (Flocq `classic` lineage); claims in
`docs/verified-claims.md`; gauntlet green (`check_admitted` unchanged).

**Remaining after this slice:** routes **(B)** and **(D)** unchanged; optional
b64 `f''` + Halley-step mirror of Scope A.

## 12. Route (C') conditional Halley bound (2026-06-12): LANDED

Fifth RGR iteration off the §6 ladder.

**Red.** Target: the bounded-iteration termination *model* from
`docs/audit-phase4-curves.md` §6.1 — not a cubic-convergence proof, but the
`ClothoidResidual.v` idiom applied to the empirical ≤4-iteration headline
(table 3 / `golden_vectors.json`). Secondary target: degenerate no-op at the
chord root composing route (A).

**Green — LANDED** (`theories/ClothoidHalley.v`, Admitted-free, three axioms):

- `clothoid_f` / `clothoid_fp` / `clothoid_fpp` + `clothoid_halley_l_update`
  matching `Clothoid.Halley/Solver.cs` polynomial assembly and safety guards.
- `clothoid_halley_fuel` — fuel-bounded iteration skeleton (structural
  termination by `nat` descent).
- `ClothoidHalleyCorpusBound` Section — `clothoid_halley_filtered_corpus_le_four`
  and `clothoid_halley_filtered_corpus_le_max` with discharged
  `H_filtered_corpus_le_four` / `H_iterations_le_max` (oracle witness).
- `degenerate_halley_fixed_at_root` — at κ₀=κ₁=0, `L = d` is fixed under one
  Halley update when `f = 0`.

**Refactor.** Registered in `_CoqProject` and `_CoqProject.full`; claims in
`docs/verified-claims.md`; host gauntlet green.

**Remaining:** b64 `f''` assembly + per-iterate Halley step (Scope A.4+); routes
**(B)** / **(D)** unchanged.

## 13. Route (C) Scope A.4+ slice — f'' + Halley step (2026-06-12): LANDED

Sixth RGR iteration; closes the b64 follow-up queued in §11/§12.

**Red.** Targets A.4–A.5 from `Solver.cs`: second derivative
`f'' = 2(P²+Q²) + 8L(Q·Rm−P·T) + 2L²(Rm²+T²−P·S2c−Q·S2s)` bit-exact under
`clothoid_scalar_int_safe` (|n| ≤ 2¹², derived bound ≤ 2⁵²); Halley denom /
step as `b64_div` round-chain with explicit `b64_safe` overflow premises (honest
that division is not integer-exact). Predicted tangents: `f''` inner
parentheses vs `minus_IZR` associativity; `8·nL` bound window (2¹⁵ not 2¹³).

**Green — LANDED** (`theories-flocq/ClothoidHalley_b64.v`, Admitted-free):

- `b64_clothoid_residual_second_prime_exact` — `f''` assembly pins `B2R` to the
  R-side witness on the nose inside the eight-scalar integer window.
- `b64_clothoid_halley_denom_round`, `b64_clothoid_halley_step_round` —
  per-iterate Halley polynomial step matches the composed round-chain under
  named overflow / non-zero-denominator premises.

**Refactor.** Registered in `_CoqProject.full`; listed in
`docs/audit-exceptions.txt` (Flocq `classic` lineage); claims in
`docs/verified-claims.md`; full-corpus compile green.

**Remaining:** full `HasClothoidIntersect` evaluator (transcendental Fresnel);
routes **(B)** / **(D)** unchanged.

## 14. Route (C) Scope A.6 slice — l_update / fuel (2026-06-12): LANDED

Seventh RGR iteration; closes the b64 iteration skeleton queued in §13.

**Red.** Target: mirror `ClothoidHalley.v` safety guards on binary64 —
`converged_bool`, `denom_guard_bool`, `l_new` (0.5L floor), `l_fallback`
(1.5L), `l_update`, and fuel-bounded `Fixpoint` — plus conditional ≤4-iteration
interface wired to `b64_clothoid_halley_fuel_iters`. Predicted tangents: `let`
binding in `l_update_converged`; `b64_lt_complete` finiteness plumbing.

**Green — LANDED** (`theories-flocq/ClothoidHalley_b64.v`, Admitted-free):

- `b64_clothoid_halley_l_update` / `b64_clothoid_halley_fuel` — Solver.cs guard
  chain on binary64 (moments as `binary64 -> b64_clothoid_moments` oracle).
- `b64_clothoid_halley_l_update_converged`, `b64_clothoid_halley_fuel_zero` /
  `b64_clothoid_halley_fuel_succ` — structural lemmas.
- `b64_clothoid_converged_bool_true_of_R` — bool guard from strict R comparison.
- `ClothoidHalleyB64CorpusBound` — conditional ≤4 headline (corpus witness).

**Refactor.** Claims in `docs/verified-claims.md`; full-corpus compile green.

**Remaining:** full `HasClothoidIntersect`; routes **(B)** / **(D)** unchanged.

## 15. Route (C) Scope A.7 slice — degenerate compose (2026-06-12): LANDED

Eighth RGR iteration; closes the b64 degenerate no-op queued in §13–§14.

**Red.** Target: mirror `ClothoidHalley.v : degenerate_halley_fixed_at_root` on
binary64 — at κ₀=κ₁=0 (`b64_degenerate_moments`), `b64_clothoid_halley_l_update`
is a no-op at the chord root `L = d` when the converged guard fires. Compose
route (A) (`ClothoidDegenerate_b64.v`) through the Scope A.6 `l_update`
skeleton via a comparison bridge (not syntactic equality of the full residual
term: `L⊗L⊗1` vs `L⊗L`). Predicted tangents: `b * b * 1` window plumbing;
finiteness separate from `B2R` identity; explicit strictly-positive rounded
threshold premise (honest round-chain idiom).

**Green — LANDED** (`theories-flocq/ClothoidHalley_b64.v`, Admitted-free):

- `b64_degenerate_residual_at_chord_B2R` — clothoid residual `B2R` equals
  `b64_degenerate_residual` under `coord_int_safe`.
- `b64_degenerate_halley_fixed_at_root` — `l_update (d⊗d) tol … d = d` when
  residual `B2R = 0` and rounded `tol * scale(d²) > 0`.
- Supporting lemmas: `b64_degenerate_residual_at_chord_finite`,
  `b64_clothoid_converged_bool_true_of_zero_residual`, `b64_abs_B2R_zero`.

**Refactor.** Claims in `docs/verified-claims.md`; full-corpus compile green.

**Remaining:** full `HasClothoidIntersect`; routes **(B)** / **(D)** unchanged.
