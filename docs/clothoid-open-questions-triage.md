# Clothoid open questions — Fresnel support, integer regime, linearisation trade-off: research & gap triage

> **Status:** living triage for the three "Open Questions (Honest)" carried
> over from the clothoid lane (the `clothoid-halley-coq` bridge of
> [`audit-phase4-curves.md`](audit-phase4-curves.md) §6.1–6.2 and the S10b
> chord seed of [`issue-67-relateng-triage.md`](issue-67-relateng-triage.md)).
> Q1 and Q3 are scope decisions, not proof gaps; Q2 has one cheap Qed
> terminal. Refresh when a session closes any route below.
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
| **Q2 Integer-parameter exact regime** | **ABSENT; one exact sub-regime TRACTABLE** | precedent `Orient_b64_exact.v:966` | The `b64_orient_sign_filtered_sound_small_int` analogy (integer coords, \|c\| ≤ 2²⁵ ⇒ bit-exact) holds only for **polynomial** predicates. The clothoid residual is transcendental — no integer regime makes `cos`/`sin` integrals dyadic. Honest carve-outs: the degenerate straight-chord regime (κ₀ = κ₁ = 0 ⇒ P = 1, Q = 0, f(L) = L² − d², unique positive root L = d **exactly**) and a Scope-A polynomial-prefix slice (residual assembly given P/Q values), mirroring `ArcLineIntersect_b64_exact.v`'s first-stage pattern. |
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
  κ₀ = κ₁ = 0 ⇒ f(L) = L² − d² with unique positive root L = d, exactly
  representable for dyadic d; an integer-coordinate version mirrors the
  `_small_int` headline pattern (`Orient_b64_exact.v:966`). A Qed terminal
  in one session, no Fresnel, no new axioms.
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
asks for it. Land **(A)** as the only near-term Qed terminal. Close Q3 as a
documented non-goal (this section is that record), with **(B)** queued
behind a consumer.

**What would NOT change under any route:** `ClothoidResidual.v` stays
Qed/three-axiom (routes only *discharge* its hypotheses, never weaken them);
this corpus stays BSD-3-Clause with its three-axiom allowlist (any
fourth-axiom or copyleft-adoption decision is recorded, never silent);
Option-B chord-first; no new `Admitted` (any deferral would have to enter
`admitted-deferred-proofs.txt`, and none is proposed); the oracle remains
differential, never the source of truth.
