# HoTT linkage to NTS: RGR pivot on risk/cost

**Status.** Written as part of the post-refactor HoTT pivot engagement (following the "Prove the link between NTS and NTS.Proofs" request and the "one axiom allowed, let's be generous" policy). The Red–Green–Refactor cycle on *how to actually prove/establish the formal link* between the C# NetTopologySuite implementation and the (now HoTT-based) formal proofs has been analysed. The old classical "oracle + bit-exact differential testing + extracted compute" linkage (see `archive/oracle/`, `archive/docs/oracle-handroll-migration.md`, `archive/docs/oracle-soundness-finding.md`) delivered pragmatic value but had structural limitations. This document records the risk/cost reasoning and the recommended pivot for the HoTT era — same shape as the archived [`snap-rounding-rgr-pivot.md`](archive/docs/snap-rounding-rgr-pivot.md) and [`soundness-strategy.md`](archive/docs/soundness-strategy.md).

The focus is effort-vs-linkage-strength, not raw correctness. The skeleton state (only `pythagoras-for-beginners.v` live, full classical corpus + history under `archive/`, personas preserved, generous one-axiom policy) makes this the right moment for the pivot decision.

## Where the RGR cycle stands

**RED — the prior linkage approach (classical proofs + oracle bridge) has known structural costs and risks (well-documented in the archive).**

- High ongoing maintenance cost: Flocq container, multi-script CI gauntlet (`check_admitted.sh`, axiom audits), admitted registries, per-file exception tracking. The corpus grew to >1,100 Qed theorems but the "link" to actual NTS C# was always indirect (bit-exact on test vectors in safe regimes + hand port + some soundness theorems over R/b64).
- Weak "proof of link": Even when oracles matched bit-exactly, there was no formal statement "this C# method is equivalent (in the sense that transports properties) to the Coq spec." Divergences required manual triage; hand-rolled OCaml oracles had their own soundness findings (see `archive/docs/oracle-soundness-finding.md`).
- Extraction story was partial and brittle: some predicates extracted cleanly, others required hand-roll + later migration. HoTT-style work was explicitly rejected early on for compatibility reasons (see `archive/docs/ecosystem-search-2026-05-29.md`).
- Scaling risk: full Phase 0-7 classical work was multi-year, high person-cost, with deferred proofs and conditional headlines carried as named hypotheses. Re-doing or maintaining that volume for every NTS change is unsustainable.
- The "prove the link" goal was never first-class; it was a side-effect of oracle consumption in NTS.Curve.

**GREEN — the current HoTT pivot skeleton already has several low-cost, high-leverage assets for a better linkage story.**

- Explicit vision in root `README.md`: univalence for `NTS_Foo ≃ Coq_Foo` + transport of theorems; synthetic topology native for JCT/curves/continuous claims; "equivalence proofs (or transport lemmas)" as the mandate.
- Generous but bounded axiom policy (`docs/axiom-policy.md` + README): one load-bearing axiom (typically univalence) per major piece, with mandatory header justification tied to the C# linkage story. No recreation of the old audit theatre for new work.
- Preserved personas + RGR discipline (HELP.md, READING-GUIDE.md, FOR-AI-AGENTS.md): Newbie Nate still starts with pythagoras; Scholar Sam / Quality Gatekeeper now review "justification and the linkage value of the one axiom" + equivalence claims; session workflow (Red/Green/Refactor + explicit stopping conditions + two-route design) is kept and explicitly said to apply to "HoTT modules + equivalence proofs".
- Archive as precedent mine + negative results: all the classical lemmas, proof structures, seam maps, counterexamples, and the old oracle protocol are available for transport/re-expression or as "what not to repeat."
- Single clean entry point + policy doc: easy onboarding without drowning in 1,100 theorems.

**OPEN / candidate targets for "proving the link" (in rough order of ambition):**

- Small equivalence examples for core primitives (e.g. Point, Orient, Distance).
- Revive/improve oracle as pragmatic bridge while building formal equivs on top.
- Synthetic re-expression of key topological results (JCT, overlay) using HITs/paths.
- Full model of NTS types + proofs that NTS impls satisfy the formal specs via equiv.
- Extraction/FFI story in a HoTT setting.

## Risk/cost of the candidate next targets (for proving the link)

| target | linkage value | risk (tractability / contributor impact) | cost (setup + per-result) |
|--------|---------------|------------------------------------------|---------------------------|
| **Small primitive equivalences first** (e.g. formalise a minimal NTS.Point / NTS.Orient in Coq/HoTT, prove `NTS_Orient ≃ Coq_Orient` or transport a simple soundness property; start with pythagoras-style example lifted to equiv) | **high** — delivers concrete, shippable artefacts early ("we have proved the C# orientation logic is equivalent to the verified model and can transport X"); demonstrates the HoTT value prop immediately; low barrier to first PRs for personas | **low** — scoped to one or two types/predicates; uses the allowed univalence axiom with clear header justification; can re-use classical lemmas from archive via transport where they apply; personas (Newbie Nate can do the example, Scholar Sam audits the equiv claim) | **low–medium** — one bounded session for first example + doc; no Flocq/container needed initially; can live in new `theories-hott/` or `link/` with minimal _CoqProject |
| Improve/keep old oracle as the *pragmatic* link while HoTT equivalences are built | medium — re-uses existing investment and gives NTS.Curve something to consume today | low (known quantity) | low (mostly archive) but ongoing maintenance cost remains |
| Synthetic JCT / topology layer (HITs for circles, paths for continuous interiors, univalent transport of labels) | high — directly attacks the "continuous" seams that were hard in classical point-set style (see archived JCT work) | medium–high — synthetic geometry in HoTT is powerful but requires comfort with HITs / higher paths; fewer existing libraries/examples for computational geometry | high (multiple sessions, new concepts for most personas) |
| Re-implement large parts of the classical corpus synthetically | high in theory (cleaner, more transportable) | **high** — risk of recreating the 1,100-theorem maintenance burden in a new foundation; contributor churn (HoTT learning curve) | **very high** — multi-year again |
| Focus on extraction/FFI story in HoTT from day one | medium (if it works, better than classical extraction) | **high** — HoTT extraction is known to be more restricted (higher inductive types, univalence often break computability or require axioms); may not deliver the old oracle_bin equivalent easily | high + uncertain (tooling risk) |
| Broad "prove NTS.Curve is sound" headline without small stepping stones | very high (the dream) | **very high** — same scaling problem as old Phase 0-7; no clear path from skeleton | very high, high chance of deferreds/conditionals reappearing |

## Decision (the pivot)

1. **STOP treating the old oracle + bit-exact testing as the primary/only "link".** It was a valuable pragmatic bridge (and the archive preserves the protocol, the migration history, and the soundness findings), but it never delivered a *proof* that the C# code is equivalent to the formal model in a way that transports properties. Continuing to invest heavily there would be high ongoing cost for marginal improvement in linkage strength.

2. **PIVOT to "small, high-value HoTT equivalences for core primitives" as the recommended first-class linkage mechanism.** Start with the lowest-risk / highest-marginal-value square: one or two concrete examples (e.g. a `Point` record + the `Orient` predicate, or the squared-distance Pythagorean fact from the kept pythagoras example lifted to an equivalence statement). 

   - Prove (or sketch) `NTS_Orient ≃ Coq_Orient` (or whatever minimal model of the NTS side we write) + transport at least one simple property.
   - Use the one allowed axiom (univalence) explicitly justified in the header *because* it enables the transport that makes the C# link meaningful.
   - Keep the old oracle running in parallel as the *execution* / differential-test bridge (low risk).
   - Mine the archive for classical lemmas that can be re-expressed or transported rather than re-proving everything from scratch.

   This is the risk/cost-optimal path: bounded per-result cost (1-3 sessions), low execution risk (small scope, re-use of RGR discipline and personas), immediate value (tangible "we proved the link for X" artefacts that can be cited in NTS issues/PRs), and directly exercises the HoTT strengths advertised in the pivot README.

3. **Defer synthetic JCT / large re-implementations and broad extraction experiments.** They are the right long-term direction but only after we have a few small equivalences under our belt that prove the methodology works for NTS contributors. Do not start them before the first primitive link is Qed-closed and documented.

4. **Update the "prove the link" backlog** in persona paths and FOR-AI-AGENTS to reflect this: first contributions for Newbie Nate / Consumer Connie / NTS-Upstream Norm can now be "port a tiny NTS primitive to a Coq model + prove the equiv + transport one fact", rather than "smallest deferred in the old registry".

### Why this is the risk/cost-optimal pivot

The classical linkage had low *per-proof* risk (once the heavy foundation was paid) but high *linkage risk* (the connection to real C# was always empirical + manual) and high *maintenance cost* (the whole apparatus). HoTT flips the trade-off: higher conceptual cost per person (univalence, synthetic style, learning curve) but potentially much stronger linkage (actual equivalences + transport) at lower long-term maintenance (smaller, more reusable theories, generous axiom policy, no need to re-audit everything).

Small equivalences first is the "Path 2" / regime-restricted bet that already worked for the classical project (integer-safe exactness, grid exactness, etc.). It converts the RED of "we have no formal statement that NTS code matches the model" into a constructive GREEN of "here is the equivalence and here is a transported theorem" in the exact regime that matters for a given primitive. Higher-ambition targets (full synthetic overlay, perfect extraction in HoTT) carry the same "blocked or intractable without new ideas" risk that C2 carried in the snap-rounding pivot.

The skeleton + "one axiom generous" + preserved RGR/personas make the cost of the first example deliberately low. We can fail fast on the methodology if the first equiv turns out to be more painful than expected, without having invested years.

## Future paths left open

- Once a couple of primitive links land, re-evaluate cost of expanding the equivalence layer (e.g. to full `RobustLineIntersector` model or to curve types).
- Investigate whether a lightweight "NTS model" layer (records that mirror C# class shapes + axioms for their behaviour) + equivalence proofs is cheaper than trying to extract or port the full algorithms.
- Keep the archived oracle as the *runtime* reference for as long as it is useful; the HoTT equivalences are the *formal* story.
- If HoTT extraction turns out to be viable for some fragments, that becomes a bonus (univalence for "the extracted term is the same up to homotopy").
- Revisit the old "conditional headline" pattern: an equivalence proof itself can be conditional on a small number of named hypotheses about the NTS side.

---

This pivot keeps the spirit of the original project (rigorous, no silent stubs, actor-specific docs) while changing the *kind* of artefact we ship: not another 100 Qed theorems in a classical corpus, but explicit, transportable proofs that specific pieces of real NTS C# are linked to verified formal statements.

Next concrete step (Green deliverable of this session): the first small equivalence example can be proposed as a follow-on session (Red: pick Orient or Distance; Green: model + equiv + transport; Refactor: update this doc + personas if needed).

References to prior RGR style: see `archive/docs/snap-rounding-rgr-pivot.md`, `archive/docs/soundness-strategy.md`, `archive/docs/issue-64-arc-primitives-triage.md`, and the session workflow in `docs/FOR-AI-AGENTS.md`.

## Session outcome: "Prove voronoid equivalence" (this RGR cycle)

**RED (re-stated for this slice).** Voronoi diagrams are mentioned aspirationally in the archived classical corpus (Triangle.v: "triangulations, and Voronoi diagrams can cite them"; ArcOrient.v has Delaunay/incircle dual; Tin.v mentions Delaunay). No Voronoi.v or equivalence to NTS existed. The old linkage (oracle for InCircle etc.) was pragmatic but not a formal NTS ≃ formal proof. High risk of scope creep if we tried a full Voronoi re-implementation.

**GREEN (delivered).** Created `theories-hott/VoronoiEquivalence.v` as the first live HoTT source (in the directory recommended in root README). It:
- Re-expresses minimal shared geometry (Point, dist_sq) from the kept pythagoras + archived Triangle.
- Defines formal geometric VoronoiDiagram (cell predicate based on closer-to-site).
- Defines NTS-side model (NTSVoronoi / NTSVoronoiDiagram mirroring observable C# behaviour).
- States the core `voronoi_equiv` : Equiv (formal) (NTS model).
- Sketches transport of a "cell is closest" theorem using the one allowed axiom (Univalence) — exactly as permitted and documented in `docs/axiom-policy.md` and the header of the new .v.
- Explicitly references archived Delaunay/incircle foundations (the dual) and InCircle_b64 oracle for future b64 instance.
- Header documents the axiom use tied to the C# linkage story (per policy).
- Admits are intentional placeholders for bounded scope (1 deliverable: the equivalence skeleton + transport example shape). Full proof is explicitly noted as next bounded session.

The file lives in `theories-hott/` (new, outside archive) and is the concrete start of "HoTT modules + equivalence proofs".

**Risk/cost of this step vs. alternatives.** Matches the table in the main pivot: small primitive equivalence = high value (first "we have a proved NTS Voronoi link" artefact), low risk (scoped, re-uses RGR + one-axiom + archive precedents), low-medium cost (skeleton only; no full diagram data structures yet). Avoided the high-risk "full Voronoi from scratch" or "synthetic everything at once".

**Refactor / cross-refs.** This doc updated with the outcome. (README, FOR-AI-AGENTS etc. already point to the RGR strategy; the new .v is the first realization of the "small equivalence" path.)

**Stopping conditions met.** Doc + first .v delivered. No tangents pursued (e.g. no full implementation of cells/edges, no build system yet, no attempt at classical re-proofs). Explicit "next session" call-out for filling the proof.

This is the Green implementation of the RGR pivot's #2 decision. The "voronoid equivalence" is now stated in HoTT terms with the linkage mechanism (univalence transport) in place.

**Follow-on (this loop).** See `docs/hott-rgr-tin-hobby-shewchuk-curve-pivot.md` (the next chunk RGR) and `docs/HoTT-Status.md` (living table). Shewchuk base was selected as the highest-leverage next small equiv (root predicate for Voronoi/Delaunay + Hobby + TIN + curves). The skeleton landed on `feature/hott-rgr-shewchuk-fill`; fill of the real proofs is the explicit next bounded step.