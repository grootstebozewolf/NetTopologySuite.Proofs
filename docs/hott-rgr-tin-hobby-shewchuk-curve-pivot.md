# HoTT: TIN / Hobby / Shewchuk / Curve — RGR pivot on risk/cost

**Status.** Written on branch `feature/hott-rgr-pivot` (branched from `hott` per "Create a new branch from hott feature/hott-rgr-pivot then RGR next big chunk"). This applies the preserved Red/Green/Refactor discipline (see `docs/FOR-AI-AGENTS.md`) to the *next big chunk* after the initial small-equivalence pilot (Voronoi in `theories-hott/VoronoiEquivalence.v` and the risk/cost pivot in `docs/hott-rgr-risk-cost-pivot.md`).

The chunks:
- **TIN** (`theories/Tin.v`, `CurveLinearise.v`, `Linearise.v`, `Simplify.v`, `Validate*.v`): curve linearisation stack + adjacent TIN merging via Douglas-Peucker + Delaunay (endpoint preservation for adjacency).
- **Hobby** (`theories-flocq/HobbyTheorem_b64.v`, `HobbyCounterexample_b64.v`, related in buffer/overlay): snap-rounding noder, Hobby 4.1 conditional, 4.3 refuted as counterexample.
- **Shewchuk** (B64_*_Shewchuk*.v, expansions in `theories-flocq/`): adaptive filter arithmetic (Stage D etc.), Thm 13 general non-overlap deferred; foundation for robust orientation/intersection.
- **Curve** (`theories/Arc*.v`, `Curve*.v`, `ArcOverlay.v`, phase4 audits): arc primitives (orient, intersect, hotpixel, chord approx), linearisation faithfulness (Qed combinatorial), conditional headlines for native/overlay.

These are the "mid-to-late" foundational + curve/snap/expansion work from the classical roadmap (see archived old README phases 0/2/4 + curve linearisation). They are big because interconnected (Shewchuk preds feed Hobby noding which is used for curve buffer/overlay; TIN/linearise is the current practical path in NTS .Curve extension; curves dual to Delaunay which uses incircle/Shewchuk-like tests).

This RGR decides the risk/cost-optimal way to "prove the link" for these in the HoTT pivot (small HoTT equivalences to NTS types/impls + transport of archived classical results, per the previous pivot's recommendation). Same shape as `archive/docs/snap-rounding-rgr-pivot.md` and the HoTT linkage RGR.

## Where the RGR cycle stands (post small Voronoi pilot + skeleton)

**RED — these chunks in classical have mixed status (some Qed, many conditional/deferred), and the linkage to real NTS is pragmatic but not first-class formal equivalence.**

- **TIN / linearisation**: 
  - `Tin.v`: Qed-closed for `same_source_share_endpoints*` (head/last preservation under simp_star / perp / mixed — enough for adjacent TIN merging even without full determinism of Douglas-Peucker). Depends on Linearise/Simplify.
  - `CurveLinearise.v`: Qed-closed for combinatorial faithfulness (`chord_approx_ring_closed`, outer/hole rings closed for valid curve rings; `to_geometry` produces valid Phase-3 Geometry structure). Pure-R, 3-axiom.
  - `Linearise.v`, `Simplify.v`, `Validate*.v` + b64 in flocq: the stack for Douglas-Peucker + greedy perp + TIN + binary64 instance (some structural Qed, soundness bridges deferred in places).
  - Linkage: NTS .Curve extension (and upstream curved work) relies on linearisation (`Flatten()` or equivalent) before any robust op. Oracle has modes for curve predicates. No formal "NTS linearised curve ring ≡ formal" equiv; the practical path is the bridge.
  - Risk in classical: high volume of list/ring algebra; deferreds in Validate for full soundness.

- **Hobby (snap-rounding noder)**:
  - `HobbyTheorem_b64.v`: `hobby_theorem_4_1_conditional` Qed (under fully_intersected input + no-proper-intersect hyp). Lemma 4.2 closed; 4.3 no-proper is counterexample (refuted in `HobbyCounterexample_b64.v`, now Tier-2 admitted).
  - Related: `TopologicalCorrectness_b64.v`, `SnapRounding_b64.v`, HotPixel, PassesThrough (some Qed, some incomplete/unsound for rounded filters — see old RGR pivot that demoted rounded filter).
  - Linkage: core for Phase 2 noding in buffer/overlay; oracle PASSES_THROUGH* modes extracted or handrolled. Used in curve buffer too (offset curves noded via Hobby).
  - Status: conditional headline; exact noder primitive recommendation was pivoted to exact R-spec in old work.

- **Shewchuk (expansion arithmetic)**:
  - Many `B64_Expansion*`, `B64_FastExpansionSum*`, `Orient_b64_expansion.v`, `B64_Shewchuk_Thm13*` etc.
  - Small/int regime exactness Qed (e.g. in Orient_b64_exact_full, stage A/B etc.).
  - General Thm 13 `fast_expansion_sum_nonoverlap_shewchuk` is registered deferred (Route 2 collapsed in sessions; Path A has defects, Route 1/2 analysis in shewchuk-thm13 doc).
  - `B64_bridge.v` Qed for basic ops.
  - Linkage: foundation for all robust predicates (orient, intersect) in NTS Robust* and .Curve. Oracle uses for exact/filtered. b64 layer critical for bit-exact with C#.
  - Risk: arithmetic proofs are deep (forward error, non-overlap); expansions grow; Flocq layer adds axiom footprint.

- **Curve (native arcs / CIRCULARSTRING)**:
  - `CurveGeometry.v`, `Arc*` (ArcOrient, ArcIntersect, ArcHotPixel, ArcChordApprox, ArcOverlay, ArcLength): types + bridges, arc-orient, arc-arc/chord intersect (IVT gap closed), hotpixel, sagitta, conditional `arc_overlay_correct_chord_approx`.
  - `CurveLinearise.v` as above (Qed structural).
  - Phase4 audits: chord paradigm sticky due to NTS/JTS SegmentString/Coordinate[] architecture; linearisation forced; predicates layer is the clean seam for arc-aware.
  - Linkage: NTS has `NetTopologySuite.Curve` extension (playground status upstream); uses linearise + chord predicates. Oracle has INCIRCLE, ARC_* modes. High consumer interest for CIRCULARSTRING but stalled 5+ years.
  - Status: combinatorial Qed, analytic/overlay conditional (named hyps for JCT etc.); native non-chord far future.

Overall RED: these are the "chokepoint + curve" work (phases 0/2/4 + linearisation). Linkage was via oracles + differential tests + some extracted (e.g. InCircle for Delaunay which underlies Voronoi/TIN). High maintenance (Flocq, audits, admitted registries for deferreds like Thm13, hobby 4.3 counter). Interdeps make "big chunk" scary (Shewchuk → Hobby noding → curve buffer/overlay/TIN). Classical already did heavy lifting (many Qed), but no HoTT equivs yet.

**GREEN — assets from HoTT skeleton + prior RGR pilot.**

- Root vision + `docs/axiom-policy.md`: one load-bearing axiom (Univalence) per major piece, justified by C# linkage value + transport. No full classical audit theatre for new HoTT work.
- Preserved RGR + personas: this session itself; Newbie Nate can do small equivs; Scholar Sam audits equiv claims + one-axiom justifications; Tech-Lead Tess uses seam maps / two-route / risk/cost.
- Previous RGR decision (`docs/hott-rgr-risk-cost-pivot.md`): pivot to *small, high-value HoTT equivalences for core primitives* as linkage mechanism (e.g. `NTS_Foo ≃ Coq_Foo` + transport). VoronoiEquivalence.v as pilot (first theories-hott/ source, states Equiv for formal vs NTS model, uses Univalence for "cell is closest" transport, refs archived foundations).
- Archive as mine: full classical results for these chunks (Qed proofs, counterexamples, proof structures, seam maps, retros, oracle protocol for linkage). Can re-express or transport lemmas (HoTT strength) instead of re-proving from scratch. E.g. transport TIN endpoint preservation or Hobby conditional into HoTT equiv.
- Skeleton: pythagoras as on-ramp (can be lifted to HoTT equiv example); no bloat; _CoqProject.hott for HoTT builds.
- Interconnections are opportunities: Delaunay (incircle/Shewchuk) dual to Voronoi (already piloted); Hobby noding used by curve ops; linearise is the NTS path today (high linkage value for .Curve consumers); Shewchuk is base for all robust (orient/intersect used everywhere, including arcs).

**OPEN — candidate targets / ways to chunk the big chunk for HoTT linkage.**

- Small equivs for predicate cores (arc-orient/incircle using Shewchuk-like expansions; passes-through from Hobby).
- Equiv for linearisation bridge (NTS curve ring linearised ≡ formal Phase-3 ring; transport combinatorial Qed from CurveLinearise).
- Equiv for noder primitive (NTS snap_round_segments ≡ formal Hobby).
- Synthetic curve types (HIT for S¹ arcs, paths for continuous claims) — high reward for topology.
- Full b64 instances + oracle equiv for these.
- Re-use classical via transport (e.g. once a Point/segment equiv is there, lift TIN adjacency, etc.).

## Risk/cost of the candidate next targets / chunking approaches

| target / order | linkage value (to NTS) | risk (tractability, HoTT fit, contributor) | cost (per small step + overall) |
|----------------|------------------------|---------------------------------------------|---------------------------------|
| **Shewchuk expansions first** (small equiv for b64 expansion ops / non-overlap in tiny regime; lift to arc-orient/incircle predicate equiv; transport small-int exactness Qed) | **high** — foundational for *all* robust predicates in NTS (RobustOrientation, RobustLineIntersector, .Curve arc-aware). Direct bit-exact consumers. Voronoi/Delaunay/TIN depend on it. | **low** — arithmetic already has b64 bridges Qed; small-regime equivs are "Path 2" style (regime-restricted, like old integer-safe orient); HoTT can use equivs for exactness witnesses; re-use archived routes/sessions for negative results. One axiom (Univalence) for transport of error bounds. Low learning for predicates team. | **low–medium** — bounded sessions per helper (e.g. TwoSum equiv first); builds on Voronoi pilot. Overall chunk cost reduced by reusing classical analysis. |
| **Hobby noder equiv next** (equiv for snap_round_segments / passes-through predicate; transport conditional 4.1 + exact R-spec recommendation; small step for rounded vs exact filter) | **high** — the noder primitive for Phase 2/ buffer/overlay on (curve) segments. Used in curve offset noding. Oracle modes directly map. | **low–medium** — conditional headline + counterexample already analyzed in old RGR (demoted rounded filter); exact spec is Qed-ish. HoTT good for "preserves fully_intersected" as path/equiv property. Risk in b64 layer (Flocq axiom) but scoped. | **medium** — one RGR per lemma (4.2 already closed classically); can do predicate equiv without full expansions first. |
| **TIN / curve linearisation** (equiv for simp_star endpoint preservation (transport Tin Qed); chord_approx_ring faithfulness (transport CurveLinearise combinatorial Qed); NTS curve ring → linearised ≡ formal) | **very high** — the *current practical linkage* in NTS .Curve (linearise before robust ops). TIN for generalisation/DEM. High consumer value (CIRCULARSTRING support via chords today). | **low** — many structural Qed already (endpoints, closed rings); combinatorial, list/ring algebra ports well to HoTT (or transport). Linearise is the "bridge" NTS actually ships. Synthetic paths/HITs can enhance later for native. | **low–medium** — smallest steps: equiv the simp_star head/last, then the ring closed property. Re-use classical proofs via transport. Bounded because Qed parts are "free". |
| **Native arc curve equivs (full ArcOrient/Intersect/HotPixel/Overlay for CSArc without chord approx)** | high (the dream for native CIRCULARSTRING without Flatten) | **high** — NTS/JTS architecture (SegmentString/Coordinate[]) forces linearise; predicates seam is clean but full native requires lifting noding/overlay too (big interdep with Hobby/Shewchuk). HoTT synthetic (S¹ HIT, winding as paths) fits topology but high conceptual cost + may need more than 1 axiom or custom layer. Contributor risk high (few HoTT geometry examples). | **high** — multi-session per primitive; depends on prior chunks (preds + noding). Risk of ballooning like old Phase 4. |
| **Broad "all at once" or synthetic everything first** | high | **very high** — recreates classical scaling problem in new foundation; interdeps (curve needs noding needs preds). | **very high** — years again. |

## Decision (the pivot)

1. **STOP treating these as one monolithic "big chunk" to port/re-prove classically or synthetically all at once.** The classical corpus already did the heavy lifting (many Qed, detailed proof structures, counterexamples, RGR retros in archive). Re-creating the volume or the full audit in HoTT would be high cost, high risk of stalling (like old Phase 4). The linkage goal is *not* "re-prove everything"; it's "prove NTS impl ≃ formal model for key observable behaviour" (small equivs + transport).

2. **PIVOT to chunked small-equivalence approach, in this risk/cost-optimal order** (building on Voronoi pilot + previous RGR decision):
   - **First: Shewchuk** (foundational predicates). Small equivs for expansion helpers + tiny-regime exactness (transport old Qed). Then arc-aware orient/incircle equiv (ties to curve/Delaunay/Voronoi). High value, re-uses b64 work + archived routes (negative results prevent tangents), low risk (regime-restricted like successful classical Path 2), fits one-axiom (Univalence for transporting error/non-overlap properties to NTS Robust*).
   - **Then: Hobby noder**. Predicate equiv for snap_round / passes-through (transport conditional + exact R-spec rec). Small steps for the filter vs exact distinction (per old RGR). High value for all noding (buffer/overlay on curves too). Medium risk (b64 + conditional already scoped).
   - **Then: TIN / linearisation stack**. Equiv for endpoint preservation (transport Tin Qed directly) + curve ring linearise faithfulness (transport CurveLinearise combinatorial Qed). This is the *highest immediate linkage value* because it's what NTS .Curve actually uses today. Low risk/cost because lots already Qed classically — HoTT gives the "NTS linearised ≡ formal" for free via equiv + transport. Enables plugging into overlay/buffer equivs.
   - **Stretch / later: native curve primitives + full synthetic**. Once the above give working linkage for the chord path + arc predicates, re-evaluate native (using synthetic S¹ / paths for the "continuous" claims that were hard classically). Defer until consumers (NTS upstream or .Curve) demand it and the base chunks are linked.

   This order minimizes interdep risk (preds → noding → linearise bridge → native), maximizes early value (predicates are used everywhere; linearise is shipped path), chunks the "big" into 1-3 session RGRs each (per RGR discipline), re-uses archive heavily (transport classical Qed into HoTT equivs), stays within one-axiom policy.

3. **Explicitly use HoTT strengths for linkage**: small `NTS_ShewchukExpansion ≃ formal` , `NTS_HobbyNoder ≃ formal` , `NTS_CurveLinearisedRing ≃ formal_Phase3Ring` etc. + univalence transport of properties (e.g. "noded output is fully_intersected" or "adjacent TINs share endpoints"). Keep pragmatic oracle bridge (archive/oracle) running in parallel for execution/diff tests. The formal equivs are the "prove the link" artefacts (citable for NTS issues, used by Scholar Sam audits, etc.).

4. **Update backlog / personas**: First contributions can target these small equivs (e.g. "port Shewchuk TwoSum to HoTT equiv + transport one non-overlap"). Tech-Lead Tess / Project Meta budget per small chunk. Quality reviews the one-axiom justification tied to NTS (e.g. "this Univalence lets us transport the Shewchuk exactness to C# RobustDeterminant").

### Why this is the risk/cost-optimal pivot

These chunks are "big" due to volume + interdeps + some open seams (deferred Thm13, conditional Hobby, architecture blocker for native curves). Classical RGRs already did risk/cost analysis (e.g. demoted rounded filter, Route 2 collapse for Shewchuk, chord vs native for curves). HoTT flips some risks (synthetic may simplify topology claims in curves/JCT) but adds learning + axiom cost — hence the generous one-axiom + small-steps mandate from prior pivot.

The recommended order is the "Path 2" bet that worked before: regime-restricted / bridge-first (linearise path + predicates) for quick value + linkage, with door open for native/synthetic later. Avoids high-risk "synthetic everything" or "full native first" (which would hit the NTS data-plane blocker immediately). Cost is bounded (small equivs reuse classical proofs via transport instead of re-proving); risk low (scoped, explicit stopping per RGR, negative results from archive sessions).

This directly advances the "prove the link between NTS and NTS.Proofs" using HoTT (equivalences + transport), while keeping the skeleton lean and personas engaged.

## Future paths left open

- After Shewchuk small equivs: b64 instance for arc predicates (transport + InCircle_b64 oracle).
- Integrate with Voronoi pilot (Delaunay dual uses incircle/Shewchuk).
- Once linearise equiv lands: equiv the full offset_curve + noding for buffer curves (ties Hobby + curve).
- Revisit native curves when base linked + upstream/NTS demand (use synthetic for the "why linearise is forced" diagnosis in phase4 audit).
- If HoTT extraction viable for some (e.g. linearise or simple noder), bonus for oracle.
- Conditional headlines pattern (from classical) can be reused: an equiv can be under named hyps about NTS side (e.g. "assuming NTS curve linearise matches formal chord_approx").
- Mine more from archive (hobby proof structure, shewchuk sessions, curve audits, buffer-noder-pipeline.md) for exact seams.

---

This RGR keeps the project rigorous (RGR + no silent stubs + one-axiom justified by linkage) while being practical for the "big chunk": chunk it, start with high-value/low-risk small equivs (Shewchuk → Hobby → TIN/linearise), leverage HoTT for the link (equiv + transport), reuse the classical investment in the archive.

**Next concrete step**: Propose bounded RGR session for first Shewchuk small equiv (Red: pick TwoSum or simple expansion; Green: model + Equiv + transport one property from archive; Refactor: update this doc + add to theories-hott/).

References: prior HoTT RGR `docs/hott-rgr-risk-cost-pivot.md` + Voronoi pilot; classical `archive/docs/shewchuk-theorem-13-proof-structure.md`, `archive/docs/hobby-theorem-proof-structure.md`, `archive/docs/audit-phase4-curves.md`, `archive/docs/audit-shewchuk-stages.md`, `archive/theories/Tin.v`, `archive/theories/CurveLinearise.v`, `archive/theories-flocq/HobbyTheorem_b64.v`, B64 Shewchuk files, etc. Session workflow in `docs/FOR-AI-AGENTS.md`.

(Outcome of this session recorded here; changes on `feature/hott-rgr-pivot`.)