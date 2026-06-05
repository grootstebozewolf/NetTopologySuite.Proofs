# HoTT Status — Current Chunks and Process

**Intro.** This is the living visibility document for the HoTT pivot (post the initial refactor commit and the Voronoi pilot). It records the bounded RGR chunks we have open, their status, and the explicit "next" so that the loop (create unique feature/ branch from hott, RGR a slice, /check-work, pause) stays on track.

See root `README.md` (Current state + Axiom policy), `docs/hott-rgr-risk-cost-pivot.md` (the linkage strategy decision), and `docs/hott-rgr-tin-hobby-shewchuk-curve-pivot.md` (the chunk plan that selected Shewchuk base first).

**Hard rule (repeated for every RGR):** one axiom only when justified (univalence for C# transport/linkage value), documented in the .v header, rest Qed/Defined or loud Admitted with discharge plan. No silent stubs. Archive is source, not to be edited for new work.

## Current Chunks

| Chunk / Area              | Status                          | Key Artefact(s)                              | Next (bounded) |
|---------------------------|---------------------------------|----------------------------------------------|----------------|
| Voronoi pilot             | GREEN skeleton (first small equiv) | `theories-hott/VoronoiEquivalence.v` (Point, voronoi_cell Prop, NTSVoronoiDiagram, voronoi_equiv Admitted, transport sketch via univalence, compiles) | Fill admits (port minimal Triangle/Orient + incircle from archive); strengthen with orient_equiv once Shewchuk base lands; add b64 instance later. |
| Shewchuk base (orient/expansion) | GREEN skeleton ("first recommended small step") | `theories-hott/ShewchukBaseEquiv.v` (Point + cross, Dir CCW/CW/COLLINEAR, formal/exact_orient, shewchuk_orient via Expansion, nts_orient, orient_equiv Admitted, one univalence justified for root-predicate transport, antisym transport example, loud notes) | **Fill real proofs**: turn the Admitted into Qed using B64_Expansion_Shewchuk.v + sign_of..._correct_shewchuk + Orient_b64_exact/sound + Orientation.v invariants (one transport lemma). Then cite from Voronoi/Hobby/TIN. |
| Hobby (4.1/4.3 biarc/residual) | RED (no HoTT model yet)        | Archived `theories-flocq/HobbyTheorem_b64.v`, `HobbyCounterexample_b64.v`, `docs/hobby-lemma-4-3-no-proper-refutation.md` etc. | After Shewchuk orient base is solid: re-express or transport the b64 Hobby lemmas as NTS_Hobby ≃ formal via orient_equiv. |
| TIN / CurveLinearise      | RED (some classical Qed, no equiv) | Archived `theories/Tin.v`, `theories/CurveLinearise.v` (linearise faithfulness Qed for CIRCULARSTRING/COMPOUNDCURVE) | After Hobby + Shewchuk: model NTS TIN + prove linearise equiv; use transported orient facts. Defer native curves. |
| Curve (Arc* / phase4)     | RED (conditionals + linearise) | Archived `theories/ArcOrient.v`, `ArcIntersect.v`, `Arc*` phase4 conditionals | After TIN linearise: revisit; decide whether native HIT curves are needed for the C# link given SegmentString forces linearise in NTS. |
| Incircle / Delaunay (cross-cut) | RED (depends on orient)     | Archived `theories/ArcOrient.v`, `theories-flocq/InCircle_b64_compute.v`, Tin mentions | After Shewchuk base: add as the dual predicate; strengthen Voronoi. |

**Process (how we keep the loop healthy)**

- RGR always starts on a unique `feature/hott-rgr-...` branch from `hott` (never main, never directly on hott for risky slices).
- Every new .v or major update gets a sibling RGR doc (or appends to an existing chunk doc) with RED/GREEN/table/Decision + Session outcome.
- HoTT-Status.md table is updated on each RGR close (this is the single source of "what is GREEN vs RED" and "what is next").
- One axiom per major piece, justified in header by the C# linkage value it buys (transport of theorems that NTS actually calls). Scholar Sam / Quality Gatekeeper review the justification + the actual equiv claim.
- Archive/ is read-only mine + negative results. We transport/re-express, we do not edit the classical corpus for new HoTT work.
- Self-verify with `/check-work` (or manual evidence + ls/grep/git show if subagent infra flakes) before pause or PR.
- PRs target `hott` (not main). Merge commits use the recommended message from the RGR doc.
- Bounded scope per slice: 1-3 deliverables (e.g. "skeleton + doc + status update"). "Next" is always explicit so the loop can continue without analysis paralysis.
- When a fill (turning Admitted -> Qed) lands, it counts as its own RGR close and updates the table row.

**Current overall state (post this RGR).** Voronoi pilot + Shewchuk base skeleton are the only live HoTT sources under `theories-hott/`. The "prove the link" mandate is now concretely started for the root predicate (Shewchuk/orient) that the rest of geometry trusts. The risk/cost-optimal path (small equivalences first) is being followed.

Update this table + add a one-paragraph outcome note to the relevant hott-rgr-*.md on every close of a branch/PR.

See also: `docs/axiom-policy.md`, `docs/FOR-AI-AGENTS.md` (HoTT-era hard invariants + session workflow), `docs/READING-GUIDE.md` / `HELP.md` (personas updated for equivalence work).

Last updated: this RGR (feature/hott-rgr-shewchuk-fill).
