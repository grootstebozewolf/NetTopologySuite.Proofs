# HoTT Status — Current Chunks and Process

**Intro.** This is the living visibility document for the HoTT pivot (post the initial refactor commit and the Voronoi pilot). It records the bounded RGR chunks we have open, their status, and the explicit "next" so that the loop (create unique feature/ branch from hott, RGR a slice, /check-work, pause) stays on track.

See root `README.md` (Current state + Axiom policy), `docs/hott-rgr-risk-cost-pivot.md` (the linkage strategy decision), and `docs/hott-rgr-tin-hobby-shewchuk-curve-pivot.md` (the chunk plan that selected Shewchuk base first).

**Hard rule (repeated for every RGR):** one axiom only when justified (univalence for C# transport/linkage value), documented in the .v header, rest Qed/Defined or loud Admitted with discharge plan. No silent stubs. Archive is source, not to be edited for new work.

## Current Chunks

| Chunk / Area              | Status                          | Key Artefact(s)                              | Next (bounded) |
|---------------------------|---------------------------------|----------------------------------------------|----------------|
| Voronoi pilot             | GREEN skeleton (first small equiv) | `theories-hott/VoronoiEquivalence.v` (Point, voronoi_cell Prop, NTSVoronoiDiagram, voronoi_equiv Admitted, transport sketch via univalence, compiles) | Fill admits (port minimal Triangle/Orient + incircle from archive); strengthen with orient_equiv once Shewchuk base lands; add b64 instance later. |
| Shewchuk base (orient/expansion) | GREEN (PR #90 + fill + orient-equiv slice on feature/hott-rgr-shewchuk-orient-equiv): id orient_equiv + univalence demo + nts_antisym Qed | `theories-hott/ShewchukBaseEquiv.v` (Point + cross + cross_antisymmetric, Dir, formal_orient def, degenerate + antisym Qed, shewchuk/nts aliases, orient_equiv as id IsEquiv, orient_types_equal_via_univalence using axiom, nts_antisym Qed; sign_of still Admitted; outcome appended + table updated) | **Next**: wire real IsEquiv/maps from B64_Expansion_Shewchuk.v + Orient_b64_*; update Voronoi etc. Update table on close. |
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

**Current overall state (post PR #90 merge + fill start).** Voronoi pilot + Shewchuk base skeleton (PR #90, fill branch active) are the live HoTT sources. Concrete formal_orient + first real Qed property landed as the start of discharging the link claims using the archive.

Update this table + add a one-paragraph outcome note to the relevant hott-rgr-*.md on every close of a branch/PR. (Table updated post-merge per PR #90 Notulist actionable.)

See also: `docs/axiom-policy.md`, `docs/FOR-AI-AGENTS.md` (HoTT-era hard invariants + session workflow), `docs/READING-GUIDE.md` / `HELP.md` (personas updated for equivalence work).

Last updated: orient-equiv RGR slice close on feature/hott-rgr-shewchuk-orient-equiv (id equiv + univalence demo + nts_antisym Qed + table refresh per process).
