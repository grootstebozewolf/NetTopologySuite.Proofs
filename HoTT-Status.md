# HoTT Status Tracker

Lightweight visibility table for the HoTT exploratory track (see `docs/hott-rgr-*.md` for detailed RGR pivots and strategy).

**Stages** (per RGR discipline):
- **RED** — Problem / risk / cost analysis phase. Target defined, tangents listed, stopping conditions explicit.
- **GREEN** — Deliver the minimal viable artifact (small equivalence skeleton, predicate model, transport example, etc.). Keep scope bounded (1-3 deliverables).
- **REFACTOR** — Clean up, integrate with project files (`_CoqProject.hott`, README, cross-refs), ensure one-axiom policy compliance, update status table.

| Chunk / Area          | Current Stage | Key Artifact(s)                          | Notes / Next |
|-----------------------|---------------|------------------------------------------|--------------|
| Voronoi equivalence (pilot) | GREEN (complete) | `theories-hott/VoronoiEquivalence.v` | First small `NTS_... ≃ formal` using Univalence for transport. References archived Delaunay/incircle. |
| Shewchuk (expansions / predicates base) | GREEN (skeleton started) | `theories-hott/ShewchukBaseEquiv.v` | Recommended first real step per tin/hobby RGR. Minimal Equiv/IsEquiv + one-axiom justification. Full small equiv (e.g. TwoSum + transport of archived exactness) in next bounded RGR. |
| Hobby (snap-rounding / noding) | RED | — | Next after Shewchuk. Predicate equiv for `snap_round_segments` / passes-through; transport conditional 4.1. |
| TIN / Linearisation (curve bridge) | RED | — | High immediate NTS `.Curve` linkage value. Transport combinatorial Qed from `CurveLinearise` + endpoint preservation from `Tin`. |
| Curve / Native arcs (phase 4) | RED | — | Stretch. Start with chord/linearise path; revisit native once base linked. |
| General / Cross-cutting | — | `docs/hott-rgr-risk-cost-pivot.md`, `docs/hott-rgr-tin-hobby-shewchuk-curve-pivot.md`, `docs/axiom-policy.md` | One load-bearing axiom (Univalence) per major piece, justified by C# linkage. Reuse archived classical results via transport. |

**Legend / Process**
- Every chunk follows the RGR workflow documented in `docs/FOR-AI-AGENTS.md`.
- "Small high-value equivalences first" strategy (see risk/cost pivots).
- Update this table at the end of each RGR Green/Refactor phase.
- Classical corpus remains fully archived and available for reference/transport under `archive/`.

Last updated: $(date +%Y-%m-%d) (post PR #89 review polish)