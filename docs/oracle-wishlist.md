**✅ Oracle Wishlist v6.0 – Phase 1 Complete Dashboard** (19 Jun 2026)  

**🎉 Milestone achieved**: All low-risk analytical primitives + lifts + basic noding + predicates **COMPLETE**.  
**TAGs shipped**: D-PT, C-LIN, D-AA, OFF, C-AREA, composites, D-CURVE, BUF-S, N-SS, R-CURVE (10+ vertical slices, all green with oracle matches).  
**Impact**: NTS.Curve now has solid analytical foundation for Distance, Centroid, Area, Offset, Buffer-Simple, basic noding/split, and topological predicates — all RGR-pinned. Low-risk phase done. Ready for core seams.

**Guiding Principles** (still enforced): Low-risk analytical first → pinnable RGR → reuse proofs math → SAFE_INT + BigDecimal → defer full overlay.

### Accepted TAGs (compact)
- **Distance** (D-PT/D-CURVE/D-AA): Full leaf + CS/CC lifts ✅
- **Centroid/Area** (C-LIN/C-AREA + composites): Enclosed + Polygon/Compound ✅
- **Offset/Buffer** (OFF + BUF-S): Leaf + single-arc CurvePolygon ✅
- **Intersections/Noding** (N-AA/N-AL + N-SS basic split): Sub-arc exact ✅
- **Relate/Predicates** (R-CURVE): Intersects/Contains/Relate wiring ✅

All with tests (4/4–20/20), code refs, oracle matches, and minimal changes.

### Current Oracle Modes
✅ ARC_DISTANCE family, ARC_ARC_DISTANCE, ARC_CENTROID, ARC_AREA_CENTROID, ARC_OFFSET_XY, ARC_BUFFER_SIMPLE, N-AA/N-AL, relate_matrix partial, V-CP, PRC-SN + recent buffer/ring/area gens.

### Remaining Roadmap (smart prioritisation)
| Priority | Item | Effort | Risk | Leverage | Action |
|----------|------|--------|------|----------|--------|
| High | Full adversarial + BigDecimal/ROCQ_REF_BIN harness across all accepted modes | 1 day | Low | High | Close RGR gaps |
| High | **ARC_BUFFER_FULL** (multi-arc, negative, self-intersect) | 3 days | Medium | Very high | Use BUF-S + N-SS |
| Medium | ARC_SIMPLIFY + ARC_SNAP | 2 days | Medium | High | Post-noding |
| Medium | Full CURVE_RELATE/DE9IM (holes, Multi, mixed) | 3 days | Medium | High | Extend matrix |
| Parked | Robust intersect, full noding engine, Shewchuk port | — | High | — | After seams stable |

**Recommended next**: **ARC_BUFFER_FULL** (builds directly on BUF-S + N-SS + OFF) or robustness hardening pass.

### Reusable Templates
**RGR Pattern** (used for every slice): Read (grep fallback) → Red (analytical test) → Green (minimal reuse) → Refactor (tiny + comment) → Pin + Cake + oracle match → Accept.

**Oracle Add SOP**: Protocol keyword → OCaml/Coq + lemma → Extract → RocqRefRunner → Generator → NTS harness → Cake → bump this file.

**Verification command** (standard): `dotnet test ... --filter "Distance|Offset|Centroid|Area|Buffer|Intersects|Relate|Split"` + oracle probes.

### How to Keep This File Smart
- New accept → add 1 row to Accepted table + bump version/date + one-line note.
- New wishlist item → add to Remaining table only.
- No full RGR stories here (keep in PRs/commits for audit).

References unchanged.  

**File updated** ✓ Bloat eliminated, progress celebrated, Phase 1 closed, Phase 2 crystal-clear, future updates easy.  

This is now the official maintainable plan. Ready to ship ARC_BUFFER_FULL Red test or any other action? 🚀
