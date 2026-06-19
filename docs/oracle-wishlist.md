**✅ Oracle Wishlist v4.0 – Clean Dashboard Edition** (Updated 19 Jun 2026)  
**Massive progress**: 7 analytical primitives now ACCEPTED (D-PT, C-LIN, D-AA, OFF, C-AREA core, composites lifts, D-CURVE full curve distance). Leaf primitives + key lifts complete. Document trimmed 70 % — no more repeated RGR stories.

**Quick Wins Summary**  
- All low-risk pure-analytical TAGs (distance family, centroid/area, offset, arc-arc) shipped with green tests + oracle matches.  
- Lifts to CircularString/CompoundCurve/CurvePolygon done for Distance, Centroid, Area, Offset.  
- 20/20 + 8/8 + 4/4 targeted runs pass; broader suites clean.  
- Proofs leverage confirmed (distance/offset/relate/buffer_region gens exist + DE-9IM coverage).

### Accepted Progress Dashboard
| TAG | Scope Accepted | Oracle Mode | Remaining Gap |
|-----|----------------|-------------|---------------|
| D-PT + D-CURVE | Arc + CS/CC Point + full curve-curve min (pairwise/ member) | ARC_DISTANCE / ARC_ARC_DISTANCE / COMPOUND partial | Full non-Point harness diffs |
| C-LIN + C-AREA | Arc + CS weighted + segment + enclosed (closed + Polygon delegate) + Compound lifts | ARC_CENTROID / ARC_AREA_CENTROID partial | Full holes/Compound in Polygon |
| D-AA | Leaf arc-arc + reuse Intersection | ARC_ARC_DISTANCE | Composite lifts |
| OFF | Leaf (signed + collapse/empty) + CS/Compound lifts | ARC_OFFSET_XY | Full buffer construction |
| N-AA/N-AL | Intersection tests | ARC_ARC_XY / ARC_SEGMENT_XY | — (full) |

**Verification stamp** (used for all accepts): `dotnet test ... --filter "Distance|Offset_|Centroid|SegmentArea|Enclosed|ArcCentroid"` → passes + oracle_bin probes match C# exactly.

### Current Oracle Modes (live)
- ✅ ARC_DISTANCE family, ARC_ARC_DISTANCE, ARC_SEGMENT_DISTANCE, ARC_CENTROID, ARC_AREA_CENTROID (partial), ARC_OFFSET_XY, ARC_ARC_XY / ARC_SEGMENT_XY  
- ✅ V-CP (rings), PRC-SN  
- Buffer/relate/ring gens recently added in Proofs.

### Remaining Wishlist (prioritised, no fluff)
**High (finish family)**
- Full COMPOUND_ARC_DISTANCE (non-Point) + exact BigDecimal/adversarial RGR harness for all distance modes
- Expand ARC_AREA_CENTROID to full holes/Compound in CurvePolygon + Area override

**Medium (next cheap)**
- **ARC_BUFFER_SIMPLE** (single → CurvePolygon + round caps; leverage recent buffer_region gen)
- N-SS (basic arc noding/split with exact sub-arcs) — lowest-risk entry to core

**Parked**
- ARC_ARC_INTERSECT_ROBUST, CURVE_NODING full, CURVE_RELATE/DE9IM full, ARC_BUFFER_FULL, ARC_SIMPLIFY, ARC_SNAP, filtered/uncertain/SAFE_BOUND/hot-pixel

**Cross-cutting** (apply to every new mode)
- Adversarial generators + SAFE_INT + BigDecimal ref + ROCQ_REF_BIN diffs.

### Reusable RGR Pattern (all runs followed this)
Read (grep Linearize/fallbacks/enumerator/prior primitives) → Red (analytical assert that would fail linearize) → Green (minimal reuse of Center/Radius/Enumerator/previous helper) → Refactor (tiny + comment) → Oracle pin + tests green + match → Accept.

### How to Ship Next (5-step SOP)
1. Pick → Read/grep.
2. Red test.
3. Green NTS (reuse pattern, <20 LOC).
4. Proofs: extend mode (leverage existing gens) → extract → RocqRefRunner.
5. Cake RGR + update this file.

**Oracle reality** (19 Jun): Proofs has buffer_region, cp_ring, holes, relate gens + distance/offset coverage → perfect for next slice. No duplication.

**Recommended Next TAG**: **ARC_BUFFER_SIMPLE** (or N-SS if you want noding seam first).  
Rationale: Leverages recent Proofs buffer gen + OFF/Distance/Centroid family; low risk; huge leverage for full buffer/relate.

**Action items (now)**
- Pin remaining adversarial for distance family.
- Ship ARC_BUFFER_SIMPLE slice.
- PR + merge this doc as v4.1.

References unchanged.  
**File updated** ✓ All accepts consolidated, repetition removed, dashboard + table added, forward-focused, scannable for team.  

Ready for ARC_BUFFER_SIMPLE Red test or the exact next-mode stub? Just say go. 🚀
