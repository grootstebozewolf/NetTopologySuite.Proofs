**✅ Oracle Wishlist v4.0 – Living Dashboard Edition** (19 Jun 2026)  
**Progress**: D-PT + C-LIN + D-AA + N-AA/N-AL **ACCEPTED** (4 slices shipped) | Remaining analytical primitives: 3 high-priority | Oracle leverage maximised  

**Update rule**: Replace this entire file on TAG pick / accept / pin. Keep <1 screen.

### Status Dashboard
| TAG Family | Scope Accepted | Oracle Mode | Tests | Status |
|------------|----------------|-------------|-------|--------|
| D-PT (point-to-arc + string/compound Point) | Full leaf + lift | ARC_DISTANCE / SEGMENT | 20/20 + match | ✅ ACCEPTED |
| C-LIN (arc + CircularString weighted) | Full for String | ARC_CENTROID | 20/20 + semicircle/collinear match | ✅ ACCEPTED |
| D-AA (arc-to-arc) | Leaf `DistanceTo(CircularArc)` | ARC_ARC_DISTANCE | 4/4 new + broader clean | ✅ ACCEPTED (this run) |
| N-AA/N-AL | Intersections | ARC_ARC_XY / SEGMENT_XY | Green | ✅ ACCEPTED |
| OFF / ARC_OFFSET | — | Stub + tests.txt exists | — | ⏳ **Next** |

**Verification (run on every accept)**:  
`dotnet test ... --filter "Centroid|ArcCentroid|DistanceToPoint|DistanceToArc|Intersection"` (20+ pass) + direct oracle_bin probes + python/C# sim (exact hex/float match on known cases).

### Guiding Principles (enforced)
Low-risk analytical only → pinnable bit-exact RGR → reuse proofs (Distance.v, ArcIntersect, length, inCircle, offset gens) → SAFE_INT + BigDecimal → no noding until primitives green.

**Oracle reality** (checked today):  
Proofs has full distance/offset test gens + `arc_offset_tests.txt`. No `arc_centroid_tests.txt` (use direct probes — works). ARC_CENTROID exported for NTS but mode still needs full adversarial pin.

### Reusable RGR Pattern (copy for next)
Read (grep Linearize/Distance/Centroid patterns) → Red (failing analytical test + oracle value) → Green (minimal override + reuse enumerator/ComputeCenter/Intersection) → Refactor (tiny + comment + no new API) → Pin + Cake → Accept on 100 % match.

### Remaining Backlog (prioritised – one slice at a time)
**High (finish D-PT family)**
- 🔶 Full COMPOUND_ARC_DISTANCE (non-Point + curve-curve lifts) + exact BigDecimal ref + adversarial (NaN/huge/major) → 1 day
- 🔶 Expand ARC_AREA_CENTROID for holes/Compound/CurvePolygon (C-AREA full)

**Medium (next cheap)**
- ⏳ **ARC_OFFSET full** (signed + collapse → EMPTY or 3 pts) → unlocks BUF-1. Leverage proofs `arc_offset_tests.txt` + gen.  
  **Starter checklist**: (1) `ArcOffset` helper in CircularArc, (2) degenerate test, (3) pin mode, (4) Cake run.
- ARC_BUFFER_SIMPLE (single arc → CurvePolygon)

**Parked**
- Robust intersect, noding, full RELATE/DE9IM, buffer full, simplify, snap, filtered/uncertain/hot-pixel (after noding seam).

### SOP – How to Ship Next Slice
1. Pick → Read/grep.  
2. Red test.  
3. Green NTS (reuse D-AA/C-LIN pattern).  
4. Proofs mode extend + extract + RocqRefRunner.  
5. Pin + verify + update this file.

**Recommended next TAG (ship today)**: **ARC_OFFSET**  
Why: Lowest risk, highest leverage (proofs tests already exist), reuses D-PT/D-AA math, direct buffer entry, zero topology impact.  
Alternative: C-AREA full if you want composition first.

**Action items (this hour)**
- Pin remaining D-PT adversarial + full COMPOUND.
- Start ARC_OFFSET slice (or C-AREA).
- PR title: `feat(Curve): analytical ARC_OFFSET + collapse (RGR pinned to proofs offset tests)`.

References unchanged.  
**File updated** ✓ All acceptances logged, repetition eliminated, dashboard + reusable pattern added, next slice actionable with starter checklist, oracle leverage explicit.

Ready for ARC_OFFSET Red test code snippet or the `oracle_protocol.ml` diff? Just say “go” and we merge before EOD. 🚀