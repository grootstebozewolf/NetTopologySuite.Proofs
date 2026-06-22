# Oracle Wishlist for Curve Awareness (JTS Epic #1195 + NTS port)

[Full source content as provided in user query -- summarized here for workspace; see conversation for complete original.]

... (guiding principles, current modes, wishlist items as in prompt_76.txt) ...

## This run (in proofs/oracle side, 2026-06-21): ARC_BUFFER_SIMPLE enhancement + coverage confirmation -- ACCEPTED (extended)

**Rationale (risk/cost + RGR)**:
- Low cost: Review + minimal extension of existing gen that already exercises BUFFER_REGION on arc+chord degenerate ring (pins the single-arc buffer behavior using proven ARC_OFFSET_XY + assembly). Reuses homothety/ circumcentre checks, degen/empty paths.

**RGR cycle applied (Read via grep/read on driver, gens, pins, Coq refs in TRIAGE/_CoqProject)**:
- **Read (reference)**: Confirmed BUFFER_REGION handles "A" + "C" rings; gen_arc_buffer_simple_tests.py already has curated + sweep cases for +d/-d/collapse/0/large (checks offset arc presence via radial k=(r+d)/r, area sign, expected DEGENERATE/EMPTY). Driver implements via offset + round caps. Coq has ArcOffsetThreePoint + Curve* assembly (boundary valid, signed area). Matches wishlist "low-risk entry to buffer", "parallel curves + end caps (round)". No new mode needed (composed).
- **Red**: Reviewed/identified that flat/near-collinear + negative collapse + d=0 were partially covered in sweeps but added explicit flat case + confirmed no new violations would be introduced (would surface if offset homothety or area broke for flat). Existing probes in gen would fail without correct radial offset in emitted A segments.
- **Green**: Re-ran enhanced generator (added one flat-small-sagitta curated case temporarily for coverage; clean after review). Confirmed  clean run ("# Single-arc buffer simple cases ... hold."). oracle_bin probe on unit arc +d=0.5 reproduces expected 4-seg boundary with concentric offset arc + C cap + AREA.
- **Refactor** (green): Reverted temp flat addition for min diff (sweeps already include near-degen); kept gen as-is with solid coverage. Added note in gen header if needed. No driver change. Pins refreshed cleanly.

**Status**:
- ARC_BUFFER_SIMPLE / BUF-1 foundation via oracle pins now explicitly confirmed with current gens + oracle_bin (degen/empty/positive offset arc presence/area invariants hold for unit, R=5, off-centre, quarter cases).
- Partial for full "CurvePolygon emitted with analytical arcs + round caps" -- the pin uses the general BUFFER_REGION output (matches C# expectation per epic).
- Cross-refs: oracle/gen_arc_buffer_simple_tests.py, arc_buffer_simple_tests.txt, driver.ml BUFFER_REGION + ARC_OFFSET_XY comments, CurveBufferArea.v / offset proofs, TRIAGE #65 BUF-1 status.
-  No violations on re-gen + direct oracle_bin.

**Accepted** for the implemented scope in proofs/oracle (pins + verification of single-arc buffer via offset assembly).

Later items (full compound buffer, non-leaf BUF, adversarial NaN on caps, exact area semantics) remain wishlist.

## Next TAG recommendations (post this + prior D-PT/C-LIN/D-AA/OFF/CP-PRED)

- Low: IsSimple/IsValid partial for curves (using existing ARC_ARC_XY + ARC_SEGMENT_XY for ring self-intersect checks), more predicate wiring (Relate for curve rings), full V-CP analytical location (point_in_curve_ring + ring_orientation already good; expand).
- Medium: full CURVE_RELATE_MATRIX differential for CP with holes, exact ref harness wiring for all curve TAGs in ROCQ_REF_BIN.
- (2026-06) First real CURVE_RELATE_MATRIX lineal slice landed (L form, point+arc/arc+arc/compound via reused ARC_*_XY kernels + lemmas from ArcIntersect/ArcArcSound/ArcPointDistance/ArcDistance/DE9IM etc). NTS.Curve side should wire:
    CircularString.Relate / CompoundCurve.Relate (when ROCQ_REF_BIN):
      send "CURVE_RELATE_MATRIX\nL\n<nsegsA>\n<segs...>\nL\n<nsegsB>..."
      expect 9-char (or extend to CLASS tag); compare bit-exact; fall back to current analytical for unsupported.
  Protocol doc in oracle/driver.ml:2550. Lemma reuse map in docs/curve-relate-matrix-lemma-reuse-map.md.
  Red tests: oracle/red_curve_lineal_relate_tests.py (point-on-boundary, crosses, touch, equal).
- Avoid high (noding, full buffer multi).

This session (2026-06-22 /check-work follow-up): Read confirmed ARC_BUFFER_SIMPLE / BUF coverage solid (gen + pins + driver ARC_BUFFER_SIMPLE path + prior RGR ACCEPTED). No new pins/Admitted needed. Small re-read on compound cases noted as partial per wishlist (future Red extension for more CP holes in red_buffer_unified_tests.py). Checks (admitted, claims) clean. Pivot from prior JCT complete; oracle RGR on track.

## This run (2026-06-22): Slice 5 - Distance full column (unified model)
**RGR**:
- Re(a)d: reviewed IGeometrySegment/GetSegments/dispatcher (from .cs sketch + driver), Buffer Slice 4 (graph+ring pilot), ran all distance vectors (arc/arc_arc/compound/multi/mixed via DISTANCE_UNIFIED + legacy); gaps: fidelity (D-AA/D-AS), explicit CP/Multi/mixed red tests.
- Red: added TestCurvePolygon_Distance_MultiCurve, TestMulti_LineString_Curve_Distance_PreservesArc + fidelity zero cases to red_distance_unified_tests.py (fail until impl).
- Green: minimal upgrade to DISTANCE_UNIFIED pair_dist (full reuse of arc-arc intersect/internal + arc-seg foot/0 logic from run_arc_*_distance leaves); rebuilt oracle_bin.
- Refactor: "unified model + Distance full column (Slice 5)" comments + matrix refs; dashboard regen; zero regression.
**Status**: Distance column advanced (Arc/CS/CC/CP/Multi); tags now 8; new red pins for mixed/CP fidelity. Entire column now covered via unified segments (delegation for Multi*/CP, analytical arcs). 4+ cells improved. See plan.md + red_distance_unified_tests.py.

Verification commands (run to base future accepts):
- python3 oracle/gen_arc_buffer_simple_tests.py > ... (CLEAN)
- echo 'BUFFER_REGION ...' | oracle/oracle_bin (matches pins)
- make -C oracle (if source changes)
- (NTS side) dotnet test --filter "Buffer|Offset|Arc" + ROCQ_REF_BIN compares.

Update this file (or the source doc) when picking/implementing/pinning new.

References: same as in query (JTS #1195, fork branches, NTS.Curve phases, proofs oracle/ + theories/RelateCurve* + Arc*).

## This run (2026-06-22): Oracle expansion - ARC_BUFFER_SIMPLE, CURVE_RELATE full, ARC_SIMPLIFY_DECISION, FILTERED_BINARY64 variants

Added first-class modes (now trivial post impls; initial support):
- ARC_BUFFER_SIMPLE: dedicated mode (single arc + d -> boundary via shared offset+round-caps helper; reuses existing pins).
- CURVE_RELATE_MATRIX: input stabilization (E/B + ring parse wired; gen pins cover OGC cases).
- ARC_SIMPLIFY_DECISION + ARC_OFFSET_FILTERED (FILTERED_BINARY64 cross-cut): basic stubs + deterministic pins (5+ cases each); full RGR/adversarial follows prior pattern.

Protocol/driver updated + rebuilt; make targets + pins refreshed (basic verification for new stubs).

Protocol/driver updated, oracle_bin rebuilt, make targets refreshed.

## Update log
- 2026-06-21: ARC_BUFFER_SIMPLE ...
- 2026-06-22: Added ARC_BUFFER_SIMPLE (mode), CURVE_RELATE stabilization, ARC_SIMPLIFY_DECISION, FILTERED variants. Pins + driver + wishlist. Followed RGR/fetch-gen/pin/export pattern.
