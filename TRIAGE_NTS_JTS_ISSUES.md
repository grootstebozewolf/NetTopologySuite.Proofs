# Triage — NTS / JTS open issues vs. NetTopologySuite.Proofs corpus

> **Source of record for the curve-awareness proof batch (#64–#69).** This is
> the report every batch issue cites. It maps the open NTS/JTS issues that the
> formal-proof corpus is meant to back onto **what is actually proven today**
> (`theories/`, `theories-flocq/`, `docs/verified-claims.md`), separating
> *proven* from *gap*, and recording priority and ordering decisions.
>
> Generated from the 2026-06-03 issue batch; last reconciled **2026-06-20**
> against the current working corpus (`origin/main` through PR #250 + PR #251
> pending — S15h–k line×line noding capstone + geometric `idet_abs_le_sq`).
> The prior reconciliation (2026-06-14,
> branch `claude/cycle-count-partition-yjgjmy`, PR #195 — the H_bridge Euler
> route + `ClassCount` convergence) predates the **arc-metrics / curve-relate /
> buffer-region / ring-validity oracle wave** (PRs ≈ #216–#246): the curve
> oracle suite is now broad — ARC_AREA / ARC_CENTROID / ARC_AREA_CENTROID /
> ARC_DISTANCE / ARC_ARC_XY / ARC_SEGMENT_XY / ARC_ARC_DISTANCE /
> ARC_SEGMENT_DISTANCE / ARC_OFFSET_XY / RING_SIMPLE / POINT_IN_CURVE_RING /
> RING_ORIENTATION / HOLES_DISJOINT / CURVE_RELATE_MATRIX / BUFFER_REGION /
> CP_BOUNDARY_SIMPLIFY — each backed by a named theory file with an honestly
> recorded deferred frontier (see `docs/oracle-handrolled-allowlist.txt`). This
> file is the cross-cutting overview; the per-area detail lives in the GitHub
> issues and the sibling docs `docs/issue-64-arc-primitives-triage.md` and
> `docs/issue-67-relateng-triage.md`.

## Scope

The corpus produces **Qed-closed Rocq theories + extractable oracles** that the
Java (JTS) and .NET (NTS) implementations can be *differentially verified*
against. These are **soundness statements**, not a verified re-implementation.
Regimes used below match `docs/verified-claims.md`: `[exact]` exact reals,
`[int-b64]` integer-coordinate binary64 (`|coord| ≤ 2²⁵`), `[int-b64-arc]` the
degree-4 `b64_inCircle` chain (`|coord| ≤ 2¹¹`), `[full-b64]` all finite
binary64, `[cond]` under named hypotheses, `[oracle]`
extracted/differential-testable.

The driving feature work is the **JTS Curve Awareness EPIC** (locationtech/jts#1195,
Option A structural `CurvePolygon`) and the NTS align epic (NTS#828). Umbrella
tracker: **#69**.

## Per-area status

| Issue | Area | Priority | Proof state | Verdict |
|---|---|---|---|---|
| **#64** | Circular-arc primitives (length, sweep, in-arc, in-circle) | `Immediate` | **Most progressed; metric + intersection suite now landed.** Asks #1/#2: `Atan2.v` + `AngleBetween.v` + `ArcLength.v` (`r·θ`, `chord_le_arc_length`) Qed. **Ask #4b PROVEN (PR #146):** `InCircle_b64_exact.v` — full-plane `b64_inCircle` sign exactness at **3 axioms, no `classic`** + `2¹¹` integer-regime value exactness + Perron witness. **Metrics landed since #195:** circular-segment area (`ArcArea.v`), arc + segment centroids (`ArcCentroid.v`, `ArcAreaCentroid.v`), point-to-arc / arc-arc / arc-segment distance (`ArcDistance.v`, `ArcPointDistance.v`, `ArcArcDistance.v`, `ArcSegmentDistance.v`), arc-arc & arc-segment intersection existence (`ArcArcCircles.v`, `ArcArcSound.v`, `ArcSegmentCircles.v`) — each with an oracle mode (ARC_AREA / ARC_CENTROID / ARC_AREA_CENTROID / ARC_DISTANCE / ARC_ARC_DISTANCE / ARC_SEGMENT_DISTANCE / ARC_ARC_XY / ARC_SEGMENT_XY), exact rational invariants proven, transcendental output as documented interface-boundary. **Ask #5a partial:** `ArcLineIntersect_b64_exact.v` Scope A (pre-division Cramer prefix bit-exact); coordinate **identity** (Scope B/C) + quartic arc-arc coordinates remain the deferred *exactness* frontier. `ArcOrient`/`ArcIntersect`/`ArcIntersectIVT`/`ArcHotPixel`/`ArcChordApprox`/`ArcOverlay` Qed. | Keep Immediate — metric/intersection oracles done; only Scope B/C + arc-arc coordinate identity remain |
| **#65** | Buffer / offset curve correctness | `Urgent` | Heaviest existing corpus: 18 `Buffer*.v` files + `ExtractBufferRings.v`, plus 3 documented counterexamples (depth enclosure / horizontal-edge / vertex-graze). **Curve-aware output now has an oracle certificate (since #195):** arc offset (`ArcOffset.v`, `ArcOffsetThreePoint.v` — `arc_offset_preserves_arc`), ring/curve offset assembly (`CurveRingOffset.v`, `CurveOffsetAssembly{,Total}.v`, `CurveRoundJoin.v`), and the buffer-region certificate (`CurveBufferArea.v` — boundary validity + signed-area algebra) drive oracle modes ARC_OFFSET_XY / BUFFER_REGION (+ ARC_BUFFER_SIMPLE/FULL pins). 3-axiom; the geometric "signed area = true Minkowski buffer area" is the deferred P2 frontier. | Keep Urgent — arc buffer/offset boundary+area certificate landed; Minkowski-area soundness deferred |
| **#66** | Precision / snap-rounding / OverlayNG soundness | `Urgent` | **Strongest coverage of the batch.** `SnapRounding_b64`, `HotPixel*`, `Hobby*`, the `PassesThrough_*` family (C1 grid-exactness reduction; plus a segment-reversal asymmetry negative that — correction 2026-06-17 — models a Liang-Barsky divide-from-c0 filter and does **NOT** map to JTS#752/#1133, since JTS's `HotPixel.intersectsScaled` canonicalizes to +X first), `Overlay*`, `RingArea979` (JTS#979). Multiple honest machine-checked **negatives** (rounded filter unsound/incomplete/asymmetric — cautions about that filter design, not JTS defects). | Keep Urgent — largely delivered, closing gaps |
| **#67** | RelateNG / 9IM matrix & boundary handling | `Immediate` | **DE-9IM suite through S15k in the working tree.** Per `docs/issue-67-relateng-triage.md` + `docs/verified-claims.md`: matrix algebra + witnesses (S0–S12), prepared-cache refinement (S13–S14b — `RelatePreparedCache*.v`, NTS#819 shape), and **line×line RelateNG noding** (S15a–k — `RelateNodingLineLine.v`: strata/regime bridges, per-pair test-10 fill, `matrix_dim_join` fold soundness, II/BB dimension pinning, collection relate-matrix capstone). Integer substrate: `RelateIntDetBound.v` now closes the geometric bound `idet_abs_le_sq` + `idet_fits_int64_for_cmax_coords` (0 axioms). Curve DE-9IM oracle `CURVE_RELATE_MATRIX` (`RelateCurveMatrix.v`) + `RELATE_MATRIX` / `RELATE_PREDICATE` drivers. **Remaining (S15l+):** prepared evaluate hook, exterior-row true-dimension pinning, Touches fill API split; global cell-**dimension** (Jordan/overlay) soundness; full multi-geometry pipeline beyond line×line. JTS#1175 fixed upstream (jts#1200). | Keep Immediate — line×line pipeline capstone landed; S15l+ + Jordan soundness remain |
| **#68** | Delaunay triangulation / Voronoi correctness | `Non-urgent` | `Triangle.v`, `Tin.v`, `GeneralTriangle{Parity,Separation}.v`, `RightTriangle*` exist; no empty-circle Delaunay / Voronoi proofs yet. **Core primitive now available:** `inCircle_R` / `b64_inCircle` proven via #146. | Correctly labeled — primitive unblocked, not yet started |
| **#69** | Umbrella / epic tracker | `Expectant` | Tracking issue only. | Keep open as the epic tracker |

## JTS #1195 TAG → proof-area mapping

The driving EPIC (locationtech/jts#1195) is structured as ~40 self-contained
**TAGs** across 7 phases ("one TAG per PR"). This maps the proof-relevant TAGs
onto the batch issues and the corpus artifacts that back them. Status:
**✅ proven** (Qed and/or extracted oracle) · **🟡 partial** (foundation/predicate
proven, soundness or coordinates open) · **⬜ planned** (not yet started) ·
**—** not proof-relevant (rendering / structural plumbing).

| JTS TAG | What it is | Proof issue | Corpus artifact / oracle | Status |
|---|---|---|---|---|
| **F-CP / F-MC / F-MS** | Structural `CurvePolygon` / `MultiCurve` / `MultiSurface` (preserve ring/member curves) | #69, #64 | `CurveGeometry.v` (SQL/MM types, `CurveRing`, validity, chord bridge); `CurvePolygon{Valid,Simple,Orientation,Disjoint,Offset}.v`; oracle-backed exterior ring (`oracle/curve_polygon.py`, `CP_BOUNDARY_SIMPLIFY`) | 🟡 structural model + validity/simplicity witness-sound; true-region (Jordan) deferred |
| **B-CP / B-MS** | Boundary of curve composites | #69, #65 | oracle `CP_BOUNDARY_SIMPLIFY` (densify → extracted `greedy_simplify_perp_b64` → per-corner `b64_orient_sign_filtered`); `CurveBufferArea.v` boundary | 🟡 densified-boundary oracle exists (INTSAFE corners certified by `_sound_small_int`); composite-boundary point-set spec deferred |
| **M-LEN-CS / M-LEN-CC** | Arc / compound-curve length (`r·θ`) | #64 | `ArcLength.v`, `Atan2.v`, `AngleBetween.v`; oracle `ARC_LENGTH_INVARIANTS_EXACT` / `ARC_SHORTER` | ✅ exact invariants; float length is interface-boundary |
| **M-AREA-CP** | `CurvePolygon` area (Green's theorem + circular-segment correction) | #64 | `ArcArea.v` (`segment_area`); oracle `ARC_AREA_INVARIANTS_EXACT` / `ARC_AREA` / `RING_ORIENTATION` (signed area) | ✅ exact rational invariants; float area interface-boundary |
| **M-DIM** | Dimension of curve geometries | #69 | — | ⬜ structural |
| **V-CP / V-CS** | Arc-aware validity (arc self-intersection, orientation via sector area, holes-in-shell) | #64 | `CurveRingSimple.v` (`curve_ring_not_simple_of_witness`), `CurvePolygonSimple.v`, `CurvePolygonValid.v`, `CurvePolygonOrientation.v`, `CurvePolygonDisjoint.v`, `InCircle_b64_exact.v`; oracle `RING_SIMPLE` / `POINT_IN_CURVE_RING` / `RING_ORIENTATION` / `HOLES_DISJOINT` | 🟡 in-circle sign ✅ (full-plane, 3-ax) + per-ring witness-soundness ✅; completeness + true-region (Jordan) deferred |
| **D-PT** | Analytical point-to-arc distance | #64 | `ArcDistance.v`, `ArcPointDistance.v`; oracle `ARC_DISTANCE` | 🟡 radial-foot core ✅; on-arc/sweep clamp deferred |
| **D-AA** | Arc-arc distance | #64 | `ArcArcDistance.v`, `ArcIntersect.v` (predicate); oracle `ARC_ARC_DISTANCE` | 🟡 disjoint circle-to-circle core ✅; sweep clamp deferred |
| **D-SL** | Arc-segment distance | #64 | `ArcSegmentDistance.v`; oracle `ARC_SEGMENT_DISTANCE` | 🟡 line-outside-circle core ✅; sweep/segment clamp deferred |
| **C-\*** | Centroid of curve geometries | #69, #64 | `ArcCentroid.v` (`arc_centroid_offset`), `ArcAreaCentroid.v`; oracle `ARC_CENTROID` / `ARC_AREA_CENTROID` | 🟡 offset spec proven (exact invariants); centroid POINT is interface-boundary (transcendental) |
| **H-\*** | Hulls over curve inputs | #69 | `Convex.v` (linear) | ⬜ curve case planned |
| **S-\*** | Simplification of curves | #69 | `Simplify.v` (greedy-perp structural), `Linearise.v`; oracle `CP_BOUNDARY_SIMPLIFY` (extracted simplifier ∘ densify, `oracle/curve_polygon.py`) | 🟡 oracle composes extracted `greedy_simplify_perp_b64` over a densified boundary; simplification-preserves-curve soundness open |
| **AT-\*** | Affine transforms (non-similarity → detect-and-densify, §7 risk) | #69 | — | ⬜ |
| **LRF-\*** | Linear referencing on curves | #69 | — | ⬜ |
| **DSF** | Densifier (curve → chords internally) | #64, #65 | `ArcChordApprox.v` (sagitta bound), `ArcChord{Density,Subdivision,Length,Sound}.v`, `CurveLinearise.v` (`chord_approx_ring_closed`); oracle `CP_BOUNDARY_SIMPLIFY` densify (`densify_arc`) | ✅ chord-approx faithfulness (closure); sagitta/`ring_simple` open |
| **BUF-1 / BUF-N** | Single-/multi-arc buffer → `CurvePolygon` | #65 | 18× `Buffer*.v` (linear), `ExtractBufferRings.v`; `CurveBufferArea.v`, `CurveRingOffset.v`, `CurveOffsetAssembly{,Total}.v`, `CurveRoundJoin.v`; oracle `BUFFER_REGION` (+ `ARC_BUFFER_SIMPLE/FULL` pins) | 🟡 arc buffer-region boundary+area certificate ✅ (3-ax); Minkowski-area soundness deferred |
| **OFF** | Offset curve (arc-preserving) | #65 | `BufferOffset.v`, `ArcOffset.v`, `ArcOffsetThreePoint.v` (`arc_offset_preserves_arc`), `CurvePolygonOffset.v`, `CurveRingOffset.v`; oracle `ARC_OFFSET_XY` | 🟡 arc offset ✅ (valid arc → valid arc, radius r+d); assembly conditional |
| **VBF** | Variable-distance buffer | #65 | — | ⬜ |
| **N-AL** | Arc-line noding / intersection | #64 | `theories-flocq/ArcLineIntersect_b64_exact.v` (Scope A), `ArcSegmentCircles.v` (`line_circle_radical_point`), `ArcIntersect.v`, `ArcIntersectIVT.v`; oracle `ARC_SEGMENT_XY` / `ARC_LINE_XY` | 🟡 Scope A (pre-division) ✅ + existence ✅; coordinate identity (Scope B/C) queued |
| **N-AA** | Arc-arc noding / intersection | #64 | `ArcArcCircles.v`, `ArcArcSound.v`, `ArcIntersect.v` (`arc_arc_intersects` predicate); oracle `ARC_ARC_XY` | 🟡 circles-intersect (Stage B) ✅; quartic coordinates open |
| **N-SS** | `SegmentString` / `Noder` for curves | #66 | `SnapRounding_b64.v`, `HotPixel*`; oracle `CURVE_SNAP_DECISION` | 🟡 linear noding ✅; curve-snap decision oracle ✅ |
| **PRC-SN** | `PrecisionModel.makePrecise` on curves | #66 | oracle `CURVE_SNAP_DECISION` / `CURVE_SNAP_INVARIANTS_EXACT` (exact-`Q`) | ✅ curve-snap grid-friendliness |
| **OV** | Arc-preserving overlay output | #66, #64 | `Overlay*.v`, `OverlayCorrectness.v`, `ArcOverlay.v` | 🟡 conditional headline (`arc_overlay_correct_chord_approx`, 2 bridge hyps) |
| **R-\* (R-CONT, R-PR)** | Predicates / relate on curved inputs | #67 | `DE9IM.v`, `RelateLineLine.v`, `RelateAreaPoint.v`, `RelateBoundary.v`, `RelateAreaLine.v`, `RelateAreaArea.v`, `RelateArcChord.v`, `RelateArcAnalytic.v`, `RelateClothoid.v`, `RelateEllipticArc.v`, `RelateBezier3.v`, `RelateCurveAreaPoint.v`, `RelateMatrix*.v`, `RelateCurveMatrix.v`, `RelatePreparedCache*.v`, `RelateNodingLineLine.v`; oracle `CURVE_RELATE_MATRIX` / `RELATE_MATRIX` / `RELATE_PREDICATE` | 🟡 matrix algebra + witnesses ✅ (S0–S12); prepared-cache refinement ✅ (S13–S14b); **line×line noding pipeline partial** ✅ through S15k (collection capstone); cell-**dimension** (Jordan/overlay) + S15l+ hooks deferred |
| **PLG** | Polygonizer accepting `CompoundCurve` edges | #69, #66 | `RingExtract.v` / overlay ring assembly; `PermCycleSplice.v`, `NumFacesSplice.v`, `EulerBridge.v` | 🟢 linear `extract_rings_valid` is a conditional-Qed; its former named seam `EdgeFaceBridge.H_bridge_core` (planar same-face ⇒ bridge) is now fully DISCHARGED — carried as the named premise `H_bridge_premise`, proved in `HBridgeEuler.v` from the named planar Euler identity + face split `num_faces_E_minus_splice`. This PLG/ring-assembly deferral is itself discharged; the deferred-proof registry is **not** empty, however — it currently holds **3** unrelated `ArcPointDistance.v` sweep-clamp residuals (`check_admitted.sh`: 9 = 6 counterexample + 3 deferred; see finding 7); `extract_rings_valid` carries the planar Euler hypotheses |
| **TRI-DT** | Delaunay on (densified) curved boundaries | #68 | `theories-flocq/InCircle_b64_exact.v` (primitive), `Triangle.v`, `Tin.v` | 🟡 in-circle primitive ✅; Delaunay proper planned |
| **TRI-VR** | Voronoi on curved input | #68 | — | ⬜ |
| **TB-\* / F-RD** | TestBuilder rendering / `ShapeWriter` hooks | — | — | — not proof-relevant |

**Reading the table against the EPIC's Definition of Done (§10).** JTS#1195's
DoD requires curve-preserving output "**where mathematically sound**" — which is
exactly what the ✅ rows certify and the 🟡 rows bound. The §7 "arc intersection
performance" risk concerns the N-AA/N-AL primitives whose *exactness* is already
proven here (`InCircle_b64_exact` / `ArcLineIntersect_b64_exact`): the corpus
supplies the soundness oracle while JTS settles the performance design.

## Referenced upstream issues

Status of the JTS/NTS issues the batch cites as drivers. Re-check before
spending further proof effort — several are stale.

| Upstream | Cited in | Status |
|---|---|---|
| JTS#1195 — Curve Awareness EPIC | #64, #65, #66, #68, #69 | Open — primary driver |
| JTS#1175 — RelateNG.computeLineEnds() skips boundary points | #64, #66, #67 | **Fixed (jts#1200)** — struck through in #64/#66/#67 |
| JTS#979 — buffer with fixed precision removes hole | #64, #65, #66 | Open — backed by `RingArea979.v` |
| JTS#752 — TopologyException in UnaryUnionNG (floating precision) | #66 | Open — **NOT explained by the asymmetry lane** (correction 2026-06-17): JTS's `HotPixel.intersectsScaled` canonicalizes to +X before testing, so it is reversal-symmetric by construction; `PassesThrough_b64_compute_asymmetric.v` models a Liang-Barsky divide-from-c0 filter JTS does not use. Root unidentified here. |
| JTS#1133 — snapRoundingNoder on polygons returns MultiLineString | #66 | Open — **same correction**: asymmetry lane does not map to this defect (JTS canonicalizes endpoints); root unidentified here |
| JTS#1106 — orientation robustness summary | #64, #66 | Open — `Orient_b64_exact*` is the ground-truth spec |
| JTS#1147, #739, #1028, #178, #180, #592, #866, #876, #908, #1102, #1183 — buffer/offset quality | #64, #65 | Open — "summary of failures" refs need re-check vs current JTS |
| JTS#1000 — OverlayNG failures summary | #64, #66, #67 | Open |
| JTS#865 — OverlayNG intersection rotates vertices | #64, #66 | Open |
| JTS#1122 — CoverageValidator misses gap if tolerance too large | #64, #66, #67 | Open |
| JTS#1190, #1138, #1039, #20 — Delaunay/Voronoi robustness | #68 | Open |
| NTS#828 — align epic | #69 | Open |
| NTS#815 — OffsetCurve miter for polygonal (JTS#1109) | #64, #65, #69 | Open — port target |
| NTS#819 — RelateNG cache for prepared A-L (JTS#1099) | #67 | Open (perf); **proof companion partial (S13–S14b)** — `RelatePreparedCache*.v` |
| NTS#247, #570 — curves / GML curves | #64, #69 | Open — old but relevant |
| NTS#719, #638 — GeometryPrecisionReducer / buffer holes | #66 | Open |

## Cross-cutting findings

1. **This file exists and is the source of record.** Cited by every batch issue;
   created 2026-06-08, refreshed 2026-06-09. Per-area detail now lives in the
   sibling docs `docs/issue-64-arc-primitives-triage.md` and
   `docs/issue-67-relateng-triage.md` (the umbrella/detail split #69 describes).
2. **Stale upstream refs.** JTS#1175 is fixed (jts#1200) and is struck through
   with the PR ref in #64, #66, #67. The buffer/overlay "summary of failures"
   refs (JTS#1102, #1000, etc.) should still be re-checked against current JTS
   before more proof spend. *Internal doc-drift:* the PLG/ring-assembly deferred
   proof was discharged 2026-06-14 (see finding 5), but the deferred-proof
   registry is **not** empty today — it holds **3** `ArcPointDistance.v`
   sweep-clamp residuals registered since (`check_admitted.sh`: 9 total = 6
   counterexample + 3 deferred-proof). Any "EMPTY (0)" wording below is the <!-- registry-sync:ok -->
   2026-06-14 state, superseded — see finding 7.
3. **Label vs. reality reconciled (2026-06-08).** #67 bumped `Urgent → Immediate`
   (was the under-built area); #65 trimmed `Immediate → Urgent` (linear buffer
   foundation mature, curve output blocked on #64).
4. **Progress since 2026-06-08 (2026-06-09).** PR #146 merged: #64 ask #4b
   (`b64_inCircle` sign exactness) closed at 3 axioms full-plane, arc-line
   Scope A landed. #67 moved from blank to S0–S3 (`DE9IM.v`, `RelateLineLine.v`,
   `RelateIntDetBound.v` + oracle vectors) — since extended through S15k; see
   finding 6. #68's `inCircle` primitive is now available. The first two items of
   the prior order of attack are done/started.
5. **Progress since 2026-06-09 (2026-06-14) — the PLG / ring-assembly lineage.**
   `extract_rings_valid` is a conditional Qed and the deferred-proof registry
   was EMPTY at that date (1 → 0) — *current state is 3, see finding 7*. The
   planar same-face ⇒ bridge seam (formerly the `Admitted`
   `EdgeFaceBridge.H_bridge_core`) is now carried as the named premise
   `H_bridge_premise`, threaded through the EdgeFaceBridge chain (all `Qed`
   parametrically over it) and DISCHARGED downstream in `theories/HBridgeEuler.v`
   (`H_bridge_premise_from_euler`) from the named planar Euler identity. PR #195
   (merged to `main`) corrected the precondition to `noded_general_position E` and
   built the planar-Euler discharge infrastructure (`ReachableDec`/`num_components`,
   `EulerArrangement`/`euler_characteristic` carried as a NAMED `V−E+F = 2C`
   hypothesis — not an axiom — and the `EulerBridge` wiring), alongside the
   `ClassCount` convergence of the orbit/component counters. The generic cycle-count
   SPLICE (`PermCycleSplice.cycle_count_surgery`) and its instantiation
   (`NumFacesSplice.num_faces_E_minus_splice`) PROVE the combinatorial core — the
   same-face FACE SPLIT `num_faces (E_minus E d) = num_faces E + 1`. The only
   residual is the named planar Euler identity itself, now a hypothesis on the
   headline `extract_rings_valid` (carried by design, never axiomatized).
6. **Progress since 2026-06-14 (2026-06-20) — the arc-metrics / curve-relate /
   buffer-region / ring-validity oracle wave.** A broad curve oracle suite
   landed (PRs ≈ #216–#246): arc **metrics** (`ArcArea.v`, `ArcCentroid.v`,
   `ArcAreaCentroid.v` + ARC_AREA / ARC_CENTROID / ARC_AREA_CENTROID), arc
   **distance** (`ArcDistance.v`, `ArcArcDistance.v`, `ArcSegmentDistance.v` +
   ARC_DISTANCE / ARC_ARC_DISTANCE / ARC_SEGMENT_DISTANCE), arc-arc / arc-segment
   **intersection** existence (`ArcArcCircles.v`, `ArcArcSound.v`,
   `ArcSegmentCircles.v` + ARC_ARC_XY / ARC_SEGMENT_XY), arc **offset / buffer**
   (`ArcOffsetThreePoint.v`, `CurveRingOffset.v`, `CurveOffsetAssembly{,Total}.v`,
   `CurveRoundJoin.v`, `CurveBufferArea.v` + ARC_OFFSET_XY / BUFFER_REGION), curve
   **validity** (`CurveRingSimple.v`, `CurvePolygon{Simple,Valid,Orientation,Disjoint}.v`
   + RING_SIMPLE / POINT_IN_CURVE_RING / RING_ORIENTATION / HOLES_DISJOINT), the
   full **DE-9IM** suite (#67 S0–S12 + CURVE_RELATE_MATRIX), curve
   **simplification** (`CP_BOUNDARY_SIMPLIFY` + `oracle/curve_polygon.py`,
   surfaces wishlist #1), and the **RelateNG noding spine** (#67 S13–S15k:
   prepared-cache refinement `RelatePreparedCache*.v`, line×line strata through
   collection relate-matrix capstone `RelateNodingLineLine.v`, geometric
   `idet_abs_le_sq` in `RelateIntDetBound.v`). Pattern across all: exact
   rational invariants / witness soundness Qed-closed; the transcendental output
   coordinate and the true-region (Jordan / Minkowski / cell-dimension) soundness
   are the recorded deferred frontiers. The hand-roll ratchet is at 19 frozen
   interface-boundary kernels (`docs/oracle-handrolled-allowlist.txt`).
7. **Reconcile 2026-06-20 (later) + deferred-registry correction.** Since the
   arc wave, `origin/main` took the **#67 prepared-cache spine** (S13 PR #248,
   S14/S14b PR #249 — `RelatePreparedCache*.v`, the NTS#819 refinement) and the
   **`Distance.v` metric foundations** (PR #252: `dist_triangle` +
   `dist_lt_iff_dist_sq_lt` + `cauchy_schwarz_2d`, making `(Point, dist)` a
   proven metric space). The **line×line noding capstone** S15h–k +
   `idet_abs_le_sq` is in review (PR #251, this branch). Tooling: the in-repo
   **Observatory dashboard** + the Rocq-provisioning **SessionStart hook**
   landed (PR #250). **Registry correction:** earlier findings' "deferred-proof
   registry EMPTY (0)" is **stale** <!-- registry-sync:ok --> — `scripts/check_admitted.sh` reports **9
   total = 6 counterexample + 3 deferred-proof**. The 3 deferred entries are all
   `ArcPointDistance.v` sweep-clamp residuals (`point_to_arc_dist_radial_lower`,
   `point_to_arc_dist_fallback_ends_lower`, `point_to_arc_dist_centre_is_r`),
   the on-arc/sweep-clamp frontier of #64's D-PT distance row — not the PLG seam,
   which is genuinely discharged.

## Recommended order of attack (revised 2026-06-20)

1. **#67** — still the deepest *unfinished* build, but now well advanced: matrix
   algebra + witnesses (S0–S12), curve DE-9IM oracle (CURVE_RELATE_MATRIX),
   prepared-cache refinement (S13–S14b), and **line×line RelateNG noding through
   S15k** (`RelateNodingLineLine.v` collection capstone). Remaining: **S15l+**
   (prepared evaluate hook, exterior-row pinning, Touches fill split), global
   cell-**dimension** (Jordan/overlay) soundness, and multi-geometry pipeline
   beyond line×line.
2. **#64** — finish ask #5a Scope B/C (arc-line coordinate **identity** + forward
   error) and the quartic arc-arc coordinates; the sign/length/area/distance and
   intersection-**existence** foundation is now done.
3. **#65** — close the geometric "signed area = true Minkowski buffer area" gap
   above the landed BUFFER_REGION certificate.
4. **#66** — finish remaining precision/overlay gaps (mostly there).
5. **#68** — Delaunay / Voronoi on top of the now-proven `inCircle_R`.

## How to cite the corpus

When referencing proven results: lead with `[exact]` rows from
`docs/verified-claims.md`, present `[cond]` rows as "conditional headline"
(never as solved), and offer the matching `[oracle]` mode to reproduce a
concrete case. Qed-closure is enforced corpus-wide by
`scripts/check_admitted.sh`; claim citations are checked by
`scripts/validate-claims.sh` on every CI run.
