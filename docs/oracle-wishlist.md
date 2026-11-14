<!-- doc-kind: guide -->
**Oracle Wishlist v7.0** (15 Aug 2026, Amsterdam)

**Milestone**: JTS two-disc overlay is exact; oracle mode **`DISC_OVERLAY`** is the Rocq twin (this accept).

**TAGs shipped**: D-PT, C-LIN, D-AA, OFF, C-AREA, composites, D-CURVE, BUF-S, N-SS, R-CURVE (10+ vertical slices, all green with oracle matches).
**Product accept**: **OV-DISC** (JTS) — two-disc CAP·CUP·SUB·XOR exact on JTS PR #8 `4bc8195d`.
**Oracle accept**: **`DISC_OVERLAY`** — protocol keyword → `theories/DiscOverlay.v` → RocqRefRunner mode → `oracle/gen_disc_overlay_tests.py`. Locked nodes `(3.5, ±√12.75)`.

Phase-0 (`feat/overlayng-phase0-red`) already proved crossing cells never collapse algebraically to A/B/A∪B/∅. `DISC_OVERLAY` is the per-shape closed form for the disc-disc crossing cell, not a shortcut around that theorem.

**Guiding Principles** (still enforced): Low-risk analytical first → pinnable RGR → reuse proofs math → SAFE_INT + BigDecimal → defer full overlay. Name gate: **OverlayNGCurve**, never OverlayNGCurved (NTSC0001).

### Accepted TAGs (compact)
- **Distance** (D-PT/D-CURVE/D-AA): Full leaf + CS/CC lifts ✅
- **Centroid/Area** (C-LIN/C-AREA + composites): Enclosed + Polygon/Compound ✅
- **Offset/Buffer** (OFF + BUF-S): Leaf + single-arc CurvePolygon ✅
- **Intersections/Noding** (N-AA/N-AL + N-SS basic split): Sub-arc exact ✅
- **Relate/Predicates** (R-CURVE): Intersects/Contains/Relate wiring ✅
- **OV-DISC** (JTS product, 15 Aug 2026): two-disc CAP·CUP·SUB·XOR exact on JTS PR #8 `4bc8195d`. https://github.com/grootstebozewolf/jts/pull/8
- **DISC_OVERLAY** (oracle, this accept): two-disc CAP/CUP/SUB/XOR as lens/blob/crescent/crescents. Lemma `theories/DiscOverlay.v` (`radical_nodes_in_lens`, `locked_disc_nodes`, Qed, 3-axiom, no new axioms). Driver `DISC_OVERLAY` reuses the `ARC_ARC_XY` radical-axis (not a second kernel). Input: two discs (centre+radius or 5-point CIRCULARSTRING) + op in {CAP,CUP,SUB,XOR}. Output: config, kind, nodes, closed-form area. Locked pin: centres `(0,0)`/`(7,0)` r=5 → nodes `(3.5, ±√12.75)`. Generator `oracle/gen_disc_overlay_tests.py` (I1–I7).
- **LEC_CIRCLE** (oracle, 15 Aug 2026): the LargestEmptyCircle closed form on a circle obstacle — the LEC laser the chord-path hypothesis said didn't exist. Lemma `theories/LECChordGap.v` (`lec_chord_hypothesis_refuted`: exact LEC of the radius-r circle over its disk = (centre, r); the chord path answers r·cos(π/n), Qed-pinned at n=4/r=2 → √2). Driver `LEC_CIRCLE`: input a circle (centre+radius or 5-point CIRCULARSTRING via `circumcentre_q`) + chord count n; output the exact closed form (bit-exact echo) + the chord-path prediction r·cos(π/n) for the perf gate to check its densify-then-LEC against. Generator `oracle/gen_lec_circle_tests.py` (I1–I5: echo, locked √2 pin, underestimate + monotone convergence, CS==direct, verdicts).
- **LEC-TYPED** (JTS product, 15 Aug 2026): typed `ObstacleDistance` (package-private next to LEC) on JTS PR #8 `5fe25422` — uncertified LEC keeps the branch-and-bound grid, but clearance is now the typed per-component metric: Point/MultiPoint euclid, LineString facets, CircularString point-to-arc per 3-control window, CompoundCurve min over members, filled disc max(0, |p−c| − r), full-circle ring ||p−c| − r|, collections flattened by min. Gate slack stays 15%; identity + ratio rows green (jts-core 2335 / jts-curve 478 / jts-app 211).
- **OBSTACLE_DISTANCE** (oracle, 15 Aug 2026): the Rocq twin of LEC-TYPED's closed-form rows. Lemma `theories/LECObstacleDistance.v` (`obstacle_distance_headline`: filled-disc max(0, |P−c| − r) and full-circle-ring ||P−c| − r| are the EXACT set distances — reverse-triangle lower bound AND radial-projection attainment — so emptiness against the infinite obstacle collapses to ONE comparison; unions flatten by min; clamping commutes with min = the Apollonius reduction `min_disc_dist_weighted`). Driver `OBSTACLE_DISTANCE`: input a query point + k typed components (`POINT x y` | `DISC x y r` | `RING x y r`); output the min clearance (hex float). Generator `oracle/gen_obstacle_distance_tests.py` (I1–I6: 3-4-5 witness pins — clearance 2 at (0,±3), 1 at the rect centre, 0 at the corners —, clamped-weighted-min mirror, disc-vs-ring, flatten/permutation, witness-grid bound + maximisers, verdicts). Failed-path ledger: `docs/lec-optimal-path.md` (corner-sampling and interior-maximiser hypotheses REFUTED). Arc rows (point-to-arc, CompoundCurve) stay next rungs.

All with tests (4/4–20/20), code refs, oracle matches, and minimal changes.

JTS R1.5 (`CircularDiscOverlay`, hooked in `OverlayNGCurve` after R1 / before R2): both operands circular discs (`CurveExact.circularDisc`) and `CircularArcDensifier.intersectCircles` returns two proper nodes. CAP = lens, CUP = two-arc blob, SUB = crescent, XOR = both crescents, as `CurvePolygon` of two `CircularString`s (`isApproximate = false`). Locked pair `CIRCLE_5` ∩ `CIRCLE_CROSSING`, centres (0,0) and (7,0), r=5, nodes `(3.5, ±√12.75)`. Crossing ratchet `aaaa` → `EEEE`; Crossing CAP 0.017 vs 0.681 ms (ratio 0.025); slack still 15%.

### Current Oracle Modes
✅ ARC_DISTANCE family, ARC_ARC_DISTANCE, ARC_CENTROID, ARC_AREA_CENTROID, ARC_OFFSET_XY, ARC_BUFFER_SIMPLE, N-AA/N-AL (`ARC_ARC_XY` / `run_arc_arc_xy`, `ARC_SEGMENT_XY`), relate_matrix partial, V-CP, PRC-SN + recent buffer/ring/area gens.
✅ **`DISC_OVERLAY`** — two full discs + {CAP,CUP,SUB,XOR} → lens/blob/crescent/crescents (nodes + closed-form area). Reuses `ARC_ARC_XY` / N-AA radical-axis + circumcentre_q.

`OVERLAY_UNIFIED` is contact DE-9IM only (`212FF1FF2` / `FFFFFFFFF`), not overlay geometry. This repo already has the intersection kernels JTS R1.5 reused (`ARC_ARC_XY` / N-AA, same radical-axis formula; `ARC_SEGMENT_XY` / N-AL).

### Remaining Roadmap (smart prioritisation)
| Priority | Item | Notes |
|----------|------|--------|
| High | Adversarial + BigDecimal/ROCQ_REF_BIN harness | 1 day. Across all accepted modes. Close RGR gaps. |
| High | **ARC_BUFFER_FULL** (multi-arc, negative, self-intersect) | 3 days. Use BUF-S + N-SS. |
| High | General circular noding + arrangement | Unparked. Split arcs at N-AA/N-AL nodes, face labels, then general CAP·CUP·SUB·XOR. JTS next laser after two-disc (disc vs polygon, CompoundCurve shells, lineal arc vs line, on-arc-vertex TopologyException). **Rung 1 landed**: `theories/ArcSplitAtNode.v` — split-at-node partition on the DISC_OVERLAY locked fixture (cover / disjoint / seam, chord-sign form, 3-axiom). Next rungs: general configuration, child mids, N-AL twin, faces. |
| Medium | ARC_SIMPLIFY + ARC_SNAP | 2 days. Post-noding. |
| Medium | Full CURVE_RELATE/DE9IM (holes, Multi, mixed) | 3 days. Extend matrix. |
| Parked | Shewchuk port | After seams stable. |

**Recommended next**: general circular noding (line–circle / multi-arc arrangement) or **ARC_BUFFER_FULL**. Do not implement those in the DISC_OVERLAY slice.

### Reusable Templates
**RGR Pattern** (used for every slice): Read (grep fallback) → Red (analytical test) → Green (minimal reuse) → Refactor (tiny + comment) → Pin + Cake + oracle match → Accept.

**Oracle Add SOP**: Protocol keyword → OCaml/Coq + lemma → Extract → RocqRefRunner → Generator → NTS harness → Cake → bump this file.

**Verification command** (standard): `make -C oracle disc-overlay-tests` + `dotnet test ... --filter "Distance|Offset|Centroid|Area|Buffer|Intersects|Relate|Split"` + oracle probes.

### How to Keep This File Smart
- New accept → add 1 row to Accepted table + bump version/date + one-line note.
- New wishlist item → add to Remaining table only.
- No full RGR stories here (keep in PRs/commits for audit).

References unchanged.

This is the official maintainable plan.
