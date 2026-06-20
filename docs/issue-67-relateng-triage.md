# Issue #67 — RelateNG / DE-9IM predicates: research & gap triage

> **Status:** living triage — S0–**S15b** **complete in the working tree**
> (2026-06-20); **S15c+** (share / OGC exterior / collections) remains open.
> Refresh when a new session closes.
>
> Corpus at time of writing: `main` (through S12 + curve→matrix transport stack);
> S13–S14 add `RelatePreparedCache.v` and `RelatePreparedCacheAreaLine.v`
> (PR #248, pending merge). Seven fill APIs through `RelateMatrixCurveAreaPoint.v`;
> oracle `RELATE_MATRIX` / `RELATE_PREDICATE` modes landed (S11).

## 1. What #67 asks for

Issue #67 ("Immediate") requests mechanically-verified proofs for **RelateNG**
and **prepared-geometry** spatial predicates — the DE-9IM intersection matrix
and the standard relate family (Contains, Intersects, Touches, Disjoint, …).

Concrete goals from the issue body:

1. **DE-9IM matrix computation** — dimensionally-extended 3×3 intersection
   matrix between two geometries (Interior / Boundary / Exterior of A vs B).
2. **Standard predicate semantics** — Contains, Covers, Crosses, Disjoint,
   Equals, Intersects, Overlaps, Touches, Within (and custom matrix patterns).
3. **Boundary handling** — correct treatment of boundary points, endpoint
   touches, and `BoundaryNodeRule` (default MOD2).
4. **Prepared mode** — `RelateNG.prepare(A)` caches spatial indexes; repeated
   `evaluate(B)` must agree with one-shot `relate(A,B)`.
5. **Oracle / differential testing** — extracted or bit-exact reference modes
   for NTS/JTS predicate ports (R-CONT, R-PR, V-CP curve validity, etc.).

**Key external references (triaged):**

| Ref | Status | Relevance |
|-----|--------|-----------|
| [JTS#1175](https://github.com/locationtech/jts/issues/1175) — `computeLineEnds()` skips boundary points on disjoint line components | **Fixed** ([JTS#1200](https://github.com/locationtech/jts/pull/1200)) | Boundary/line-end regression; good counterexample target |
| [NTS#819](https://github.com/NetTopologySuite/NetTopologySuite/issues/819) — prepared A-L cache (JTS#1099) | Open (perf); **proof companion partial (S13–S14)** | Prepared correctness must be **result-independent of cache path**; generic + rectangle-boundary area-line refinement in `RelatePreparedCache*.v` |
| Overlay/relate bugs (#1000, #1122, …) | Mixed | Predicate errors often surface via overlay validity |

## 2. Strategic context already on record

**Phase 3 overlay ≠ Phase 7 predicates.** The corpus has a strong overlay
story (`boolean_op`, `TopologyGraph`, `overlay_ng_correct_conditional`) but
overlay answers *set combination* ("what is A ∪ B?"), while RelateNG answers
*topological classification* ("does A contain B?"). They share noding and
segment intersection machinery but need a **new DE-9IM layer**.

**Reuse spine (already Qed):**

- Segment intersection decision + completeness (`theories/Intersect.v`).
- Point-in-polygon via crossing parity (`Overlay.v` `point_in_ring` /
  `point_in_polygon`).
- Labelled planar graph after noding (`OverlayGraph.v` — edge `in_left` /
  `in_right` flags).
- Conditional point-in-ring ↔ interior (`PointInRingCorrect.v`,
  `JordanCurveSeam.v`, `JCT.v`).

**Hard constraints inherited from overlay/JCT work:**

- Full `point_in_ring_correct` without named hypotheses is **not** closed —
  the parity ↔ interior seam (`parity_characterises_interior_cont_strict`) is
  the genuine JCT content. Predicate proofs that reduce to "point in polygon"
  inherit this seam honestly (conditional headlines or guarded special cases).
- `DE9IM.v` / `IntersectionMatrix` landed in S1; regime→witness selection
  through S12; **prepared-cache refinement** landed S13–S14 (`RelatePreparedCache.v`,
  `RelatePreparedCacheAreaLine.v`). Full RelateNG matrix-fill from geometry
  (noding) remains absent.

## 3. Per-ask status

| Ask | Status | Anchor (file:line) | Notes |
|-----|--------|-------------------|-------|
| **#1 DE-9IM matrix type + entries** | **LANDED (S1)** | `DE9IM.v` | `IntersectionMatrix`, `matrix_matches`, JTS/OGC pattern tables. |
| **#2 Standard predicate definitions** | **LANDED (S1)** | `DE9IM.v` | `im_disjoint`, `im_intersects`, `im_contains`, `im_touches`, … + `predicate_holds`. |
| **#3a Segment intersection (line-line)** | **PROVEN (Qed)** | `Intersect.v:900` (`segment_intersection_decision`), `:243` (`strict_completeness`) | Feeds `Intersects`/`Crosses`/`Touches` for line-line; collinear case closed (`collinear_share_iff_1d_overlap`). |
| **#3b Point-in-polygon (area-point)** | **DEFINED; correctness PARTIAL** | `Overlay.v:183-203` (`point_in_ring`, `point_in_polygon`, `point_in_geometry`) | Algorithm defined; full correctness is conditional on JCT seam (`point_in_ring_correct_jct_cont` in `PointInRingCorrect.v`). |
| **#3c Boundary / endpoint semantics** | **PARTIAL (S4b)** | `RelateBoundary.v` | MOD2 `BoundaryNodeRule`, endpoint vs interior contact predicates, Touches/Intersects soundness; JTS#1175 class pinned via test 10. Area-point boundary Touches in `RelateAreaPoint.v`. Full RelateNG boundary fill still absent. |
| **#4 RelateNG algorithm** | **PARTIAL (S15b)** | `RelateNodingLineLine.v` | Line×line segment strata + point-set DE-9IM spec; disjoint + proper-cross + collinear-overlap meet-layer bridges to S8 `line_pair_fill`. Share / OGC exterior rows / collections remain S15c+. |
| **#5 Prepared-mode correctness** | **PARTIAL (S13–S14)** | `RelatePreparedCache.v`, `RelatePreparedCacheAreaLine.v` | Generic + segment + rectangle-boundary area-line refinement; full `relate(A,B)` pipeline still absent. |
| **#6 Oracle / extraction** | **PARTIAL (S11)** | `oracle/relate_matrix.ml`, `driver.ml` | `RELATE_MATRIX` + `RELATE_PREDICATE` on pinned catalog; no geometry compute. |
| **#7 Curve-aware predicates (V-CP, R-*)** | **PARTIAL (S12)** | `RelateArcChord.v`, `RelateCurveAreaPoint.v` | Arc×line + curve-polygon×point (chord rect via `to_geometry`). Chord-length bridge now closed (`ArcChordLength.v`); arc-span soundness partially closed (`ArcChordSound.v`, side/endpoint-conditioned). `to_geometry` point-in-ring bridge (S12b) now closed (`point_in_rect_curve_geometry_iff_polygon`). |

## 4. Inventory of reusable assets

**R-side (`theories/`, 3 axioms, Admitted-free on these modules):**

- `Overlay.v` — `Geometry`, `valid_geometry`, `point_in_ring`, `point_in_polygon`,
  `boolean_op`, `edge_crosses_ray`, `segments_intersect_properly`.
- `Intersect.v` — segment intersection decision, strict/collinear completeness.
- `OverlayGraph.v` — `TopologyGraph`, `EdgeLabel`, `correct_labels_all_ops`.
- `PointInRingCorrect.v` — `segment_crosses_ray` bool soundness, JCT-conditional
  headlines, generic-position guards.
- `Bbox.v` — `bbox_disjoint` (necessary but not sufficient for geometry
  disjoint).
- `RelatePreparedCache.v` — prepared-mode cache refinement (`evaluate_eq_brute`,
  `prepared_intersects_eq_brute`); STRtree query = permutation of bbox-overlap
  filter; path-independence corollaries.
- `RelatePreparedCacheAreaLine.v` — area-line carrier instance
  (`rect_boundary_segments`, `prepared_area_line_intersects_eq_brute`); rectangle
  boundary edges indexed once, line envelope as query box (NTS#819 shape).

**Flocq layer (`theories-flocq/`):**

- `Intersect_b64.v` / `Intersect_b64_exact.v` — robust segment intersection
  (feeds line-line noding for relate).
- `OverlayCorrectness.v` — conditional overlay headline (not predicate-level).

**Oracle (`oracle/`):**

- `driver.ml` — ORIENT / INTERSECT / INCIRCLE / … plus S11 `RELATE_MATRIX` /
  `RELATE_PREDICATE` (pinned-catalog lookup; not geometry compute).

## 5. The genuine gaps, by nature (post S4b)

1. **Closed through S10b (#1–#2, partial #3/#7):** `DE9IM.v` pattern algebra;
   line-line witnesses + geometry (`RelateLineLine.v`); Romanschek oracle pins
   (S3); rectangle membership + Contains/Touches witnesses (`RelateAreaPoint.v`);
   MOD2 / endpoint-contact geometry + JTS#1175 class (`RelateBoundary.v`);
   rectangle vs segment witnesses (`RelateAreaLine.v`);
   rectangle-pair witnesses (`RelateAreaArea.v`);
   regime→witness selection for rect×rect (`RelateMatrixRect.v`), line×line
   (`RelateMatrixLineLine.v`), area×line (`RelateMatrixAreaLine.v`), and
   arc×line chord path (`RelateArcChord.v`, `RelateMatrixArcChord.v`),
   Option-A analytic arc (`RelateArcAnalytic.v`, `RelateMatrixArcAnalytic.v`),
   and clothoid chord seed (`RelateClothoid.v`, `RelateMatrixClothoid.v`).
   These prove the selected witness matrices satisfy their predicates and the
   genuine per-regime geometry (shared point / its absence / mutual exclusion);
   they do NOT derive a matrix from geometry — the regime→true-DE-9IM bridge is
   the deferred RelateNG noding step.  Oracle fill vocabulary + seeds through
   seven selection APIs (through S12; `oracle/relate_matrix_fill_vocabulary.txt`,
   `oracle/de9im_*_vectors.txt`).  Full RelateNG noding remains absent; S11
   `RELATE_MATRIX` / `RELATE_PREDICATE` modes serve pinned-catalog differential
   tests only.

2. **Algorithm gap (#4) — still open:** RelateNG is a full arrangement
   classifier (point, line, area, collection, zero-length lines, union
   semantics). Comparable to Phase 3 overlay in scope.

3. **Inherited JCT seam (#3b) — narrowed, not closed:** Strict-interior
   rectangle Contains is guarded via `RectangleJCT.v`. General polygons and
   half-open boundary regimes (Contains vs Touches) still need explicit
   guards or JCT-linked proofs.

4. **Boundary policy (#3c) — partial:** Endpoint vs interior predicates and
   MOD2 classification are formalised at the soundness-witness layer. Full
   line-end enumeration on multi-component collections and matrix-fill
   fidelity remain open.

5. **Prepared cache (#5) — partial (S13–S14):** Generic monoid refinement +
   segment-intersects + rectangle-boundary area-line instances are **PROVEN**
   in `RelatePreparedCache.v` / `RelatePreparedCacheAreaLine.v`. The remaining
   obligation is end-to-end `evaluate(prepare(A),B) = relate(A,B)` once the
   RelateNG pipeline (ask #4) exists; polygon-envelope early-exit (S14b) queued.

6. **Curve extension (#7):** S12 lands chord rect curve-polygon × point carrier
   (S4 guard delegation); the `to_geometry` point-in-ring bridge (S12b) is now
   closed (`point_in_rect_curve_geometry_iff_polygon`). The crossing-number
   transport foundation also landed: `RayParityDegenerate.v` proves a
   zero-length `(v,v)` edge is parity-neutral, so Phase-3 `point_in_ring` facts
   move to `flat_map` chord rings (which carry `(v,v)` edges at joins). On that
   foundation the **first genuine curve→matrix soundness** landed
   (`RelateCurveAreaPointSound.v`): `point_in_ring_chord_rect_iff` (chord ring ≡
   `rect_ring` on point-in-ring) + `strict_interior_in_rect_curve_{polygon,geometry}`
   (the chord-rect curve geometry Contains its strict interior, transporting S4).
   General curve surfaces, arc outer rings, and the matrix-fill side remain open.

## 6. Risk/cost-ordered options for the next (Coq) terminal

S0–S14 closed items **(A)–(D)**, JTS#1175 **(C)**, area-line **(G)**,
area-area **(H)**, rect×rect fill **(J)**, line×line fill **(K)**,
area×line fill **(L)**, arc-chord relate **(M)**, and prepared cache **(F)**.
Next frontier:

- **(E) Full RelateNG noding pipeline** — *high / multi-session.* **Primary
  next rung (S15c+).** S15a–S15b land line×line strata + disjoint/proper-cross/
  collinear-overlap bridges (`RelateNodingLineLine.v`). Remaining: share regime,
  OGC exterior rows, collections, zero-length lines, union semantics —
  Phase-3-scale.

- **(F) Prepared A-L cache correctness** — **partial (S13–S14).** Generic
  refinement + rectangle-boundary area-line instance in `RelatePreparedCache*.v`;
  polygon-envelope early-exit (S14b) and full-pipeline hook remain queued.

- **(I) Oracle `RELATE_MATRIX` driver** — **done (S11).** `oracle/relate_matrix.ml`
  + `RELATE_MATRIX` / `RELATE_PREDICATE` in `oracle/driver.ml`.

## 7. Scope note for the issue owner

#67 spans **predicate semantics** (seeded through S12 curve-polygon × point +
seven fill APIs), **prepared-cache refinement** (S13–S14), and **RelateNG
implementation fidelity** (full noding still open; S11 oracle modes landed).
The recommended path forward:

- **S10b (done):** Option-A analytic arc (`RelateArcAnalytic.v`,
  `RelateMatrixArcAnalytic.v`); clothoid chord seed (`RelateClothoid.v`,
  `RelateMatrixClothoid.v`); oracle seeds
  `de9im_arc_analytic_vectors.txt`, `de9im_clothoid_vectors.txt`. The
  **law-of-cosines chord-length bridge at `arc_sweep_angle` is now CLOSED**
  (`ArcChordLength.v : arc_chord_dist_sq_via_sweep`, squared form
  `dist_sq(start,end) = 2·dist_sq(center,start)·(1 − cos sweep)`, built on a
  provider-agnostic `law_of_cosines_equal_norm` over `cos_angle_between`); the
  clothoid lane's remaining open questions are triaged in
  [`clothoid-open-questions-triage.md`](clothoid-open-questions-triage.md).
- **S11 (done):** `RELATE_MATRIX` / `RELATE_PREDICATE` oracle modes.
- **S12b (done):** the `to_geometry` ↔ linearised-rectangle point-set bridge
  (`RelateCurveAreaPoint.v : point_in_rect_curve_geometry_iff_polygon`, 0 axioms);
  the S4 Contains/Touches facts now transport to the curve geometry's point set.
- **S12 (done):** curve-polygon × point carrier + fill (`RelateCurveAreaPoint.v`,
  `RelateMatrixCurveAreaPoint.v`); oracle `de9im_curve_area_point_vectors.txt`.
  S12b (the `to_geometry` point-in-ring bridge) now closed:
  `point_in_rect_curve_geometry_iff_polygon`.
- **S13 (done):** prepared-mode cache refinement (`RelatePreparedCache.v`); generic
  monoid + segment-intersects concrete instance.
- **S14 (done):** area-line carrier instance (`RelatePreparedCacheAreaLine.v`);
  rectangle boundary edges + line envelope query. Open: polygon-envelope early-exit (S14b).
- **S15a (done):** line×line point-set DE-9IM bridge (`RelateNodingLineLine.v`);
  disjoint + proper-cross meet-layer bridges; `Intersect.v` strict-interior
  intersection parameters.
- **S15b (done):** proper-cross IB/BI/BB emptiness + collinear-overlap II=1
  bridge (`classify_proper_cross_line_point_ii_ib_meet`,
  `classify_collinear_overlap_line_ii_cell` with `C <> D`).
- **S15c+:** share regime, OGC exterior rows, collections.

## 8. Proposed milestone sketch (if accepted)

| Session | Deliverable | Depends on |
|---------|-------------|------------|
| S1 | `theories/DE9IM.v` — matrix type, pattern match, standard predicate Props | — |
| S2 | `theories/RelateLineLine.v` — line-line DE-9IM via `Intersect.v` | S1 |
| S3 | Romanschek line-line oracle matrices (`RelateLineLine.v` tests 6–13) | S2 |
| S4 | Guarded `Contains` for axis-aligned rectangle (`RelateAreaPoint.v`) | S1 + `RectangleJCT.v` |
| S4b | Boundary / MOD2 policy — endpoint contact + JTS#1175 class (`RelateBoundary.v`; area-point boundary Touches in `RelateAreaPoint.v`) | S2 + S4 |
| S5 | Area-line witnesses + pierce geometry — guarded rectangle vs segment (`RelateAreaLine.v`) | S2 + S4 |
| S6 | Area-area witnesses — guarded rectangle pairs (`RelateAreaArea.v`) | S4 |
| S7 | Rect×rect regime→witness selection — `rect_pair_fill` + regime mutual exclusion (`RelateMatrixRect.v`) | S6 |
| S8 | Line-line matrix fill (`RelateMatrixLineLine.v`) | S2 |
| S9 | Area-line matrix fill (`RelateMatrixAreaLine.v`) + fill vocabulary seed | S5 |
| S10 | Arc×line chord-path relate + fill (`RelateArcChord.v`, `RelateMatrixArcChord.v`) | S2 + arc stack |
| S10b | Option-A analytic arc + clothoid (`RelateClothoid.v`) | S10 + `Atan2` |
| S11 | Oracle `RELATE_MATRIX` + `RELATE_PREDICATE` (`relate_matrix.ml`) | S2–S10b |
| S12 | Curve-polygon × point + fill (`RelateCurveAreaPoint.v`) | S4 + `CurveGeometry` |
| S13 | Prepared-mode cache refinement (`RelatePreparedCache.v`) | S1 + `Bbox.v` |
| S14 | Area-line prepared-cache instance (`RelatePreparedCacheAreaLine.v`) | S13 + `RectangleJCT.v` |
| S15a | Line×line noding bridge (`RelateNodingLineLine.v`) | S8 |
| S15b | Proper-cross meet layer + collinear-overlap II bridge | S15a |
| S15c+ | Share + OGC exterior rows + collections | S15b |