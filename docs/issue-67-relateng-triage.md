# Issue #67 — RelateNG / DE-9IM predicates: research & gap triage

> **Status:** living triage — S0–**S12** **complete in the working tree**
> (2026-06-11); **S13+** (full RelateNG noding, prepared cache) remains open.
> Refresh when a new session closes.
>
> Corpus at time of writing: `main` through S3; S4–S10 add `RelateAreaPoint.v`,
> `RelateBoundary.v`, `RelateAreaLine.v`, `RelateAreaArea.v`,
> `RelateMatrixRect.v`, `RelateMatrixLineLine.v`, `RelateMatrixAreaLine.v`,
> `RelateArcChord.v`, `RelateMatrixArcChord.v` (pending commit).

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
| [NTS#819](https://github.com/NetTopologySuite/NetTopologySuite/issues/819) — prepared A-L cache (JTS#1099) | Open (perf) | Prepared correctness must be **result-independent of cache path** |
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
- `DE9IM.v` / `IntersectionMatrix` landed in S1; **RelateNG matrix-fill**
  and prepared-cache paths are still absent from `theories/`.

## 3. Per-ask status

| Ask | Status | Anchor (file:line) | Notes |
|-----|--------|-------------------|-------|
| **#1 DE-9IM matrix type + entries** | **LANDED (S1)** | `DE9IM.v` | `IntersectionMatrix`, `matrix_matches`, JTS/OGC pattern tables. |
| **#2 Standard predicate definitions** | **LANDED (S1)** | `DE9IM.v` | `im_disjoint`, `im_intersects`, `im_contains`, `im_touches`, … + `predicate_holds`. |
| **#3a Segment intersection (line-line)** | **PROVEN (Qed)** | `Intersect.v:900` (`segment_intersection_decision`), `:243` (`strict_completeness`) | Feeds `Intersects`/`Crosses`/`Touches` for line-line; collinear case closed (`collinear_share_iff_1d_overlap`). |
| **#3b Point-in-polygon (area-point)** | **DEFINED; correctness PARTIAL** | `Overlay.v:183-203` (`point_in_ring`, `point_in_polygon`, `point_in_geometry`) | Algorithm defined; full correctness is conditional on JCT seam (`point_in_ring_correct_jct_cont` in `PointInRingCorrect.v`). |
| **#3c Boundary / endpoint semantics** | **PARTIAL (S4b)** | `RelateBoundary.v` | MOD2 `BoundaryNodeRule`, endpoint vs interior contact predicates, Touches/Intersects soundness; JTS#1175 class pinned via test 10. Area-point boundary Touches in `RelateAreaPoint.v`. Full RelateNG boundary fill still absent. |
| **#4 RelateNG algorithm** | **ABSENT** | — | No noding + matrix-fill pipeline; JTS uses point-local topology + union semantics for collections. |
| **#5 Prepared-mode correctness** | **ABSENT** | — | NTS#819 is perf-only; proof obligation is `evaluate(B) = relate(A,B)` regardless of cache. |
| **#6 Oracle / extraction** | **PARTIAL (S11)** | `oracle/relate_matrix.ml`, `driver.ml` | `RELATE_MATRIX` + `RELATE_PREDICATE` on pinned catalog; no geometry compute. |
| **#7 Curve-aware predicates (V-CP, R-*)** | **PARTIAL (S12)** | `RelateArcChord.v`, `RelateCurveAreaPoint.v` | Arc×line + curve-polygon×point (chord rect via `to_geometry`). Chord-length bridge now closed (`ArcChordLength.v`); arc-span soundness partially closed (`ArcChordSound.v`, side/endpoint-conditioned). `to_geometry` point-in-ring bridge (S12b) still open. |

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

5. **Prepared cache (#5):** Correctness of memoisation is a **refinement**
   theorem — tractable once base `relate` is specified.

6. **Curve extension (#7):** S12 lands chord rect curve-polygon × point carrier
   (S4 guard delegation); `to_geometry` point-in-ring bridge is S12b. General
   curve surfaces and arc outer rings remain open.

## 6. Risk/cost-ordered options for the next (Coq) terminal

S0–S10 closed items **(A)–(D)**, JTS#1175 **(C)**, area-line **(G)**,
area-area **(H)**, rect×rect fill **(J)**, line×line fill **(K)**,
area×line fill **(L)**, and arc-chord relate **(M)**. Next frontier:

- **(E) Full RelateNG noding pipeline** — *high / multi-session.*
  Collections, zero-length lines, union semantics — Phase-3-scale engagement.

- **(F) Prepared A-L cache correctness** — *medium after (E).* Show cached
  `evaluate` = uncached `relate` for area-line pairs (NTS#819 proof companion).

- **(I) Oracle `RELATE_MATRIX` driver** — **done (S11).** `oracle/relate_matrix.ml`
  + `RELATE_MATRIX` / `RELATE_PREDICATE` in `oracle/driver.ml`.

## 7. Scope note for the issue owner

#67 spans **predicate semantics** (seeded through S12 curve-polygon × point +
seven fill APIs) and **RelateNG implementation fidelity** (full noding still
open; S11 oracle modes landed). The recommended path forward:

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
- **S12 (done):** curve-polygon × point carrier + fill (`RelateCurveAreaPoint.v`,
  `RelateMatrixCurveAreaPoint.v`); oracle `de9im_curve_area_point_vectors.txt`.
  Open: `to_geometry` point-in-ring bridge (S12b).
- **S13+:** full noding, prepared cache (**F**).

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
| S13+ | Full noding / prepared cache | S9–S12 |