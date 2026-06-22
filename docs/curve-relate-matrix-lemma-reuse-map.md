# Lemma Reuse Map — CURVE_RELATE_MATRIX (lineal analytical slice, R-PR / JTS #1195)

This map was produced during the mandatory READ phase before any code changes.
Only lemmas/theorems that **actually exist** in the repo are listed. Vague entries avoided.

## Core arc/arc and arc/segment intersection existence + symmetry

- **Exact id**: `arc_arc_intersects_sym` (Lemma)
  - File: `theories/ArcIntersect.v:184`
  - Fact: `arc_arc_intersects a1 a2 <-> arc_arc_intersects a2 a1`
  - Reuse in CURVE_RELATE_MATRIX: When collecting BB witnesses via symmetric pair enumeration (A-segs vs B-segs), transpose consistency of hasBB / crosses for matrix transpose does not require new proof.
  - Why sufficient: Directly reuses the proven commutativity of the existence predicate used by the ARC_ARC_XY kernel (and RING_SIMPLE). No ad-hoc symmetry argument in matrix path.

- **Exact id**: `arc_chord_intersects_sym` (Lemma)
  - File: `theories/ArcIntersect.v:166`
  - Fact: arc_chord_intersects a P Q <-> arc_chord_intersects a Q P
  - Reuse: Mixed arc/segment (CompoundCurve) pair_pts; symmetry for BI/IB classification.
  - Why: Same justification as above; reuses existing lemma backing ARC_SEGMENT_XY.

- **Exact id**: `chord_crosses_arc_circle_sym` (Lemma)
  - File: `theories/ArcIntersect.v:195`
  - Fact: chord_crosses_arc_circle a P Q <-> ... Q P (product commutativity)
  - Reuse: As a fast positive filter inside boundary contact or crosses detection when lifting from chord-cross to real arc contact (conditional path).
  - Why: Avoids re-proving sign symmetry for the sufficient condition.

- **Exact id**: `arc_arc_intersects_shared_vertex` (Theorem)
  - File: `theories/ArcArcSound.v:75`
  - Fact: `arc_end a1 = arc_start a2 -> arc_arc_intersects a1 a2` (unconditional; no IVT)
  - Reuse: Detecting BB contact at join points of two CompoundCurves / CircularStrings (or within a curve for self, but mainly inter-curve endpoint touch). Justifies endpoint-touch as hasBB without needing full coordinate intersection.
  - Why: This is the exact case for adjacent segments in curve chains (`curve_ring_adjacent` / `curve_segment_end`/`start` equality). Reused rather than a weaker ad-hoc "if endpoints equal then contact" claim.

- **Exact id**: `arc_arc_intersects_shared_vertex_rev` (Corollary)
  - File: `theories/ArcArcSound.v:89`
  - Fact: symmetric of the above (start/end flip).
  - Reuse: Same BB endpoint classification (order-independent wiring in pair enumeration).
  - Why: Direct from the headline theorem via `arc_arc_intersects_sym`.

- **Exact id**: `inCircle_R_arc_start_self`, `inCircle_R_arc_end_self` (Lemmas)
  - File: `theories/ArcArcSound.v:56`, `:61`
  - Fact: An arc's own endpoints satisfy `inCircle_R start mid end endpoint = 0` (lie on circumcircle).
  - Reuse: Combined with arc_span_contains_{start,end} to establish that shared endpoints are full members of `arc_arc_intersects`.
  - Why: These are the load-bearing membership facts inside the proof of `arc_arc_intersects_shared_vertex`; reuse prevents re-proving trivial but critical on-circle property.

- **Exact id**: `arc_span_contains_start`, `arc_span_contains_end` (Lemmas)
  - File: `theories/ArcIntersect.v:140`, `:148`
  - Fact: `arc_span_contains a (arc_start a)` and likewise for end (by definition of span).
  - Reuse: Point-on-boundary at endpoints for Point ↔ {CircularString,CompoundCurve}; also shared-vertex BB.
  - Why: Explicitly ties zero-distance / exact endpoint equality to boundary stratum membership without new span reasoning.

- **Exact id**: `arc_span_contains_mid` (Lemma)
  - File: `theories/ArcIntersect.v:156`
  - Fact: mid is in span (under valid_arc, via arc_interior_side).
  - Reuse: Midpoint samples in boundary scanning for lineal; confirms control point of arc is boundary.
  - Why: Reuses the same directed-sweep (Option S) characterisation used everywhere else.

## Point-to-arc / boundary classification (zero distance <=> on boundary)

- **Exact id**: `radial_foot_on_arc_when_span` (Lemma)
  - File: `theories/ArcPointDistance.v:52`
  - Fact: If radial foot F of P onto circle lies in arc_span_contains, then `on_arc a F`.
  - Reuse: In pointOnBoundary test for Point vs arc segment inside CircularString/Compound; combines with inCircle=0.
  - Why: This is the exact bridge from distance geometry to the arc membership used by ARC_DISTANCE; reuse for "point on boundary" vs exterior decision.

- **Exact id**: `point_to_arc_dist_radial_lower` (Lemma)
  - File: `theories/ArcPointDistance.v:83`
  - Fact: On-arc X implies |dist O P - r| <= dist P X (soundness).
  - Reuse: Justifies that if computed distance (via ARC_DISTANCE path or direct) is zero then the point realises boundary contact.
  - Why: Prevents weaker ad-hoc "distance small => boundary" in matrix hasBI/IB for point cases.

- **Exact id**: `point_to_arc_attains_radial` (Lemma)
  - File: `theories/ArcPointDistance.v:109`
  - Fact: The radial foot (when in span) attains the distance.
  - Reuse: For exact "point lies on arc boundary" classification when radial foot test passes.
  - Why: Attainment + lower bound together give iff for the radial case.

- **Exact id**: `point_to_arc_dist_fallback_ends_lower`, `point_to_arc_dist_centre_is_r`
  - Files: `theories/ArcPointDistance.v:134`, `:162`
  - Fact: Off-sweep fallback to endpoint min; centre special case = r.
  - Reuse: Complete the pointOnBoundary decision tree for all positions (endpoint, centre, near-chord but off).
  - Why: Existing case analysis; do not duplicate.

- **Exact id**: `point_circle_dist_lower` (Theorem)
  - File: `theories/ArcDistance.v:49`
  - Fact: Reverse triangle: any circle point X gives |OP - r| <= PX.
  - Reuse: Foundational for all point-to-arc zero tests (on_circle => dist lower bound 0 iff on).
  - Why: Core metric fact reused by ArcPointDistance and ARC_DISTANCE oracle mode.

- **Exact id**: `radial_foot_on_circle`, `radial_foot_dist` (Lemmas)
  - File: `theories/ArcDistance.v:78`, `:98`
  - Fact: Radial foot construction lands on circle and realises exact distance.
  - Reuse: Same as above for boundary predicate.

- **Exact id**: `two_circles_dist_lower`, `circle_feet_dist`, `two_circles_dist_radial`, `arc_arc_dist_external` (Theorem/Lemmas)
  - File: `theories/ArcArcDistance.v`
  - Fact: External circle-to-circle distance soundness + attainment (d - r1 - r2).
  - Reuse: For disjoint / touch decision when two arcs' circles are separate (quick reject for hasBB); distance-0 implies interior or boundary contact when sweeps overlap.
  - Why: Reuses the D-AA core instead of local distance reasoning inside relate.

## inCircle / orientation primitives (decision soundness, invariance)

- **Exact id**: `inCircle_R_at_A`, `inCircle_R_at_B`, `inCircle_R_at_C` (Lemmas)
  - File: `theories/ArcOrient.v:199` et seq.
  - Fact: Endpoints and mid of the defining triple give det=0.
  - Reuse: Basis for all self-membership and arc_arc_intersects constructions.
  - Why: Already Qed; the matrix path inherits via the shared kernels.

- **Exact id**: `arc_interior_side_mid`, `arc_orient_mid` (Theorems)
  - File: `theories/ArcOrient.v:170`, `:183`
  - Fact: Midpoint lies in interior side; orient classification.
  - Reuse: Span tests and mid-sample classification in lineal boundary scans.
  - Why: Reused from the same orient used by all arc predicates.

- **Exact ids**: `inCircle_R_swap_*`, `inCircle_R_cyclic`, `inCircle_R_translation_invariant`, `inCircle_R_scaling`, `inCircle_R_rotation_invariant`, `inCircle_R_scale_pos_iff_pos` (family of Lemmas)
  - File: `theories/ArcOrient.v:228`...
  - Fact: Invariance and sign behaviour of the 4-point predicate.
  - Reuse: Ensures that BB intersection decisions (and pointOnBoundary) are stable under the rigid motions / scaling that preserve geometry in RGR comparisons; also supports symmetry without re-proof.
  - Why: These establish "the predicate decision is geometrically meaningful" — reuse rather than local numeric robustness arguments.

- **Exact ids**: `arc_coord_safe_px`, `arc_coord_safe_py` (Lemmas, ArcOrient.v:334)
  - Fact: Coord safety lifting for arc controls (ties to coord_int_safe pattern).
  - Reuse: When routing through safe-domain facts for any future b64 exact path; documents that current interface-boundary uses the same safety mindset as Orient/Intersect exact.
  - Why: Pattern reuse from safe int domain lemmas even if not direct extract here.

## Matrix algebra + specification (no new universe)

- **Exact ids**: `matrix_transpose`, `matrix_matches_transpose`, `matrix_ok`, `char_false_empty`, `char_true_nonempty`, and the family `disjoint_not_intersects_*`, `intersects*_not_disjoint`, `im_*_matches_some_*`, `not_intersects*_nonempty` (DE9IM.v)
  - File: `theories/DE9IM.v` (multiple)
  - Fact: DE-9IM structural laws, transpose, pattern matching, nonempty <=> some dim value.
  - Reuse: In relate_matrix.ml (already) and when constructing or validating the emitted 9-char for lineal cases; predicate_holds uses the patterns. For lineal matrices the same algebra applies to the cells we do populate (0/1/F).
  - Why: Do not duplicate matrix cell reasoning; the lineal path only supplies the DimValue facts from analytical leaves and lets the algebra hold.

- **Exact ids** (from RelateCurveMatrix.v, reused for algebra even on lineal): `geom_de9im_matrix_ok`, `geom_de9im_ee_nonempty`, `geom_de9im_pointset_transpose`, `cell_ok_swap_imp`
  - File: `theories/RelateCurveMatrix.v:223`...
  - Fact: Matrix well-formedness, EE nonempty, transpose law at point-set level.
  - Reuse: The transpose law and well-formedness checks are referenced in driver comments and test I2; the pointset spec inspires the lineal stratum (no area => no dim-2 except possibly EE). For lineal we still guarantee a well-formed matrix and transpose consistency via the same cell_ok shape.
  - Why: The algebraic laws are proven independently of areal vs lineal; reuse avoids any parallel matrix-proof development.

## Boundary / adjacency facts (from CurveGeometry)

- **Exact ids**: `curve_ring_adjacent`, `curve_segment_start`, `curve_segment_end`, `valid_arc`, `curve_ring_arcs_valid` (definitions + lemmas in CurveGeometry.v and users)
  - Fact: Consecutive segments meet end==start; validity requires valid_arc + adjacency + closed (for rings).
  - Reuse: In lineal path, we do *not* require closed; but we reuse adjacency definition to recognise "structure-equivalent" for EQUAL case, and to skip adjacent-within-curve joins when looking for proper crosses (permitted shared vertices).
  - Why: Exact match to the model used by RING_SIMPLE / CurveRingSimple.v; no redefinition.

## Safe-domain / extraction contract pattern (theories-flocq)

- **Exact ids**: `coord_int_safe` (and `intersect_inputs_int_safe`, `intersect_point_inputs_int_safe`)
  - File: `theories-flocq/Orient_b64_exact.v`, `theories-flocq/Intersect_b64_exact.v`
  - Fact: When coords are int-safe (<=2^25 in abs, finite), certain operations (dets, intersections) stay exact or have proven error bounds.
  - Reuse: In the lineal matrix path we follow the same "exact centres via circumcentre_q (Q), then only interface-boundary sqrt/atan2" contract already used by ARC_ARC_XY / ARC_SEGMENT_XY. Document that we stay inside the regime where the proven R-side predicates justify the float decisions (no new unsafe float reasoning). Future b64 extract for arc relate can plug the safe predicates directly.
  - Why: Reuses the established extraction safety pattern rather than inventing per-matrix safety.

## Existing extraction / kernel contracts (driver reuse)

- The `arc_arc_pts`, `arc_seg_pts`, `chord_chord_pts`, `pair_pts` functions (and `point_on_arc_sector`, `circumcentre_q`) inside driver.ml are the **identical kernels** behind:
  - `run_arc_arc_xy`
  - `run_arc_segment_xy`
  - `run_ring_simple`
- These are already pinned by adversarial suites (arc_arc_tests.txt, arc_segment_tests.txt, ring_simple_tests.txt) and have Coq companions (ArcArcCircles.v, ArcSegmentCircles.v, ArcIntersectIVT.v, CurveRingSimple.v).
- **Reuse contract**: CURVE_RELATE_MATRIX lineal BB detection **calls the same functions** (or a thin shared helper) instead of duplicating geometry logic. This composes the kernels rather than creating a parallel "matrix geometry" implementation.

---

## Missing facts (honestly isolated; none invented for v1)

- No unconditional "interior point of arc A lies on arc B" existence lemma beyond the conditional `arc_arc_intersects_of_chord_cross_cond` + IVT (ArcArcSound.v + ArcIntersectIVT.v). For v1 lineal we rely on the same witness enumeration used by ARC_ARC_XY (float candidates + span filter). The matrix only claims "contact exists" when the driver witness list is non-empty, consistent with how ARC_ARC_XY reports.
- Reflex arcs (sweep >= pi) span characterisation remains the documented limitation of the chord-side `arc_span_contains` (everywhere, including RING_SIMPLE). v1 inherits it; tests avoid or note.
- Full cell-dimension soundness for lineal (II=1 for overlap runs) is test-pinned / independent-sampling, as for areal CURVE_RELATE (no overlay in proofs repo). We only populate 0/1 where the sampling + witness list + structure match give clear evidence.

All other facts needed for the first slice (disjoint / touch / cross / pointOnBoundary / equal for the listed combinations) are covered by the reused items above.

## Why this satisfies "actual reuse, no reproof of low-level"

- Intersection existence decisions flow through `arc_arc_intersects*` and the shared `pair_pts` implementation.
- Symmetry flows through the sym lemmas rather than `a,b vs b,a` ad-hoc.
- Boundary (zero dist / on sweep / shared vertex) flows through ArcPointDistance + ArcArcSound + ArcIntersect span lemmas.
- Safe/exact domain mindset reuses the Q-centres + coord_int_safe pattern.
- Matrix algebra reuses DE9IM + RelateCurveMatrix laws.
- No new R-side existence predicate or new IVT application was added.

If a needed sub-claim had no lemma, it would be listed above under "Missing". For this scope, none were required.
