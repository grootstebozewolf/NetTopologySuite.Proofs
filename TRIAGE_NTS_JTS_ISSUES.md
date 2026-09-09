# Triage — NTS / JTS open issues vs. NetTopologySuite.Proofs corpus

> **Source of record for the curve-awareness proof batch (#64–#69).** This is
> the report every batch issue cites. It maps the open NTS/JTS issues that the
> formal-proof corpus is meant to back onto **what is actually proven today**
> (`theories/`, `theories-flocq/`, `docs/verified-claims.md`), separating
> *proven* from *gap*, and recording priority and ordering decisions.
>
> Generated from the 2026-06-03 issue batch; last reconciled **2026-06-30**
> against HEAD (PRs #302–#307): the **clothoid buffer-soundness + winding-number
> wave** — clothoid offset validity/sharpness (`ClothoidBufferBridge.v`),
> clothoid–clothoid offset contact (`ClothoidOffsetContact.v`), whole-ring offset
> assembly (`ClothoidBufferAssembly.v`), offset-ring simplicity from clearance
> (`CurveRingOffsetSimple.v`), and an atan2-free **winding number** point-in-ring
> decider (`WindingNumber.v` — `winding_decides_membership`). Prior reconcile
> **2026-06-21** (HEAD e2552db): ARC_BUFFER_SIMPLE oracle RGR + d=0 soundness;
> #67 S15l JCT seam + Jordan cell-dimension + touch dispatch discharges;
> #64 arc point-dist two D-PT stubs discharged (one deferred remains);
> dashboard/claims refreshes. See per-child and oracle-curve-wishlist.md.
> **Wire map** (upstream → Proofs epic + `topic:`) authored **2026-08-03** —
> see §Wire map below (JTS/NTS drivers + proposed `topic: hull` / MBT epic).
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
> `docs/relate-ng-status.md` (RelateNG living status; the pre-#530 triage
> is archived at `docs/history/issue-67-relateng-triage.md`).

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
Option A structural `CurvePolygon`) and the NTS align epic (NTS#828). The
early-block tracker **#69** is owner-retire ready
(`docs/scout/69-closing-summary.md`); the index is this file's §Wire map.
#423 / #424 / #425 stand alone.

## Per-area status

| Issue | Area | Priority | Proof state | Verdict |
|---|---|---|---|---|
| **#64** | Circular-arc primitives (length, sweep, in-arc, in-circle) | `Immediate` | **Most progressed; metric + intersection suite landed.** Asks #1/#2: `Atan2.v` + `AngleBetween.v` + `ArcLength.v` (incl. `chord_le_arc_length`) Qed. **Ask #4b PROVEN (PR #146):** `InCircle_b64_exact.v`. **Metrics + intersect existence:** area/centroid/distance/oracle suite (ARC_*). **Arc sweep** disambiguation + fixes (`RelateArcAnalytic.v`, `arc_sweep_*`). **D-PT:** fully closed — `radial_lower`/`centre_is_r` discharged 2026-06-21, `fallback_ends_lower` 2026-06-28, and the underlying planar `arc_dot_max_at_endpoint` 2026-07-01 (chord-frame reduction, 3-axiom). Arc-line Scope B/C + arc-arc quartic coords are the exactness frontier. | Keep Immediate — D-PT fully closed (arc point-distance Qed); arc-arc quartic coords remain |
| **#65** | Buffer / offset curve correctness | `Urgent` | Heaviest existing corpus: 18 `Buffer*.v` files + `ExtractBufferRings.v`, plus 3 documented counterexamples. **Curve-aware:** arc offset (`arc_offset_preserves_arc`), assembly, buffer-region cert (`CurveBufferArea.v`). Oracle: ARC_OFFSET_XY / BUFFER_REGION / ARC_BUFFER_SIMPLE pins. **2026-06-21:** Coq `arc_buffer_simple_d0_is_identity` + unsafe radius lemmas; oracle RGR confirmation + coverage for ARC_BUFFER_SIMPLE (single-arc via offset+round-caps, degen/empty/pos cases) — ACCEPTED. **2026-06-30 (PRs #302–#306) clothoid buffer-ring soundness chain (all 3-axiom, Qed):** `clothoid_ring_offset_valid` (min-radius offset stays a valid ring) + sharpness; `clothoid_clothoid_offset_contact_sound` (two adjacent offset osculating arcs meet ONLY at their shared join); `clothoid_buffer_assembly_sound` (every join of the whole offset ring — interior + wrap — is a single clean contact); `curve_ring_simple_of_clearance` (non-adjacent offset segments meet NOWHERE when source clearance > 2·\|d\|, via a metric tube argument — chords + arcs). Together: a **simple-closed-curve certificate for well-separated clothoid buffer rings**. Minkowski-area soundness + the {-1,0,+1} winding characterisation for unconditional simplicity remain deferred. | Keep Urgent — clothoid buffer-ring soundness chain (validity → adjacent contact → whole-ring assembly → clearance simplicity) landed; Minkowski + unconditional simplicity deferred |
| **#66** | Precision / snap-rounding / OverlayNG soundness | `Urgent` | **Strongest coverage of the batch.** `SnapRounding_b64`, `HotPixel*`, `Hobby*`, the `PassesThrough_*` family (C1 grid-exactness reduction; plus a segment-reversal asymmetry negative that — correction 2026-06-17 — models a Liang-Barsky divide-from-c0 filter and does **NOT** map to JTS#752/#1133, since JTS's `HotPixel.intersectsScaled` canonicalizes to +X first), `Overlay*`, `RingArea979` (JTS#979). Multiple honest machine-checked **negatives** (rounded filter unsound/incomplete/asymmetric — cautions about that filter design, not JTS defects). C1 grid-exactness tight regime closed; overlay/ring conditional; curve-snap oracle present; JTS#979 mechanism certified; remaining gaps (C1 width, C2 parked, unconditional OV headline, arc Hobby) explicitly named in docs. | Keep Urgent — largely delivered, closing gaps |
| **#67** | RelateNG / 9IM matrix & boundary handling | `Immediate` | **DE-9IM suite through S15l + JCT/Jordan capstones.** S0–S12 matrix/witnesses, S13–S14 prepared-cache, S15a–k line×line noding. **67-a / 67-b** unit-square matrix + boundary graph. **S15l triangle touch (PR #263 + follow-ups):** strict_ii_no_common, bb_cell, satisfy_pointset + `touch_triangle_f_cells_trimmed`, `relate_triangle_touch` discharged (2026-06-21). **67-c (chunk S15l, PR #493):** line×line exterior-row true-dim pin (`RelateNodingLineLineExtPinned.v`, IE=1/EI=1/BE=0/EB=0/EE=2). **JCT seam + Jordan cell-dimension soundness** for triangle touch landed (d153665). Integer 0-axiom substrate. Curve oracle `CURVE_RELATE_MATRIX`. Remaining S15l+: Touches-vs-Share fill split, multi-geom, nine-cell `geom_de9im_pointset`. Triangle honesty / bar-1 / bar-2 gtri cells live on **#522** (row below). | Keep Immediate — 67-c exterior-row pin + JCT/Jordan landed; S15l+ pipeline leftovers remain. Ticket 523 grilled 2026-08-30 (`docs/scout/map-523.md`); still open, not accepted (`RelateCurveMatrix.v : cell_none_iff_empty`) |
| **#522** | RelateNG honest classifier (triangle bar 1 → bar 2) | `Expectant` | **Honesty:** fallthrough is `im_unsupported` / wire `UNSUPPORTED`, never a confident `FFFFFFFFF` (`RelateNGCore.v : relate_unsupported_no_predicate`). **Bar 1 (wired regimes):** overlap / disjoint / vertex-touch / contains (`RelateNGOverlap.v : triangle_pair_regime_overlap`, `RelateNGDisjoint.v : triangle_pair_regime_disjoint`, `RelateNGTouchVertexRegime.v : triangle_pair_regime_touchvertex`, `RelateNGContainsBridge.v : contains_b_ccw_implies_closed_containment`). Shared-edge touch stays the frozen predicate. **Completeness is false:** the T-junction / partial-edge kiss is now the named leftover-`Ⅰ` regime (`TPR_TouchPartialEdge` via the `touch_partial_edge_b` detector, `92d84e5` / PR #609) but stays `im_unsupported` on the wire; obtuse-at-v (leftover `ⅠⅠ`) still declines unclassified (`RelateNGComplete.v : triangle_pair_regime_incomplete_tjunction` recorded the finding; the decline golden moved to obtuse-at-v). **Bar 2 gtri cells (specified interior, not a remint of the classifier pins):** disjoint FF2FF1212 (`RelateNGDisjointCells.v : sentinel_disjoint_ogc_gtri_cells`); contains 212FF1FF2 (`RelateNGContainsCells.v : contains_pair_ogc_gtri_cells`); touch-edge FF2F11212 (`RelateNGTouchEdgeCells.v : touch_edge_pair_ogc_gtri_cells`); overlap 212101212 (`RelateNGOverlapCells.v : overlap_pair_ogc_gtri_cells`). Classifier still emits FFFFFFFFF / 2FFFFFFF2 / FFFF1FFF2 / 2FFF1FFF2. **Prepared:** cache-consulting `evaluate` (`RelatePrepared.v : prepared_evaluate_cache_short_circuit`). **Still declines on the wire:** T-junction (as the named `TPR_TouchPartialEdge` regime), obtuse-at-v, empty/empty, off-dispatch geometry. **Not this epic:** fill remints, leftover certificates, full noding, `geom_de9im_pointset`. Living map: `docs/scout/map-522.md`. Closing summary: `docs/scout/522-closing-summary.md`. Owner sign-off retires the epic. | Keep open until owner sign-off — wrap-up is #578 / `522-l` |
| **#68** | Delaunay triangulation / Voronoi correctness | `Non-urgent` | `Triangle.v`, `Tin.v`, `GeneralTriangle{Parity,Separation}.v`, `RightTriangle*`; **track opened 2026-07-04**: `DelaunayEmptyCircle.v` (empty-circle predicate ↔ exact `b64_inCircle` sign, #364) + `DelaunayFlipWitness.v` / `DelaunayFlipGeometric.v` (flip sign algebra + CCW transport) + **`DelaunayEdgeEmptyCircle.v` (68-a, PR #416):** weak-skeleton `delaunay_edge` ↔ incident-triangle empty circumcircle + **`DelaunayLocallyDelaunay.v` (68-b):** local-Delaunay packaging + flip refutes both-locally-Delaunay (+ mirror, rational flip witness). | Predicate + flip algebra + edge ↔ empty-circle (weak skeleton) + **local Delaunay / flip-refutes-both banked**; active residue is global/covering DT existence + geometric insert correctness + Voronoi dual |
| **#69** | Umbrella / epic tracker | `Expectant` | **Owner-retire ready.** One minted micro: `OracleCurveChecklist.v : w1_w5_coverage_table_complete` (`69-a`; do not remint). Children #64–#68 already retired; residue lives on successor epics. No replacement umbrella. Leftover TAGs (M-DIM / AT-* / LRF-* research; S-* technique) are parks in `docs/scout/69-closing-summary.md`. Packaging facades `JordanRingKit.v` / `JctSeamPack.v` stay `claimId: none`. | Owner review retires the tracker — this row is not "SQL/MM is done" |
| **#615** | ISO 13249-3 conformance for the curve foundation branch (fork `feat/curves-structure-wkt-foundation`; not proof work — differential + clause conformance, oracle-pinned) | `Expectant` | **A+B scope landed 2026-08-30; C (validity lane) opened and continues past the epic by design.** Captures (`615-a`, #616): ADR-0005 lenient-intake/strict-IsValid + CONTEXT.md *Curve conformance* glossary (`88e61e8` + `ce12455`). Fork landings: nested-CC flatten `2c4c7bc` (`615-b`, #617); empty-component intake drop `4c787c2`+`2d84afd` (`615-c`, #619); exact Length `2ccd353`+`df5ba57` (`615-d`, #618); exact Envelope `9111983`+`88e4af6` (`615-e`, #620); exact point-to-curve Distance `b829d42`+`61f4981` (`615-f`, #622); IsValid rung 1 `359b334`+`505ffaa` (`615-g`, #623); IsSimple rung 1 `b392590`+`e00c00b` (`615-h`, #624 — closed, continues at #630); WKT/WKB small print `ed40bf3`+`5fa469a` (`615-i`, #621). One-SoT: `docs/iso13249-3-curve-type-bindings-2026-08.md` (`SUMMARY ok`; §5b wrap-up gates: fork Curves+IO 441 green modulo the 4 pre-existing GML2 `WriteEmpty*`; illustrator 53/53, 0 skipped; oracle differential `ok=55 warn=0 bug_or_fail=0`; gauntlet `ok=5`). | Keep open until owner sign-off — wrap-up is #625 / `615-j`; the validity lane's next rung is #630 |

### Per-ask status for #66 (the 8 asks from issue body; accurate as of current state)
- #1 Snap-rounding / passes-through: ✅ (C1 grid-exactness tight regime closed per `PassesThrough_b64_grid_exact.v` slices 1-18) / 🟡 (full `2²⁵` width open)
- #2 Precision model / reducer: ✅ (idempotence `b64_snap_idempotent_finite`, shared-pixel etc.)
- #3 OverlayNG boolean semantics: ✅ (`Overlay.v : boolean_op`, labelling)
- #4 OverlayNG end-to-end correctness: 🟡 (conditional headline `overlay_ng_correct_conditional` under 3 hyps; ring extract conditional)
- #5 DCEL / ring assembly (for overlay): 🟢 (`extract_rings_valid_of_guards`, PRs #334–#362: the Euler hypotheses are DISCHARGED — `H_bridge_premise_holds` proves same-face ⇒ cut-edge Euler-free and `euler_characteristic_holds` proves V + F = E + 2C outright under the five geometric/noding guards; ring extraction is now guard-conditional only)
- #6 Fixed-precision hole collapse (JTS#979): ✅ (mechanism in `RingArea979.v` + oracles)
- #7 Curve snap (PRC-SN): ✅ (oracle `CURVE_SNAP_DECISION` / `CURVE_SNAP_INVARIANTS_EXACT`)
- #8 Oracle / differential testing: 🟡 (many modes extracted; interface-boundary for transcendentals; passes-through C1 oracle etc.)

Remaining gaps explicitly named (C1 full width, C2 parked, unconditional OV headline, arc Hobby analog) in `docs/snap-rounding-rgr-pivot.md`, `docs/verified-claims.md`, and issue #66. "largely delivered, closing gaps" verdict matches actual theorems/oracle modes.

## JTS #1195 TAG → proof-area mapping

The driving EPIC (locationtech/jts#1195) is structured as ~40 self-contained
**TAGs** across 7 phases ("one TAG per PR"). This maps the proof-relevant TAGs
onto the batch issues and the corpus artifacts that back them. Status:
**✅ proven** (Qed and/or extracted oracle) · **🟡 partial** (foundation/predicate
proven, soundness or coordinates open) · **⬜ planned** (not yet started) ·
**—** not proof-relevant (rendering / structural plumbing).

| JTS TAG | What it is | Proof issue | Corpus artifact / oracle | Status |
|---|---|---|---|---|
| **F-CP / F-MC / F-MS** | Structural `CurvePolygon` / `MultiCurve` / `MultiSurface` (preserve ring/member curves) | #64 · #509 | `CurveGeometry.v` (SQL/MM types, `CurveRing`, validity, chord bridge); `CurvePolygon{Valid,Simple,Orientation,Disjoint,Offset}.v`; oracle-backed exterior ring (`oracle/curve_polygon.py`, `CP_BOUNDARY_SIMPLIFY`) | 🟡 structural model + validity/simplicity witness-sound; true-region (Jordan) deferred |
| **B-CP / B-MS** | Boundary of curve composites | #65 · #515 | oracle `CP_BOUNDARY_SIMPLIFY` (densify → extracted `greedy_simplify_perp_b64` → per-corner `b64_orient_sign_filtered`); `CurveBufferArea.v` boundary | 🟡 densified-boundary oracle exists (INTSAFE corners certified by `_sound_small_int`); composite-boundary point-set spec deferred |
| **M-LEN-CS / M-LEN-CC** | Arc / compound-curve length (`r·θ`) | #64 · **#508** | `ArcLength.v`, `Atan2.v`, `AngleBetween.v`, `ArcRectifiable.v`, `CurveLength.v`; oracle `ARC_LENGTH_INVARIANTS_EXACT` / `ARC_SHORTER` | ✅ exact invariants; **`r·θ` meets the spec** (`ArcRectifiable.v : arc_r_theta_is_curve_length`); additivity is `CurveLength.v : curve_length_additive` (zoo wrap-up #566). Engine agreement remains differential; float length is interface-boundary |
| **M-LEN-ZOO** | Exact metric length across the Zoo (Bible §4.2 `length()`; order: ellipse → cubic Bézier → clothoid → single-span NURBS, `rx=ry` bridge as ellipse rung 1) | **#508** | ADR-0004; CONTEXT.md (*Exact curves*: Zoo, Exact, Oracle-stable, Metric length); Bible amendment A1 (`bible/a1-cubic-bezier` in the jts fork); oracle `LENGTH_UNIFIED` (`C`/`A` today — `E`/`B` extension + `K`/`N` mint owed, ISO 13249-3 projections); wrap-up `docs/scout/508-closing-summary.md` | ✅ #566 / 508-h. **Unconditional:** CircularArc `r·θ` (`ArcRectifiable.v : arc_r_theta_is_curve_length`); additivity (`CurveLength.v : curve_length_additive`); reparam/reflect (`CurveLength.v : is_curve_length_reparam`, `CurveLength.v : is_curve_length_reflect`); golden NURBS quarter (`NurbsConicExact.v : nurbs2_golden_quarter_length`); equal-weight N ⊃ B (`NurbsQuadraticLength.v : nurbs2_equal_weights_cubic`, `NurbsGeneralLength.v : nurbs3_equal_weights_length`); Bézier polygon ceiling (`Bezier3Polygon.v : bezier3_length_le_polygon`); unit straight clothoid window (`ClothoidLength_unit.v : unit_line_discharges_window`); knot-list additivity (`NurbsKnotSpans.v : nurbs_spans_additive`) and glued two-quarter instance (`NurbsKnotSpans.v : golden_half_circle_length`). **Engine-conditional (no inhabitant):** elliptic E (`EllipseSpeedIntegral.v : ellipse_speed_integral_is_curve_length`). **Fresnel clothoid inhabitant:** `ClothoidFresnelInhab.v : fresnel_unit_window_length_inhab` (Stdlib RiemannInt; Category C; board #564). Pack layer remains `ClothoidFresnel.v : fresnel_is_curve_length`. **Out of scope:** Cox-de Boor; Exact* zoo types / CurveSegment growth (year-1 is CSChord or CSArc; QEX `ExactCurveEpic508.v : ticket_508_qed_or_qex` is not owner accept); Bible §2.6 densify ≤1.15×. This flip is not "the zoo is unconditionally exact." Owner review retires #508. |
| **M-AREA-CP** | `CurvePolygon` area (Green's theorem + circular-segment correction) | #64 | `ArcArea.v` (`segment_area`); oracle `ARC_AREA_INVARIANTS_EXACT` / `ARC_AREA` / `RING_ORIENTATION` (signed area) | ✅ exact rational invariants; float area interface-boundary |
| **M-DIM** | Dimension of curve geometries | TRIAGE park | — | ⬜ research park (no statement; `docs/scout/69-closing-summary.md`) |
| **V-CP / V-CS** | Arc-aware validity (arc self-intersection, orientation via sector area, holes-in-shell) | #64 | `CurveRingSimple.v` (`curve_ring_not_simple_of_witness`), `CurvePolygonSimple.v`, `CurvePolygonValid.v`, `CurvePolygonOrientation.v`, `CurvePolygonDisjoint.v`, `InCircle_b64_exact.v`, **`CurveRingOffsetSimple.v`** (`curve_ring_simple_of_clearance`), **`WindingNumber.v`** (`winding_decides_membership`), **`CircularStringValid.v`** (`circularstring_abca_valid` — historical V-CS pin, JTS `2b56b1a4`); **`CircularStringOddCount.v`** (`circularstring_abca_postgis_invalid` — EX-CS-4, JTS `81c2e996`, PostGIS odd ≥ 3, closed-4 rejected); oracle `RING_SIMPLE` / `POINT_IN_CURVE_RING` / `RING_ORIENTATION` / `HOLES_DISJOINT` | 🟡 in-circle sign ✅ (full-plane, 3-ax) + per-ring witness-soundness ✅ + **control-count annulus pin ✅ (2026-08-23, even leftover first≠last invalid, odd ≥ 3 unchanged)**; **offset-ring simplicity now POSITIVELY certified under a clearance hypothesis (2026-06-30), and a Z-valued winding number decides point-in-ring (`Z.odd ∘ winding_number` ⟺ `point_in_ring`)**; completeness + unconditional true-region (Jordan / {-1,0,+1} winding) deferred |
| **D-PT** | Analytical point-to-arc distance | #64 | `ArcDistance.v`, `ArcPointDistance.v`; oracle `ARC_DISTANCE` | 🟡 radial-foot core ✅; on-arc/sweep clamp deferred |
| **D-AA** | Arc-arc distance | #64 | `ArcArcDistance.v`, `ArcIntersect.v` (predicate); oracle `ARC_ARC_DISTANCE` | 🟡 disjoint circle-to-circle core ✅; sweep clamp deferred |
| **D-SL** | Arc-segment distance | #64 | `ArcSegmentDistance.v`; oracle `ARC_SEGMENT_DISTANCE` | 🟡 line-outside-circle core ✅; sweep/segment clamp deferred |
| **C-\*** | Centroid of curve geometries | #64 | `ArcCentroid.v` (`ArcCentroid.v : arc_centroid_offset_semicircle`); `ArcAreaCentroid.v`; oracle `ARC_CENTROID` / `ARC_AREA_CENTROID` | 🟡 offset spec proven (exact invariants); centroid POINT is interface-boundary (transcendental) |
| **H-\*** | Hulls over curve inputs | **#424** (`topic: hull`; JTS#1160 MBT / JTS #8 · #41 H-CV) | `Convex.v` (linear); `MinimumBoundingTriangle.v` (424-a); **`HullExactExtrema.v` (424-b, disc + single-arc cardinals)** | 🟡 424-a MBT + 424-b H-CV extrema Qed; H-CC CompoundCurve leftover (JTS #6) |
| **S-\*** | Simplification of curves | TRIAGE park · NTS#429 | `Simplify.v` (`Simplify.v : simp_star_perp_length_monotone`); `Linearise.v`; oracle `CP_BOUNDARY_SIMPLIFY` (extracted simplifier ∘ densify, `oracle/curve_polygon.py`) | 🟡 structural greedy-perp; simplification-preserves-curve soundness open (technique park; no epic from the #69 letter) |
| **AT-\*** | Affine transforms (non-similarity → detect-and-densify, §7 risk) | TRIAGE park | — | ⬜ research park (no statement; `docs/scout/69-closing-summary.md`) |
| **LRF-\*** | Linear referencing on curves | TRIAGE park | — | ⬜ research park (no statement; `docs/scout/69-closing-summary.md`) |
| **DSF** | Densifier (curve → chords internally) | #64, #65 | `ArcChordApprox.v` (sagitta bound), `ArcChord{Density,Subdivision,Length,Sound}.v`, `CurveLinearise.v` (`chord_approx_ring_closed`); oracle `CP_BOUNDARY_SIMPLIFY` densify (`densify_arc`) | ✅ chord-approx faithfulness (closure); sagitta/`ring_simple` open |
| **BUF-1 / BUF-N** | Single-/multi-arc buffer → `CurvePolygon` | #65 | 18× `Buffer*.v` (linear), `ExtractBufferRings.v`; `CurveBufferArea.v`, `CurveRingOffset.v`, `CurveOffsetAssembly{,Total}.v`, `CurveRoundJoin.v`, **`ClothoidBufferBridge.v`, `ClothoidOffsetContact.v`, `ClothoidBufferAssembly.v`, `CurveRingOffsetSimple.v`** (clothoid chain); oracle `BUFFER_REGION` (+ `ARC_BUFFER_SIMPLE/FULL` pins); **oracle pilot for unified segments + NTS sketch (2026-06)** | 🟡 arc buffer-region boundary+area cert ✅ (3-ax) + d=0 + helpers; **clothoid buffer-ring chain ✅ (2026-06-30): validity → adjacent offset contact → whole-ring assembly cleanliness → non-adjacent simplicity under clearance > 2·\|d\| = simple-closed-curve cert**; oracle pilot + dispatcher sketch for Arc/CS/CC/CP; pure-linear regression zero; Minkowski + unconditional simplicity deferred. |
| **OFF** | Offset curve (arc-preserving) | #65 | `BufferOffset.v`, `ArcOffset.v`, `ArcOffsetThreePoint.v` (`arc_offset_preserves_arc`), `CurvePolygonOffset.v`, `CurveRingOffset.v`, `ClothoidBufferBridge.v` (`clothoid_ring_offset_valid` + sharpness), `ClothoidOffsetContact.v`, `ClothoidBufferAssembly.v`, `CurveRingOffsetSimple.v`; oracle `ARC_OFFSET_XY` | 🟡 arc offset ✅ (valid arc → valid arc, radius r+d); **clothoid ring offset now soundness-complete at the adjacency level + non-adjacent simplicity gated on a clearance hypothesis (2026-06-30)** |
| **VBF** | Variable-distance buffer | #65 | — | ⬜ |
| **N-AL** | Arc-line noding / intersection | #64 | `theories-flocq/ArcLineIntersect_b64_exact.v` (Scope A), `ArcSegmentCircles.v` (`line_circle_radical_point`), `ArcIntersect.v`, `ArcIntersectIVT.v`; oracle `ARC_SEGMENT_XY` / `ARC_LINE_XY` | 🟡 Scope A (pre-division) ✅ + existence ✅; coordinate identity (Scope B/C) queued |
| **N-AA** | Arc-arc noding / intersection | #64 | `ArcArcCircles.v`, `ArcArcSound.v`, `ArcIntersect.v` (`arc_arc_intersects` predicate); `CircleCircleResultant.v : radical_points_satisfy_circle_circle_res` (constructor ⇒ affine resultant root, claimId `64-naa-res`); `CircularCookZ.v : I_circles_z` (integer discriminant + hen mint, claimId `64-circ-z-partition`); `CircularCookHit.v : ticket_64_circ_hit_params_qed_or_qex` (full-circle `γ` + `(tᵢ, tⱼ)`, claimId `64-circ-hit-params`); `CircularCookSpan.v : circular_arc_gamma_constructed` / `CircularCookSpan.v : locked_span_gamma_hit` (span-restricted `γ` on CircularArc, claimId `64-circ-span-gamma`); `CircularCookSplit.v : ticket_0007_circ_cook_step_qed_or_qex` (circular Hit → sidecar `split(t)` cook, claimId `0007`); `CircularCookSplit.v : ticket_0007_circ_mint_two_qed_or_qex` (I.7 MintTwo / `p−` second Hit, claimId `0007`); `CircularCookSplit.v : ticket_0007_i1_fence_qed_or_qex` (I.1 four-object fence, claimId `0007`); `CircularCookHit.v : ticket_0007_i2_hit_sound_qed_or_qex` (I.2 ∀ Hit soundness, claimId `0007`); `CircularCookEmpty.v : ticket_0007_i3_empty_qed_or_qex` (I.3 ∀ Empty / Decline, claimId `0007`); `CircularCookConfluence.v : ticket_0007_i8_confluent_qed_or_qex` (I.8 leftover confluence, claimId `0007`); `CircularCookLicense.v : ticket_0007_i9_tags_qed_or_qex` (I.9 classifier ≠ cook, claimId `0007`); `CircularCookClose.v : ticket_0007_i10_sidecar_qed_or_qex` (I.10 Campaign-I close, claimId `0007`); `CircularCookSpanFilter.v : ticket_0007_ii1_hit_qed_or_qex` (II.1 span filter as IResult, claimId `0007`); `CircularCookSpanSplit.v : ticket_0007_ii2_meet_qed_or_qex` (II.2 split γ_span at in-span t, claimId `0007`); `CircularCookOkCirc.v : ticket_0007_ii3_hit_qed_or_qex` (II.3 I_ok_circ on circular eggs, claimId `0007`); `CircularCookCloseII.v : ticket_0007_ii4_inhabitant_qed_or_qex` (II.4 Campaign-II close, claimId `0007`); `CircularCookCsConcat.v : ticket_0007_b1_joint_qed_or_qex` (Phase B.1 CircularString concat joints, claimId `0007`); oracle `ARC_ARC_XY` / `I_CIRCULAR` | 🟡 circles-intersect (Stage B) ✅; constructor ⇒ resultant root ✅; Z classifier partition iff + internal kiss ✅; full-circle locked Hit `(h*, p*, tᵢ, tⱼ)` ✅; span-restricted CircularArc `γ` ✅ (4-axiom sidecar); circular Hit sidecar cook ✅ (host `try_cook_hit` still QEX); I.7 MintTwo / `p−` ✅ (Empty/Decline/Touch still QEX); I.1 fence ✅ (`I_circles_z` ≠ `I_circles_gamma` ≠ sidecar cook ≠ `I_gloss`; Touch ≠ IHit; circular Empty ≠ Decline; chord × circular Decline in `I_ok`); I.2 ∀ Hit soundness ✅ (`I_circles_gamma` Hit iff proper disc ∧ `on_full_circle` both roots; γ_full, not arc membership); I.3 ∀ Empty / Decline ✅ (Empty iff proper ∧ γ_full images disjoint; Decline iff `d=0` or `r≤0`; discriminant ≠ image-disjoint); I.8 leftover confluence ✅ (`leftovers_ab` = `leftovers_ba` on γ_full; not the bag loop); I.9 classifier ≠ cook ✅ (`I_circles_z` / `I_CIRCULAR` Hit is tags 0/1, not `(p*, tᵢ, tⱼ)`; ⇏ host `try_cook_hit` / `circ_split` / first-cook expansion); I.10 Campaign-I close ✅ (sidecar cook on both roots; host CircGamma QEX; first cook chord–chord; `I_CIRCULAR` stays a classifier; #666 fence holds; Campaign II / H⊥ named parked at that close; no new kernel; not SQL/MM done); II.1 span filter as IResult ✅ (arc Hit iff `on_arc_gamma` both; locked `p+` Hit, `p−` Empty; γ_full ≠ span; host CircGamma QEX; II.2–II.4 / H⊥ / SQL/MM cathedral parked); II.2 split γ_span at in-span t ✅ (leftovers of `arc_gamma` meet at locked `p+`; leftover on parent circle; `p−` stays Empty / no invented span cook; host CircGamma QEX; II.3–II.4 / H⊥ / SQL/MM cathedral parked); II.3 I_ok_circ ✅ (first glossary-type inhabitant on EggCircularArc × EggCircularArc; locked `p+` Hit licenses `span_split`; locked far pair inhabits Empty; host CircGamma QEX; `I_ok_circ` Hit ≠ host `I_ok`; II.4 / H⊥ / SQL/MM cathedral parked); II.4 Campaign-II close ✅ (`CircularCookCloseII.v : ticket_0007_ii4_inhabitant_qed_or_qex`; sidecar `I_ok_circ` inhabitant; leftover meet is ¬Empty `CircularCookCloseII.v : ticket_0007_ii4_not_kiss_qed_or_qex`; host CircGamma QEX `CircularCookCloseII.v : ticket_0007_ii4_host_qed_or_qex`; Phase B CS / CC / CP gaps named; bag loop stays obligation; H⊥ parked; not SQL/MM done `CircularCookCloseII.v : ticket_0007_ii4_phase_b_qed_or_qex`); Phase B.1 CircularString concat joints ✅ (`CircularCookCsConcat.v : ticket_0007_b1_joint_qed_or_qex`; ∀ CS joint is `I_ok_circ` Hit at `(end, 1, 0)`; locked 2-arc contiguous `CircularCookCsConcat.v : ticket_0007_b1_not_interior_qed_or_qex`; reuse `I_ok_circ` `CircularCookCsConcat.v : ticket_0007_b1_reuse_qed_or_qex`; host CircGamma QEX `CircularCookCsConcat.v : ticket_0007_b1_host_qed_or_qex`; CompoundCurve / CurvePolygon / H⊥ parked; not SQL/MM done `CircularCookCsConcat.v : ticket_0007_b1_park_qed_or_qex`); host `CircularCook.v : ticket_64_circ_gamma_qed_or_qex` QEX (atan2-free interpolant remaining) |
| **N-SS** | `SegmentString` / `Noder` for curves | #66 | `SnapRounding_b64.v`, `HotPixel*`; oracle `CURVE_SNAP_DECISION` | 🟡 linear noding ✅; curve-snap decision oracle ✅ |
| **PRC-SN** | `PrecisionModel.makePrecise` on curves | #66 | oracle `CURVE_SNAP_DECISION` / `CURVE_SNAP_INVARIANTS_EXACT` (exact-`Q`) | ✅ curve-snap grid-friendliness |
| **OV** | Arc-preserving overlay output | #66, #64 | `Overlay*.v`, `OverlayCorrectness.v`, `ArcOverlay.v` | 🟡 conditional headline (`arc_overlay_correct_chord_approx`, 2 bridge hyps) |
| **R-\* (R-CONT, R-PR)** | Predicates / relate on curved inputs | #67 | `DE9IM.v`, `RelateLineLine.v`, `RelateAreaPoint.v`, `RelateBoundary.v`, `RelateAreaLine.v`, `RelateAreaArea.v`, `RelateArcChord.v`, `RelateArcAnalytic.v`, `RelateClothoid.v`, `RelateEllipticArc.v`, `RelateBezier3.v`, `RelateCurveAreaPoint.v`, `RelateMatrix*.v`, `RelateCurveMatrix.v`, `RelatePreparedCache*.v`, `RelateNodingLineLine.v`, **`RelateNodingLineLineExtPinned.v` (67-c)**; oracle `CURVE_RELATE_MATRIX` / `RELATE_MATRIX` / `RELATE_PREDICATE` | 🟡 matrix algebra + witnesses ✅ (S0–S12); prepared-cache refinement ✅ (S13–S14b); **line×line noding pipeline partial** ✅ through S15k + 67-c exterior-row pin; cell-**dimension** (Jordan/overlay) + S15l+ hooks deferred |
| **PLG** | Polygonizer accepting `CompoundCurve` edges | #66 | `RingExtract.v` / overlay ring assembly; `PermCycleSplice.v`, `NumFacesSplice.v`, `EulerBridge.v` | 🟢 linear `extract_rings_valid` is a conditional-Qed; its former named seam `EdgeFaceBridge.H_bridge_core` (planar same-face ⇒ bridge) is now fully DISCHARGED — carried as the named premise `H_bridge_premise`, now a THEOREM of the five geometric/noding guards (`WalkResidualDischarge.H_bridge_premise_holds`, Euler-free; the planar Euler identity itself is unconditional via `EulerUnconditional.euler_characteristic_holds`). This PLG/ring-assembly deferral is itself discharged; the deferred-proof registry is now **empty** — its last residual (`arc_dot_max_at_endpoint`, `ArcSinglePeak.v`) was discharged 2026-07-01 (`check_admitted.sh`: 0 = 0 counterexample + 0 deferred; the finding-7 `ArcPointDistance.v` sweep-clamp residuals were discharged before it); ring extraction is guard-conditional only (`extract_rings_valid_of_guards` + `extract_rings_valid_holes_of_guards`, PRs #334–#372) |
| **TRI-DT** | Delaunay on (densified) curved boundaries | #68 | `theories-flocq/InCircle_b64_exact.v` (primitive), `DelaunayEmptyCircle.v`, `DelaunayFlipWitness.v`, `DelaunayFlipGeometric.v`, `DelaunayEdgeEmptyCircle.v` (68-a), `DelaunayLocallyDelaunay.v` (68-b), `Triangle.v`, `Tin.v` | 🟡 in-circle primitive ✅ + empty-circle predicate ✅ + flip sign algebra ✅ + edge ↔ empty-circle (weak skeleton) ✅ + **local Delaunay / flip-refutes-both ✅**; geometric insert / full covering DT + curved densification planned |
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
| JTS#1195 — Curve Awareness EPIC | #64, #65, #66, #68 | Open — primary driver (tracker #69 owner-retire ready) |
| JTS#1175 — RelateNG.computeLineEnds() skips boundary points | #64, #66, #67 | **Fixed (jts#1200)** — struck through in #64/#66/#67 |
| JTS#979 — buffer with fixed precision removes hole | #64, #65, #66 | Open — backed by `RingArea979.v` |
| JTS#96 — incorrect results with fixed-precision buffer | #65, #66 | Open — sibling of JTS#979 (fixed-precision buffer soundness); new driver, 2026-06-20 scan |
| JTS#752 — TopologyException in UnaryUnionNG (floating precision) | #66 | Open — **NOT explained by the asymmetry lane** (correction 2026-06-17): JTS's `HotPixel.intersectsScaled` canonicalizes to +X before testing, so it is reversal-symmetric by construction; `PassesThrough_b64_compute_asymmetric.v` models a Liang-Barsky divide-from-c0 filter JTS does not use. Root unidentified here. |
| JTS#1133 — snapRoundingNoder on polygons returns MultiLineString | #66 | **Open** — 2026-06-20 verify: reclassified `type-bug` → `type-question` (why it left the bug scan), **not** resolved. Same correction: asymmetry lane does not map (JTS canonicalizes endpoints) |
| JTS#1106 — orientation robustness summary | #64, #66 | Open — `Orient_b64_exact*` is the ground-truth spec |
| JTS#750 — Orientation.Index problem with COLLINEARity | #66, #67 | Open — companion to JTS#1106; `Orient_b64_exact*` collinear (`cross = 0`) sign is the ground-truth spec; new driver, 2026-06-20 scan |
| JTS#163 — increase spatial-predicate accuracy via better DD conversion | #66, #67 | Open — relate/predicate robustness substrate (DE-9IM #67); new driver, 2026-06-20 scan |
| JTS#1147, #739, #1028, #178, #180, #592, #866, #876, #908, #1102, #1183 — buffer/offset quality | #64, #65 | Open — "summary of failures" refs need re-check vs current JTS. 2026-06-20 scan: #739, #1028, #178, #180, #592, #876, #908, #1102, #1183 confirmed open `type-bug`; #1147 ("Unexpected `OffsetCurve.getCurve()` output since jts 1.20.0" — offset regression, relevant to NTS#815) & #866 ("Buffer unexpected boundary artifacts") **open, reclassified `type-bug` → `type-question`** |
| JTS#1000 — OverlayNG failures summary | #64, #66, #67 | Open |
| JTS#865 — OverlayNG intersection rotates vertices | #64, #66 | Open |
| JTS#1122 — CoverageValidator misses gap if tolerance too large | #64, #66, #67 | Open |
| JTS#1190, #1138, #1039, #20 — Delaunay/Voronoi robustness | #68 | Open — 2026-06-20 scan: #1138, #1039, #20 confirmed open `type-bug`; #1190 ("ConformingDelaunayTriangulationBuilder poor triangulation", last activity 2026-04-13) **open, reclassified `type-bug` → `type-question`** |
| NTS#828 — align epic | #64 (historical tracker #69) | Open |
| NTS#815 — OffsetCurve miter for polygonal (JTS#1109) | #64, #65 | Open — port target |
| NTS#819 — RelateNG cache for prepared A-L (JTS#1099) | #67 | Open (perf); **proof companion partial (S13–S14b)** — `RelatePreparedCache*.v` |
| NTS#247, #570 — curves / GML curves | #64 | Open — old but relevant |
| NTS#719, #638 — GeometryPrecisionReducer / buffer holes | #66 | Open — both confirmed open `bug` (2026-06-20 scan) |
| NTS#429 — Simplification and topology | TRIAGE park (S-*) | Open (`bug`) — `Simplify.v : simp_star_perp_length_monotone`; the deferred *simplification-preserves-topology / curve* soundness frontier; new driver, 2026-06-20 scan |
| NTS#780 — InputLines not set when calling RobustLineIntersector | #66, #67 | Open (`bug`) — port/API surface on the `RobustLineIntersector` differential-test path (Phase 0/1 oracle); note, 2026-06-20 scan |

## Wire map — upstream → Proofs epic + topic

> **Macro routing table** for PR machine headers (`topic:`) and blast-cone
> epicenters. One upstream issue maps to **one primary** Proofs epic; secondary
> touch is allowed in prose but the wire is the default home.
>
> Last authored **2026-08-03** from the board wire list (JTS + NTS).

| Upstream | Proofs epic | `topic:` | Notes |
|---|---|---|---|
| [locationtech/jts#1191](https://github.com/locationtech/jts/issues/1191) | [#410](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/issues/410) | `koc` | Compound-curve / Koc railway alignment cluster |
| [locationtech/jts#1195](https://github.com/locationtech/jts/issues/1195) | [#64](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/issues/64) | `core` | Curve Awareness EPIC — arc primitives / structural core (tracker #69 owner-retire ready; index is this table) |
| [locationtech/jts#1190](https://github.com/locationtech/jts/issues/1190) | [#68](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/issues/68) | `mesh` | Conforming Delaunay / triangulation quality |
| [locationtech/jts#1169](https://github.com/locationtech/jts/issues/1169) | [#1200](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/issues/1200) | `core` | Primary core epic for this driver (open/create board issue if missing) |
| [locationtech/jts#1000](https://github.com/locationtech/jts/issues/1000) | [#66](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/issues/66) | `precision` | OverlayNG failures summary |
| [locationtech/jts#1183](https://github.com/locationtech/jts/issues/1183) | [#65](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/issues/65) | `buffer` | Buffer / offset quality |
| [locationtech/jts#1102](https://github.com/locationtech/jts/issues/1102) | [#65](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/issues/65) | `buffer` | Buffer quality |
| [locationtech/jts#1181](https://github.com/locationtech/jts/issues/1181) | [#814](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/issues/814) | `core` | Shared core epic with NTS#814 |
| [locationtech/jts#1180](https://github.com/locationtech/jts/issues/1180) | [#65](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/issues/65) | `buffer` | Buffer / offset |
| [locationtech/jts#1153](https://github.com/locationtech/jts/issues/1153) | [#64](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/issues/64) | `core` | Arc / curve-core adjacent |
| [locationtech/jts#1039](https://github.com/locationtech/jts/issues/1039) | [#68](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/issues/68) | `mesh` | Delaunay / mesh robustness |
| [NetTopologySuite/NetTopologySuite#851](https://github.com/NetTopologySuite/NetTopologySuite/issues/851) | [#65](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/issues/65) | `buffer` | Buffer / offset |
| [NetTopologySuite/NetTopologySuite#844](https://github.com/NetTopologySuite/NetTopologySuite/issues/844) | [#66](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/issues/66) | `precision` | Precision / snap / overlay |
| [NetTopologySuite/NetTopologySuite#819](https://github.com/NetTopologySuite/NetTopologySuite/issues/819) | [#67](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/issues/67) | `relate` | RelateNG prepared / A-L cache |
| [NetTopologySuite/NetTopologySuite#818](https://github.com/NetTopologySuite/NetTopologySuite/issues/818) | [#64](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/issues/64) | `core` | SQL-MM align surface (historical tracker #69; `OracleCurveChecklist.v : w1_w5_coverage_table_complete`) |
| [NetTopologySuite/NetTopologySuite#817](https://github.com/NetTopologySuite/NetTopologySuite/issues/817) | [#64](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/issues/64) | `core` | Arc / curve-core |
| [NetTopologySuite/NetTopologySuite#815](https://github.com/NetTopologySuite/NetTopologySuite/issues/815) | [#64](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/issues/64) | `core` | OffsetCurve miter track → arc/core companion (buffer detail still #65) |
| [NetTopologySuite/NetTopologySuite#814](https://github.com/NetTopologySuite/NetTopologySuite/issues/814) | [#814](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/issues/814) | `core` | 1:1 NTS → Proofs mirror epic |
| [NetTopologySuite/NetTopologySuite#813](https://github.com/NetTopologySuite/NetTopologySuite/issues/813) | [#68](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/issues/68) | `mesh` | Mesh / triangulation |
| [NetTopologySuite/NetTopologySuite#812](https://github.com/NetTopologySuite/NetTopologySuite/issues/812) | [#423](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/issues/423) | `metric` | Directed Hausdorff port still open. Grill: [`docs/scout/map-hausdorff-functions.md`](docs/scout/map-hausdorff-functions.md). Spec: [`docs/scout/spec-hausdorff-functions.md`](docs/scout/spec-hausdorff-functions.md). Notion tickets `NTS-812` / `GEOS-DHD`. Discrete + oriented discrete already on NTS develop; locus class is not |
| [NetTopologySuite/NetTopologySuite#810](https://github.com/NetTopologySuite/NetTopologySuite/issues/810) | [#425](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/issues/425) | `coverage` | Coverage cleaner / gap-overlap |

### Topic palette (macro)

| `topic:` | Primary epics | Domain |
|---|---|---|
| `core` | #64, #814, #1200 | Arc primitives, SQL/MM structure, shared core |
| `buffer` | #65 | Buffer / offset / clothoid rings |
| `precision` | #66 | Snap-rounding, OverlayNG, precision models |
| `relate` | #67 | DE-9IM / RelateNG / prepared (67-a matrix · 67-b boundary · 67-c exterior-row pin) |
| `mesh` | #68 | Delaunay / Voronoi / local DT |
| `koc` | #410 | Koc compound-curve alignment |
| `metric` | #423 | Distance / Hausdorff / Frechet cluster. Engine surface: [`docs/scout/map-hausdorff-functions.md`](docs/scout/map-hausdorff-functions.md) |
| `coverage` | #425 | Coverage validation / cleaning |
| `hull` | #424 | Convex / minimum bounding hulls (424-a MBT · 424-b H-CV extrema) |

### Proposed new epics (paper ∪ major group)

| `topic:` | Proposal | Upstream / paper | Proofs home today | Action |
|---|---|---|---|---|
| **`hull`** | Port **MinimumBoundingTriangle** from JTS 1.21 + curve H-CV extrema | [locationtech/jts#1160](https://github.com/locationtech/jts/issues/1160); JTS #8 / #41 | Epic **#424** open. 424-a MBT + 424-b H-CV extrema (`HullExactExtrema.v`) on `_CoqProject`. H-CC CompoundCurve leftover | Keep #424; next hull rung is H-CC / constructive scan, not a remint of 424-b |

PR body template once wired:

```text
topic: hull
claimId: <micro>
witness: <fixture or none>
```

## Cross-cutting findings

1. **This file exists and is the source of record.** Cited by every batch issue;
   created 2026-06-08, refreshed 2026-06-09. Per-area detail now lives in the
   sibling docs `docs/issue-64-arc-primitives-triage.md` and
   `docs/relate-ng-status.md` (the historical umbrella/detail split;
   the pre-#530 RelateNG triage is archived).
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
8. **Reconcile 2026-06-30 — the clothoid buffer-soundness + winding-number wave
   (#65, with #66/#67 PIP spillover).** `origin/main` took PRs #302–#307, all
   3-axiom (classical-reals trio) and Qed: **(#302/#303)** `ClothoidBufferBridge.v`
   — `clothoid_ring_offset_valid` (a curvature-bounded clothoid arc-ring offsets to
   a valid ring when `d > −1/κ_max`) + `clothoid_offset_below_min_radius_fails`
   sharpness; **(#304)** `ClothoidOffsetContact.v` — `internally_tangent_circles_unique`
   (reusable nra-free engine) + `clothoid_clothoid_offset_contact_sound` (two
   adjacent G¹-joined offset osculating arcs meet ONLY at their shared join);
   **(#305)** `ClothoidBufferAssembly.v` — `clothoid_buffer_assembly_sound` lifts
   that pairwise fact to the whole closed ring (every interior + wrap join is a
   single clean contact); **(#306)** `CurveRingOffsetSimple.v` —
   `curve_ring_simple_of_clearance` (non-adjacent offset segments meet NOWHERE
   when source clearance `> 2·|d|`, a metric tube argument covering chords AND
   arcs). Together: a **simple-closed-curve certificate for well-separated clothoid
   buffer rings.** **(#307)** `WindingNumber.v` resolves the long-deferred
   `PointInRingCorrect.v §5` winding-number seam without `atan2`: the signed
   ray-crossing count (Sunday's algorithm) is `Z`-valued, and
   `winding_decides_membership` proves `Z.odd (winding_number p r) = true ↔
   point_in_ring p r` (reusing `point_in_ring_eq_parity`) — a verified
   winding-number point-in-ring decider. **Trust footprint unchanged:** the
   classical-reals trio holds; `scripts/check_admitted.sh` reports **0 total
   (0 counterexample + 0 deferred-proof)** — the last residual obligation
   `arc_dot_max_at_endpoint` (`ArcSinglePeak.v` §2, a planar single-peak dot bound)
   was discharged 2026-07-01 via its chord-frame reduction (no `psatz`/CSDP needed;
   the earlier D-PT `ArcPointDistance` sweep-clamp residuals of finding 7 were
   discharged before it); the oracle hand-roll ratchet is at **28**
   frozen kernels. Deferred
   frontier: Minkowski buffer-area soundness, and the `{−1,0,+1}` winding
   characterisation for SIMPLE polygons (unconditional Jordan simplicity — the
   genuine global-geometry rung that #306's clearance hypothesis and #307's parity
   decider now sit beneath).

## Recommended order of attack (revised 2026-08-16)

1. **#67** — still the deepest *unfinished* build, but now well advanced: matrix
   algebra + witnesses (S0–S12), curve DE-9IM oracle (CURVE_RELATE_MATRIX),
   prepared-cache refinement (S13–S14b), and **line×line RelateNG noding through
   S15k** (`RelateNodingLineLine.v` collection capstone). **67-c / S15l line×line
   exterior-row true-dimension pinning** landed (`RelateNodingLineLineExtPinned.v`).
   Remaining **S15l+**: prepared evaluate hook, Touches fill split, global
   cell-**dimension** (Jordan/overlay) soundness, and multi-geometry pipeline
   beyond line×line. (Recent rungs: general-triangle Jordan cell-dim soundness,
   direct right-triangle `hole_inside_outer`, RelateNG/Prepared pipeline skeleton
   + rects_relate, line×line exterior-row pin.)
2. **#64** — finish ask #5a Scope B/C (arc-line coordinate **identity** + forward
   error) and the quartic arc-arc coordinates; the sign/length/area/distance and
   intersection-**existence** foundation is now done.
3. **#65** — close the geometric "signed area = true Minkowski buffer area" gap
   above the landed BUFFER_REGION certificate.
4. **#66** — finish remaining precision/overlay gaps (mostly there).
5. **#68** — Delaunay / Voronoi on top of the now-proven `inCircle_R`.
6. **#423** — Formal proofs for distance metrics: directed/discrete Hausdorff
   and Fréchet correctness (`metric`). `423-a` / `423-b` Green. Remaining
   Proofs asks stay the two ticket-10 lines (densification bound;
   `HAUSDORFF_DIRECTED` / `HAUSDORFF_SYMM`). JTS locus class is unported
   on NTS develop (NTS#812). Engine grill:
   [`docs/scout/map-hausdorff-functions.md`](docs/scout/map-hausdorff-functions.md).
7. **#424** — Formal proofs for hull constructions: minimum bounding triangle,
   convex hull, enclosing-shape invariants (`hull`).
8. **#425** — Formal proofs for polygonal coverage: validity, gap/overlap
   cleaning, and union soundness (`coverage`; Coverage cleaner / gap-overlap).

The curve-awareness attack does **not** include an oracle-gate / CURVEPOLYGON type-I/O /
RocqRefRunner-first-for-CP step. That is not a leftover implement.
CURVEPOLYGON (ISO/IEC 13249-3, WKB 10) is JTS I/O identity on JTS #7 via #51,
not an oracle keyword; no Proofs issue is closed as done on JTS #7.

## How to cite the corpus

When referencing proven results: lead with `[exact]` rows from
`docs/verified-claims.md`, present `[cond]` rows as "conditional headline"
(never as solved), and offer the matching `[oracle]` mode to reproduce a
concrete case. Qed-closure is enforced corpus-wide by
`scripts/check_admitted.sh`; claim citations are checked by
`scripts/validate-claims.sh` on every CI run.
