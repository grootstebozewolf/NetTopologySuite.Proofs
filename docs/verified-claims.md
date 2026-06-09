# Verified Claims — NetTopologySuite.Proofs

> **Living, CI-verified document.** Every theorem cited below (in
> `<module> : <name>` form) is cross-checked against the source by
> [`scripts/validate-claims.sh`](../scripts/validate-claims.sh) on each CI run;
> a renamed or removed theorem orphans its claim and fails the build. (Qed-
> closure itself is enforced corpus-wide by `scripts/check_admitted.sh`.)

Citable index of what is actually proved (Rocq 9.1.1; Flocq 4.2.2 for the
binary64 layer). Each row: `file : theorem`, plain meaning, axiom footprint,
regime. These are *soundness* statements, not a verified re-implementation.

**Regimes.** `[exact]` exact reals · `[int-b64]` integer-coordinate binary64
(`|coord| ≤ 2²⁵`) · `[int-b64-arc]` integer-coordinate binary64 for the
degree-4 `b64_inCircle` chain (`|coord| ≤ 2¹¹`, tighter than orient2d) ·
`[full-b64]` *all* finite binary64 (exact, no magnitude limit) · `[cond]`
holds under named hypotheses · `[oracle]` extracted, differential-testable
against the C# port.

**Axioms.** `theories/` uses 3 classical-reals axioms (`sig_not_dec`,
`sig_forall_dec`, `functional_extensionality_dep`); `theories-flocq/` adds
`Classical_Prop.classic` from Flocq (the "4" below). Every theorem is `Qed`;
CI rejects unregistered `Admitted`. Full README: [../README.md](../README.md).

When citing: lead with `[exact]` rows; present `[cond]` rows as "conditional
headline", never as solved; offer the oracle to reproduce a concrete case.

---

## Phase 0 — Robust orientation (CCW / `Orientation.Index`)

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `Orientation.v : cross_antisymmetric` | Swapping two points flips the sign `[exact]` | 3 |
| `Orientation.v : cross_cyclic` | Cyclic rotation preserves the sign `[exact]` | 3 |
| `Orientation.v : cross_translation_invariant` | Translation preserves orientation `[exact]` | 3 |
| `Orientation.v : cross_at_P0_is_collinear` (+`_P1`,`_degenerate_base`) | Coincident points ⇒ sign 0 `[exact]` | 3 |
| `Orient_b64_exact.v : b64_orient2d_exact_for_small_int` | binary64 determinant = exact cross on integer coords `[int-b64]` | 4 |
| `Orient_b64_exact.v : b64_orient_sign_filtered_sound_small_int` | Filtered (fast) predicate's Pos/Neg/Zero agree with the true sign on integer coords `[int-b64]` | 4 |
| `Orient_b64_exact_full.v : b64_orient2d_exact_sound` | **Full-plane headline.** The *exact* predicate's Pos/Neg/Zero agree with the true orientation sign for **all finite binary64** — no `\|coord\| ≤ 2²⁵` limit `[full-b64]` | 3 |

`[oracle]` `RobustOrientation` bit-exact vs `ORIENT`/`ORIENT_FILTERED`;
`ORIENT_EXACT` is the exact full-plane reference (mirrors `b64_orient2d_exact`).

**Exact predicate — full plane, 3 axioms.** `b64_orient2d_exact` is proven
sound over the *entire* binary64 plane (every finite double is a dyadic
`m·2ᵉ`; the determinant sign is computed exactly in `ℤ`). Unusually for
`theories-flocq/`, it stays at **3 axioms** (no `Classical_Prop.classic`) —
it uses only the `B2R` decode + exact `ℤ` arithmetic, no float ops.

**Still open / honest scope.** The *fast* Shewchuk-adaptive filter
(`b64_orient_sign_filtered`) is proven only on integer coords (Stage A); its
general bounded-magnitude soundness (Stages B–D) remains a registered
deferred proof. And JTS/NTS double-double `Orientation.index` is **not**
proven sound — the exact predicate is the ground-truth spec it should be
diffed against (JTS #1106).

## Relate / DE-9IM integer-coordinate substrate (#67)

Grounds the integer-arithmetic overflow-safety of the Romanschek, Clemen &
Huhnt (ISPRS IJGI 2021, 10, 715) robust DE-9IM approach (§3.2). Pure `ℤ`,
**0 axioms** (every theorem *Closed under the global context* — fewer than the
3-axiom `[exact]` reals rows). `[int]` = exact integer coordinates, bounded
window.

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `RelateIntDetBound.v : idet_abs_le_2sq` | Orientation determinant on coords in `[0,c]` satisfies `\|idet\| ≤ 2c²` (conservative algebraic bound) `[int]` | 0 |
| `RelateIntDetBound.v : idet_fits_int64_for_int32_coords` | 32-bit integer coords ⇒ determinant fits a signed 64-bit integer (`2·(2³¹−1)² ≤ 2⁶³−1`) — the paper's "32 bit integers can be used for the coordinates" `[int]` | 0 |
| `RelateIntDetBound.v : cmax_sq_le_int64` (+`cmax_succ_sq_gt_int64`) | `cmax = 3 037 000 499 = ⌊√(2⁶³−1)⌋` pinned exactly (the paper's tight 64-bit window, Eq 5/8) `[int]` | 0 |
| `RelateIntDetBound.v : idet_max_witness` (+`idet_min_witness`) | Triangles realize `±cmax²` ⇒ the determinant range `[−cmax², cmax²]` is tight `[int]` | 0 |

**Honest scope.** The universal *geometric* bound `\|idet\| ≤ c²` (Eq 4 — the
half-box-area fact that would license the full `[0, cmax]` window) is deferred;
what is closed is the conservative `2c²` bound (sufficient for the 32-bit
regime), the exact `cmax` bracketing, and the `±cmax²` tightness witnesses.

## Phase 1 — Robust segment intersection (`RobustLineIntersector`)

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `Intersect.v : segments_share_point_implies_opposite_sides` | Shared point ⇒ neither line strictly separates the other `[exact]` | 3 |
| `Intersect.v : same_side_rejection_is_sound` | **Rejection is sound:** a "no intersection" verdict never drops a real crossing `[exact]` | 3 |
| `Intersect.v : strict_completeness` | Strict opposite-sides both tests ⇒ interior crossing exists `[exact]` | 3 |
| `Intersect.v : collinear_share_iff_1d_overlap` | **Collinear case (new):** sharing a point ⇔ 1-D extents overlap `[exact]` | 3 |
| `Segment.v : between_of_on_line_and_coord_range` | Collinear + coord-range bounds ⇒ point lies on the segment `[exact]` | 3 |
| `Intersect_b64.v : b64_intersect_sign_filtered_sound_small_int` | 5-valued predicate's None/Point verdicts sound on integer coords `[int-b64]` | 4 |
| `Intersect_b64_exact.v : b64_intersect_point_{x,y}` | Intersection coords carry a Qed forward-error bound (K·ε) `[int-b64]` | 4 |

`[oracle]` `SignFiltered` bit-exact on 187/187 differential cases.
**Open:** float coordinate computation (needs `b64_div` + error analysis).

## Phase 2 — Snap rounding (Hobby / Halperin–Packer noder)

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `SnapRounding_b64.v : b64_snap_round_preserves_passes_through` | Snapping preserves which hot pixels a segment passes through `[int-b64]` | 4 |
| `SnapRounding_b64.v : b64_snap_idempotent_finite` | **Precision-reducer idempotence:** re-snapping a finite point to the grid returns the *identical* binary64 (bit-level, not just equal real) `[int-b64]` | 4 |
| `TopologicalCorrectness_b64.v : b64_snap_round_preserves_shared_hot_pixel` | Segments sharing a pixel still share one after snapping `[int-b64]` | 4 |
| `HobbyTheorem_b64.v : hobby_lemma_4_2` | Hobby Lemma 4.2 (strip-shaped snap region) `[exact]` | 3 |
| `HobbyTheorem_b64.v : hobby_theorem_4_1_conditional` | **Conditional headline:** snap preserves "fully intersected", assuming Lemma 4.3's no-proper half `[cond]` | 4 |
| `HotPixel_b64.v : b64_passes_through_sound` | **Closed filter sound:** bool `true` ⇒ the segment (and its unit-grid snap) really meet the closed hot pixel `[exact]` | 4 |
| `HotPixel_b64.v : b64_passes_through_complete` | **Closed filter complete:** a real (half-open) pass ⇒ the bool fires `[exact]` | 4 |
| `HotPixel.v : in_hot_pixel_convex` | Half-open hot pixel is convex: both endpoints in ⇒ whole segment in `[exact]` | 3 |
| `HotPixelConvex_b64.v : b64_both_endpoints_in_pixel_whole_segment` | Same, lifted to b64-bridged points — the rounding-free endpoint route `[exact]` | 4 |
| `PassesThrough_b64_compute_unsound.v : b64_passes_through_compute_unsound` | **Honest negative:** the *rounded* compute filter is NOT sound vs the exact spec — a witness with `compute = true`, `spec = false` (sub-ulp over-accept) `[exact]` | 4 |
| `PassesThroughHalfopen_b64_compute_unsound.v : b64_passes_through_halfopen_compute_unsound` | Same honest negative for the **half-open** mode (`PASSES_THROUGH_HALFOPEN`): rounded half-open filter unsound vs its exact spec `[exact]` | 4 |
| `PassesThroughHalfopen_b64_compute_incomplete.v : b64_passes_through_halfopen_compute_incomplete` | **Honest negative (noder-unsafe direction):** the rounded half-open filter is NOT complete — `spec = true`, `compute = false` (drops a real pass grazing the open edge) `[exact]` | 4 |
| `PassesThrough_b64_compute_asymmetric.v : b64_passes_through_compute_asymmetric` (+`_halfopen_`) | **Honest negative (order-dependent noding):** the rounded passes-through filter is NOT symmetric under segment reversal — `compute P0 P1 C = true` but `compute P1 P0 C = false` (closed + half-open). The order-dependence root behind JTS#752 / JTS#1133; pure `vm_compute` `[full-b64]` | 4 |
| `PassesThrough_b64_spec_symmetric.v : b64_passes_through_hot_pixel_symmetric` | **Green companion:** the *exact* R-spec passes-through filter IS symmetric under segment reversal (`spec P0 P1 C = spec P1 P0 C`) — the order-safe noder primitive the rounded filter fails to be `[exact]` | 4 |
| `PassesThrough_b64_grid_exact.v : b64_passes_through_grid_exact_iff_touch` | **C1 grid-exactness reduction (#66 pivot):** on the unit grid a point is a fixed point of `b64_snap`, so the snap-consistency conjunct is vacuous — full-predicate grid-exactness (`compute = spec`) reduces to the single Liang-Barsky touch. Isolates the open rounded-vs-exact touch core; Qed-closed `[full-b64]` | 4 |
| `PassesThrough_b64_grid_exact.v : coord_int_safe_snap_id` | **C1 slice 2:** an integer-valued, bounded, finite coordinate (`coord_int_safe`) is a `b64_snap` fixed point — the integer grid IS the fixed-point grid, so the reduction's hypothesis is discharged for genuine integer-grid (post-snap noder) inputs; Qed-closed `[full-b64]` | 4 |
| `PassesThrough_b64_grid_exact.v : slab_guard_bridge` | **C1 slice 3:** the rounded compute degenerate-slab guard on binary64 operands equals the exact-spec guard on their `B2R` values (`b64_le_eq_Rle_bool` + `b64_eqb_true_iff_B2R`); the division-free layer of the single-touch core; Qed-closed `[full-b64]` | 4 |
| `PassesThrough_b64_grid_exact.v : b64_minus_half_exact` | **C1 slice 4 (coordinate-exactness):** general half-integer subtraction is exact — for half-integer-valued operands with mantissa difference `< 2^prec`, `b64_minus` equals the exact real difference (`generic_format_half_prec` + `b64_minus_correct`). Covers the t-bound numerators (half-integer slab bound − integer endpoint) that exceed the existing 27-bit helper; Qed-closed `[full-b64]` | 4 |
| `PassesThrough_b64_grid_exact.v : b64_max_B2R` (+`b64_min_B2R`) | **C1 slice 5 (max/min composition):** the operand-selecting `b64_max`/`b64_min` bridge to `Rmax`/`Rmin` on `B2R` values for finite operands — reduces the clipped-interval t-bound test to a comparison of the real values of the rounded t-bounds, isolating the division rounding to the per-bound level; Qed-closed `[full-b64]` | 4 |

`[oracle]` `PASSES_THROUGH_FILTER`/`PASSES_THROUGH_HALFOPEN`. The closed-filter
rows pin the **closed** filter, sound *and* complete vs the closed hot-pixel
R-spec at unit grid (the half-open predicate is strictly stronger:
`b64_..._halfopen_implies_closed`). These characterise the R-spec predicate;
the extracted oracle runs the bit-exact computational mirror
(`PassesThrough_b64_compute.v`, validated bit-for-bit). The naive
`compute ⇒ spec` rounding bridge is **machine-checked false** (the last row;
`docs/oracle-soundness-finding.md`); the provable, useful directions are grid
exactness (C1) and completeness `spec ⇒ compute` (C2), both strongly evidenced
and open. The rounded filter is also **not symmetric** under segment reversal
(`PassesThrough_b64_compute_asymmetric.v`, both modes) — the order-dependent
noding root behind JTS#752 / JTS#1133; the symmetric, sound primitive is the
exact R-spec, not the rounded compute filter.
**Refuted:** `hobby_lemma_4_3_no_proper` is **machine-checked false** as
stated (`HobbyCounterexample_b64.v`; `docs/hobby-lemma-4-3-no-proper-refutation.md`)
— snap-rounding collapses two parallel segments onto one grid line,
manufacturing a collinear-overlap proper intersection. Moved from the
deferred-proof registry to the counterexample registry. Cite as
"conditional headline"; the per-pair preservation premise is provable
only over noded arrangements, not for arbitrary segment pairs.

`[oracle]` `CURVE_SNAP_DECISION` / `CURVE_SNAP_INVARIANTS_EXACT` (PRC-SN,
JTS#1195): exact-`Q` curve-snap grid-friendliness — snap the three arc control
points to a 1/scale grid (`q_make_precise`), then `PRESERVE` the arc iff the
snapped circumcentre lands on the grid, else `DENSIFY` (`DEGEN` if the snapped
controls go collinear). Exact `Q` catches the double-rounding the JTS binary64
centre computation hides on large / sub-grid coordinates. Reuses the
snap-rounding machinery; pure rational, no transcendental and no new axiom.

## Phase 3 — Planar overlay (OverlayNG)

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `Overlay.v : boolean_op` (+comm. lemmas) | Set semantics of union/intersection/difference/symdiff `[exact]` | 3 |
| `OverlayBridge.v : correct_labels_all_ops` | Edge labelling correct for every boolean op `[int-b64]` | 4 |
| `OverlayCorrectness.v : overlay_ng_correct_conditional` | **Conditional headline:** extracted overlay = boolean op, under 3 named hypotheses `[cond]` | 4 |
| `JordanCurveSeam.v : geometric_interior_stdlib_vacuous` | **JCT seam refutation:** the corpus's `geometric_interior_stdlib` is identically false (discontinuous "jump" paths collapse `connected_in_complement`), so the JCT-conditional headline is only vacuously satisfiable `[exact]` | 3 |
| `JordanCurveSeam.v : jct_hypotheses_force_empty_interior` | The conditional headline's `geometric_interior_stdlib ↔ interior_pred` hypothesis forces `interior_pred` empty too `[exact]` | 3 |
| `JordanCurveSeam.v : far_points_connected_cont` | The corrected continuous relation is non-degenerate: a straight-line path joins two off-box points in the complement — discontinuity, not geometry, caused the collapse `[exact]` | 3 |
| `JordanCurveSeam.v : jct_cont_interior_is_geometric` | **Sufficiency:** under `JCT_two_components_cont` (now with the separation clause), every interior point is a `geometric_interior_cont` point — so re-pointing H1 onto `geometric_interior_cont` is a genuine, satisfiable obligation, not the vacuous one. Does *not* prove the JCT `[exact]` | 3 |
| `JCT.v : continuity_glue` | Two functions continuous on ℝ that agree at a point glue into a continuous function — the analysis lemma behind continuous-path concatenation `[exact]` | 3 |
| `JCT.v : connected_in_complement_cont_trans` | `connected_in_complement_cont` is transitive (midpoint concatenation, glued continuous); with `_refl`/`_sym` it is an equivalence relation on the complement `[exact]` | 3 |
| `JCT.v : in_bounded_component_cont_invariant` | Boundedness is a component invariant for the continuous relation — constant on a connectivity class `[exact]` | 3 |
| `JCT.v : no_path_from_interior_to_exterior` | **Sketch's "thesis-scale" core is free:** with interior = bounded component, an interior point reaches no non-interior point through the complement — the Qed counterpart of `JCT_two_components_cont`'s separation clause, by component invariance, no JCT `[exact]` | 3 |
| `JCT.v : far_point_not_interior` | Honest continuous analogue of the vacuity witness: a point far past the bounding box is NOT interior (a real straight-line ray escapes any radius) — without claiming the interior empty `[exact]` | 3 |
| `JCT.v : point_in_ring_correct_jct_cont` | **Non-vacuous continuous headline:** `point_in_ring ↔ geometric_interior_cont` under the single named seam Prop `parity_characterises_interior_cont` (the genuine remaining JCT content) `[cond]` | 3 |

`[oracle]` `EDGE_IN_RESULT`.
**Open:** `extract_rings_valid` (DCEL, registered deferred) + polygonal JCT
(thesis-scale, no stub). The JCT seam's prior `geometric_interior_stdlib`
formulation is now **refuted as vacuous**
(`JordanCurveSeam.v : geometric_interior_stdlib_vacuous`); the genuine
theorem is restated over continuous paths as `JCT_two_components_cont`
(stated, not proved), and the overlay/buffer headline H1 has been
**re-pointed** off `geometric_interior_stdlib` onto `geometric_interior_cont`
(`OverlayCorrectness.v`, `docs/buffer-noder-pipeline.md`) so it is no longer
vacuous. See [`docs/jct-vacuity-finding.md`](jct-vacuity-finding.md) and
[`docs/h1-vacuity/`](h1-vacuity/). Cite as "conditional headline + oracle".

## Phase 4 — Native curves (linearization, chord-approx arcs)

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `Linearise.v : chord_le_detour` | A chord ≤ the polyline detour it replaces `[exact]` | 3 |
| `Linearise.v : disjoint_under_linearise` | ε-linearization preserves disjointness within tolerance `[exact]` | 3 |
| `Linearise.v : regime3_counterexample` | Honest negative: a predicate linearization cannot preserve `[exact]` | 3 |
| `ArcChordApprox.v : sagitta_le_arc_radius` | Chord-vs-arc deviation bounded by the radius `[exact]` | 3 |
| `ArcIntersectIVT.v : chord_crosses_arc_circle_implies_circle_intersection` | Sign change of in-circle along a chord ⇒ real crossing (IVT) `[exact]` | 3 |
| `ArcOverlay.v : arc_overlay_correct_chord_approx` | **Conditional headline:** result point within `max_sagitta` of an arc, under 2 bridge hypotheses `[cond]` | 3 |
| `Atan2.v : cos_atan2` (+`sin_atan2`) | **Option-A foundation (issue #64):** the Stdlib-`Ratan`-built `atan2 y x` is the polar angle of `(x,y)` — `cos = x/r`, `sin = y/r` for `(x,y)≠0` `[exact]` | 4 |
| `AngleBetween.v : cos_angle_between` (+`sin_angle_between`) | **Option-A central angle/sweep (issue #64):** the signed angle `atan2(cross,dot)` between two vectors has `cos = dot/(\|u\|\|v\|)`, `sin = cross/(\|u\|\|v\|)` (Lagrange identity); sign encodes orientation. Range (-π,π] via `atan2_range` `[exact]` | 4 |
| `ArcLength.v : chord_le_arc_length` (+`chord_subtended_sq`) | **Option-A exact arc length (issue #64):** `arc_length = r·θ`; the chord never exceeds the arc (`2r·sin(θ/2) ≤ rθ`), and `chord² = 2r²(1−cosθ)` (half-angle bridge to dot products) `[exact]` | 4 |
| `InCircle_b64_exact.v : b64_inCircle_exact_sound` | **Full-plane sign exactness (issue #64 ask #4b):** the common-exponent integer-determinant predicate's sign agrees with `inCircle_R_BP` for all finite binary64 inputs — integer `ℤ` arithmetic only, no float ops, **3 axioms (no `classic`)** `[full-b64]` | 3 |
| `InCircle_b64_exact.v : b64_inCircle_exact_for_small_int` | **Integer-regime value exactness:** `B2R (b64_inCircle …) = inCircle_R_BP` on the nose when every coordinate is integer-valued with `\|n\| ≤ 2¹¹` `[int-b64-arc]` | 4 |
| `InCircle_b64_exact.v : b64_inCircle_B2R_sign_sound_small_int` | Sign of the rounded `b64_inCircle` value agrees with `inCircle_R_BP` in the same `2¹¹` integer regime `[int-b64-arc]` | 4 |
| `InCircle_b64_exact.v : perron_inCircle_sign_sound` | Perron stage-10 thin-sliver witness at the `2¹¹` boundary: opposite-sign chord endpoints with bit-exact `b64_inCircle` values `[int-b64-arc]` | 4 |
| `ArcLineIntersect_b64_exact.v : b64_arc_line_{sP_R,sQ_R,dx_R,dy_R}` | **Arc-line Scope A (issue #64 ask #5a):** first-stage Cramer prefix before division — outer `sP`/`sQ` inCircle evaluations and chord `dx`/`dy` differences are bit-exact integer-valued binary64 `[int-b64-arc]` | 4 |

`[oracle]` `INCIRCLE_SIGN`/`ARC_CHORD_CROSSES_CIRCLE`/`ARC_PASSES_THROUGH_PIXEL` +
the three issue-#64 arc-length modes below.
**Arc length is transcendental** (`s = √r²·Θ`, `Θ` an angle) so it has *no
Coq-extractable form*. The honest oracle therefore splits along the exactness
ladder (cf. `ArcChordApprox.v`'s polynomial layer):
- **`ARC_LENGTH_INVARIANTS_EXACT`** — the *exact-rational* invariants `r²`,
  `cos θ₀ = dot/r²`, major-arc flag (pure zarith `Q`; mirrors
  `ArcLength.chord_subtended_sq` / `AngleBetween.cos_angle_between`). Exact about
  the geometry *around* the length, not the length value. Ratchet-clean.
- **`ARC_SHORTER`** — *exact decision* of which of two arcs is shorter, decidable
  rationally when radii match (order of `Θ` from `cos θ₀` + flag); reports
  `TRANSCENDENTAL` rather than rounding when radii differ. Ratchet-clean.
- **`ARC_LENGTH`** — the literal float length, an *interface-boundary* mode
  (the value JTS/NTS compute via `Math.sqrt`/`Math.acos`); one rounding past the
  exact invariants. Hand-rolled float, a sanctioned ratchet exception
  (`docs/oracle-handrolled-allowlist.txt`, interface-boundary category).

The **arc circular-segment area** (M-AREA-CP) follows the same split:
`A_seg = (r²/2)(Θ − sin Θ)`.
- **`ARC_AREA_INVARIANTS_EXACT`** — exact rationals `r²`, `cos θ₀`, `sin²θ₀`,
  major flag (pure `Q`, ratchet-clean).
- **`ARC_AREA`** — the float segment area, interface-boundary (one `acos`+`sin`
  past the exact invariants). These replace main's earlier hand-rolled shoelace
  stub, which had bypassed the (then BSD-awk-broken) ratchet.
**Option-A note (issue #64):** `atan2` work is **4-axiom** — Stdlib's `atan`
pulls `Classical_Prop.classic` (cos/sin/sqrt stay 3-axiom). This is the cost of
the JTS-faithful atan2 representation; downstream arc-length/sweep proofs
inherit it.
**Caveat:** bridge hypotheses are *boundary* closeness — this backs "chord
approximation correct to tolerance", **not** "fixes CIRCULARSTRING
self-intersection".
**Arc-line honest scoping (PR #146):** Scope A proves only the prefix before
the dividing step (`sP`, `sQ`, `dx`, `dy`). The headline
`B2R (b64_arc_line_intersect_point_x …) = arc_line_intersect_x_R …` does
*not* hold on the nose in the integer regime (intersection parameter is
generally non-dyadic); round-chain identity (Scope B) and forward-error bound
(Scope C) remain queued.

## Issue #67 — DE-9IM matrix algebra (`DE9IM.v`, session 1)

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `DE9IM.v : im_disjoint_not_intersects_partial` | **Partial headline:** JTS `disjoint` forces `intersects₀/₁/₄` false (not full `intersects` — `intersects₃` can still match; see gap witnesses) `[exact]` | 0 |
| `DE9IM.v : im_contains_transpose_within` (+`predicate_contains_transpose_within`) | `contains` on `m` ⇔ `within` on `matrix_transpose m` (JTS converse) `[exact]` | 0 |
| `DE9IM.v : im_covers_transpose_coveredBy` (+`predicate_covers_transpose_coveredBy`) | `covers` on `m` ⇔ `coveredBy` on transpose (`pattern_transpose` on all four JTS covers patterns) `[exact]` | 0 |
| `DE9IM.v : disjoint_intersects3_example_holds` | **Honest gap:** a matrix can be both `disjoint` and `intersects₃` (abstract IM algebra ≠ complete geometry IM) `[exact]` | 0 |

Full RelateNG matrix-fill and prepared-cache slices remain follow-up (#67 S3+).

## Issue #67 — line-line DE-9IM soundness (`RelateLineLine.v`, session 2)

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `RelateLineLine.v : line_line_proper_cross_sound` | **Proper crossing:** strict opposite-sign crosses ⇒ witness matrix satisfies `Crosses` and `Intersects` `[exact]` | 3 |
| `RelateLineLine.v : line_line_rejection_disjoint_sound` | **Rejection:** same-side sign test ⇒ `Disjoint` witness and no shared point (soundness of NTS rejection) `[exact]` | 3 |
| `RelateLineLine.v : line_line_share_intersects_sound` | **Share-point:** any `between` witness ⇒ `Intersects` witness matrix `[exact]` | 3 |
| `RelateLineLine.v : line_line_collinear_overlap_sound` | **Collinear overlap:** both endpoints of CD on AB ⇒ `Overlaps` (LL) witness `[exact]` | 3 |

Witness matrices are soundness targets, not a computed RelateNG IM. Endpoint-only touches inherit existential `Intersects` only.

## Issue #67 — Romanschek line–line oracle matrices (`RelateLineLine.v`, S3 seed)

Pinned 9-char DE-9IM strings from Romanschek et al. (IJGI 2021) Table 5/6 /
[topology-relations](https://github.com/dd-bim/topology-relations) agree with NTS 2.3.0 at
extent `r_max ≤ 1056`. Vectors: `oracle/de9im_line_line_vectors.txt`. Predicate
lemmas only — no WKT→matrix computation yet.

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `RelateLineLine.v : paper_test7_overlaps` | Test 7 (`1FFF0FFF2`) satisfies `Overlaps` (LL) `[exact]` | 3 |
| `RelateLineLine.v : paper_test6_not_crosses` | Test 6 (`FF1FF0102`) does **not** satisfy `Crosses` under `pat_crosses_ll` (II=F) `[exact]` | 3 |
| `RelateLineLine.v : paper_test13_crosses` | Test 13 (`0F1FF0102`) satisfies `Crosses` (LL); II=0 matches `ll_matrix_point_ii` `[exact]` | 3 |
| `RelateLineLine.v : paper_test10_not_disjoint` | Test 10 (`FF10F0102`) is **not** `Disjoint` (BI=0) though segments are separated `[exact]` | 3 |
| `RelateLineLine.v : paper_test7_agrees_overlap_witness_core` | Test 7 shares II/BB cells with `ll_matrix_overlap_ii` `[exact]` | 3 |

## Foundational — squared distance / degenerate cases (`Distance.v`)

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `Distance.v : dist_sq_nonneg` | Squared distance ≥ 0 `[exact]` | 3 |
| `Distance.v : dist_sq_zero_iff_eq` | Squared distance = 0 ⇔ points coincide `[exact]` | 3 |
| `Distance.v : dist_le_iff_dist_sq_le` | Distance compare ⇔ squared-distance compare (justifies sqrt-free fast path) `[exact]` | 3 |

Unconditional exact-reals — the most directly citable rows.
