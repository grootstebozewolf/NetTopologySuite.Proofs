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
(`|coord| ≤ 2²⁵`) · `[full-b64]` *all* finite binary64 (exact, no magnitude
limit) · `[cond]` holds under named hypotheses · `[oracle]` extracted,
differential-testable against the C# port.

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
**Open:** `hobby_lemma_4_3_no_proper` (registered deferred). Cite as
"conditional headline", not "Hobby's theorem proved".

## Phase 3 — Planar overlay (OverlayNG)

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `Overlay.v : boolean_op` (+comm. lemmas) | Set semantics of union/intersection/difference/symdiff `[exact]` | 3 |
| `OverlayBridge.v : correct_labels_all_ops` | Edge labelling correct for every boolean op `[int-b64]` | 4 |
| `OverlayCorrectness.v : overlay_ng_correct_conditional` | **Conditional headline:** extracted overlay = boolean op, under 3 named hypotheses `[cond]` | 4 |

`[oracle]` `EDGE_IN_RESULT`.
**Open:** `extract_rings_valid` (DCEL, registered deferred) + polygonal JCT
(thesis-scale, no stub). Cite as "conditional headline + oracle".

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

`[oracle]` `INCIRCLE_SIGN`/`ARC_CHORD_CROSSES_CIRCLE`/`ARC_PASSES_THROUGH_PIXEL`.
**Option-A note (issue #64):** `atan2` work is **4-axiom** — Stdlib's `atan`
pulls `Classical_Prop.classic` (cos/sin/sqrt stay 3-axiom). This is the cost of
the JTS-faithful atan2 representation; downstream arc-length/sweep proofs
inherit it.
**Caveat:** bridge hypotheses are *boundary* closeness — this backs "chord
approximation correct to tolerance", **not** "fixes CIRCULARSTRING
self-intersection".

## Foundational — squared distance / degenerate cases (`Distance.v`)

| `file : theorem` | Meaning | Ax |
|---|---|---|
| `Distance.v : dist_sq_nonneg` | Squared distance ≥ 0 `[exact]` | 3 |
| `Distance.v : dist_sq_zero_iff_eq` | Squared distance = 0 ⇔ points coincide `[exact]` | 3 |
| `Distance.v : dist_le_iff_dist_sq_le` | Distance compare ⇔ squared-distance compare (justifies sqrt-free fast path) `[exact]` | 3 |

Unconditional exact-reals — the most directly citable rows.
