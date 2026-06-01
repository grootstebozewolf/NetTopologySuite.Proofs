# Verified Claims — NetTopologySuite.Proofs

Companion mechanized proofs (Rocq/Coq 9.1.1, + Flocq 4.2.2 for the
binary64 layer) for foundational NetTopologySuite / JTS primitives.

**What this is.** A citable index of what is *actually proved*, with exact
theorem names, a one-line plain-language meaning, the axiom footprint, and
an honest scope qualifier for each. Link this file (and a specific theorem)
when discussing a robustness issue.

**What this is not.** Not a verified re-implementation of NTS. The
guarantees are *soundness* statements about predicates/algorithms, in one
of three regimes — (a) exact real arithmetic, (b) the integer-coordinate
binary64 regime (`|coord| ≤ 2²⁵`), or (c) *conditional* on explicitly named
hypotheses. Where a result is conditional or its converse is open, it says
so. Full unconditional soundness against IEEE-754 across all magnitudes is
**not** claimed end-to-end on any phase.

**Axiom discipline.** Every theorem ends in `Qed` (CI rejects unregistered
`Admitted`). Files in `theories/` use only the **three classical-reals
axioms** (`ClassicalDedekindReals.sig_not_dec`, `sig_forall_dec`,
`FunctionalExtensionality.functional_extensionality_dep`). Files in
`theories-flocq/` additionally inherit `Classical_Prop.classic` from Flocq's
binary64 arithmetic (tracked in `docs/audit-exceptions.txt`). Footprints
below are stated per claim. See the [README](../README.md) for the full
discipline (Qed invariant, tiered `Admitted` registries, per-theorem axiom
audit).

Legend: **[exact]** = exact-reals; **[int-b64]** = integer-regime binary64;
**[conditional]** = holds under named hypotheses; **[oracle]** = an
extracted, differential-testable decision procedure exists.

---

## Phase 0 — Robust orientation  ·  *“SignFlip Nightmares”*

The orientation (signed-area / CCW) predicate underlying `Orientation.Index`
and every CCW test.

| Theorem (`file : name`) | Plain meaning | Footprint |
|---|---|---|
| `theories/Orientation.v : cross_antisymmetric` | Swapping the two reference points flips the orientation sign. **[exact]** | 3 reals |
| `theories/Orientation.v : cross_cyclic` | Cyclic rotation of the three points preserves the sign. **[exact]** | 3 reals |
| `theories/Orientation.v : cross_translation_invariant` | Translating all three points leaves the orientation unchanged. **[exact]** | 3 reals |
| `theories/Orientation.v : cross_at_P0_is_collinear` (+ `_P1`, `_degenerate_base`) | Coincident points are reported collinear (sign 0). **[exact]** | 3 reals |
| `theories-flocq/Orient_b64_exact.v : b64_orient2d_exact_for_small_int` | The binary64 determinant equals the exact real cross product on integer coordinates. **[int-b64]** | 4 (incl. `classic`) |
| `theories-flocq/Orient_b64_exact.v : b64_orient_sign_filtered_sound_small_int` | **Headline.** The 5-valued filtered predicate's `Pos/Neg/Zero` verdicts agree with the true sign on integer coordinates; `Uncertain`/`NaN` make no claim. **[int-b64]** | 4 (incl. `classic`) |

**[oracle]** `RobustOrientation` (`Orient2d`/`Sign`/`SignFiltered`) is
bit-exact vs the Coq-extracted `RocqRefRunner` `ORIENT` / `ORIENT_FILTERED`
modes on a differential corpus (random + NaN + huge-magnitude + integer
adversarial families).

**Scope.** General bounded-magnitude soundness (Shewchuk Stages B–D, where
the filter returns `Uncertain`) is a **registered deferred proof**
(thesis-scale; `docs/admitted-deferred-proofs.txt`). The defensible claim
today is *the filter is sound, and on integer coordinates it is complete*.

---

## Phase 1 — Robust segment intersection  ·  *“Phantom Crossings”*

The cross-product intersection test behind `RobustLineIntersector` and the
“non-noded intersection” failure class.

| Theorem (`file : name`) | Plain meaning | Footprint |
|---|---|---|
| `theories/Intersect.v : segments_share_point_implies_opposite_sides` | If two segments share a point, neither segment's line strictly separates the other's endpoints. **[exact]** | 3 reals |
| `theories/Intersect.v : same_side_rejection_is_sound` | **Soundness of rejection.** If the sign test says “no intersection”, there is genuinely no shared point — so the fast-path reject never drops a real crossing. **[exact]** | 3 reals |
| `theories/Intersect.v : strict_completeness` | Converse for the proper case: strict opposite-sides on both tests ⇒ an interior intersection point exists (Cramer construction). **[exact]** | 3 reals |
| `theories/Intersect.v : collinear_share_iff_1d_overlap` | **Collinear case (new).** For collinear segments, sharing a point ⇔ their 1-D extents overlap (an endpoint of one lies on the other). Closes the previously-deferred collinear converse. **[exact]** | 3 reals |
| `theories/Segment.v : between_of_on_line_and_coord_range` | Collinearity + both coordinate-range bounds ⇒ the point lies on the segment (detection of collinear sub-cases from raw coordinates). **[exact]** | 3 reals |
| `theories-flocq/Intersect_b64.v : b64_intersect_sign_filtered_sound_small_int` | The 5-valued intersection predicate's `None`/`Point` verdicts are sound on integer coordinates; `Collinear`/`Uncertain`/`NaN` make no claim. **[int-b64]** | 4 (incl. `classic`) |
| `theories-flocq/Intersect_b64_exact.v : b64_intersect_point_{x,y}` | Intersection-point coordinates carry a Qed-closed forward-error bound (K·ε / condition-number form). **[int-b64]** | 4 (incl. `classic`) |

**[oracle]** `RobustLineIntersector.SignFiltered` is bit-exact vs
`RocqRefRunner` `INTERSECT_FILTERED` / `INTERSECT_POINT_*` on 187/187
differential cases incl. an integer-regime adversarial family.

**Scope.** Predicate soundness is solid; the `IntersectCollinear`
disambiguation now has its full R-side characterization (above). General
floating-point coordinate computation (needs `b64_div` + error analysis) is
future work.

---

## Phase 2 — Snap rounding  ·  *“Hot-Pixel Drift”*

Hobby/Halperin–Packer snap-rounding noder (the layer that *prevents*
non-noded intersections downstream).

| Theorem (`file : name`) | Plain meaning | Footprint |
|---|---|---|
| `theories-flocq/SnapRounding_b64.v : b64_snap_round_preserves_passes_through` | Snapping a segment to the grid preserves which hot pixels it passes through. **[int-b64]** | 4 (incl. `classic`) |
| `theories-flocq/TopologicalCorrectness_b64.v : b64_snap_round_preserves_shared_hot_pixel` | Two segments sharing a hot pixel still share one after snapping (topology preserved at the supported level). **[int-b64]** | 4 (incl. `classic`) |
| `theories-flocq/HobbyTheorem_b64.v : hobby_lemma_4_2` | Hobby's Lemma 4.2 (strip-shaped snap region), Qed-closed. **[exact]** | 3 reals |
| `theories-flocq/HobbyTheorem_b64.v : hobby_theorem_4_1_conditional` | **Conditional headline.** Snap-rounding preserves “fully intersected”, *assuming* Lemma 4.3's no-proper half. **[conditional]** | 4 (incl. `classic`) |

**[oracle]** `PASSES_THROUGH_FILTER` / `PASSES_THROUGH_HALFOPEN` extracted.

**Scope.** Hobby Theorem 4.1 is **conditional** on
`hobby_lemma_4_3_no_proper`, a registered deferred (thesis-scale) proof.
Claim it as “conditional headline”, not “Hobby's theorem proved”.

---

## Phase 3 — Planar overlay (OverlayNG)  ·  *“Overlay Ghost Towns”*

Topology-graph construction, edge labelling, boolean overlay.

| Theorem (`file : name`) | Plain meaning | Footprint |
|---|---|---|
| `theories/Overlay.v : boolean_op` (+ commutativity lemmas) | Set-theoretic semantics of union/intersection/difference/symdiff, with proved commutativity. **[exact]** | 3 reals |
| `theories-flocq/OverlayBridge.v : correct_labels_all_ops` | Edge labelling is correct for every boolean op. **[int-b64]** | 4 (incl. `classic`) |
| `theories-flocq/OverlayCorrectness.v : overlay_ng_correct_conditional` | **Conditional headline.** The extracted overlay's point-set matches the boolean op, under three named hypotheses (JCT, valid ring assembly, semantic bridge). **[conditional]** | 4 (incl. `classic`) |

**[oracle]** `EDGE_IN_RESULT` extracted.

**Scope.** Headline is **conditional** on two open pieces: `extract_rings_valid`
(DCEL ring assembly — registered deferred, ~5–7 sessions) and the polygonal
Jordan Curve Theorem (thesis-scale, no stub — toolkit absent from the
ecosystem). Frame as “conditional headline + extracted oracle”, not
“OverlayNG verified”.

---

## Phase 4 — Native curves  ·  *“Arc Bend Betrayals”*

Curve linearization tolerance contract and chord-approximated arc overlay.

| Theorem (`file : name`) | Plain meaning | Footprint |
|---|---|---|
| `theories/Linearise.v : chord_le_detour` | A chord is no longer than the polyline detour it replaces. **[exact]** | 3 reals |
| `theories/Linearise.v : disjoint_under_linearise` | ε-linearization preserves disjointness within tolerance — feeds the `ILinearizable` tolerance contract. **[exact]** | 3 reals |
| `theories/Linearise.v : regime3_counterexample` | A tolerance-sensitive predicate where linearization *cannot* preserve the outcome — honest negative result. **[exact]** | 3 reals |
| `theories/ArcChordApprox.v : sagitta_le_arc_radius` | The chord-vs-arc deviation (sagitta) is bounded by the arc radius. **[exact]** | 3 reals |
| `theories/ArcIntersectIVT.v : chord_crosses_arc_circle_implies_circle_intersection` | A sign change of the in-circle test along a chord implies a real circle crossing (IVT). **[exact]** | 3 reals |
| `theories/ArcOverlay.v : arc_overlay_correct_chord_approx` | **Conditional headline.** A point in the chord-approximated boolean result is within `max_sagitta` of an arc curve, under two bridge hypotheses. **[conditional]** | 3 reals |

**[oracle]** `INCIRCLE_SIGN` / `ARC_CHORD_CROSSES_CIRCLE` /
`ARC_PASSES_THROUGH_PIXEL` extracted.

**Scope.** The arc-overlay headline's bridge hypotheses are **boundary**
closeness (distance to the 1-D arc curve), which is stronger than the bare
sagitta bound and does **not** back a claim like “fixes CIRCULARSTRING
self-intersection”. It backs *“chord approximation correct to tolerance”* —
the guarantee NTS.Curve already targets. Exact (non-chord) arc arithmetic is
deferred (no published Hobby analog for arcs).

---

## Foundational  ·  *“Sqrt Shadow Bugs”*

Squared-distance and degenerate-case algebra under `Distance.v` — used by
indexing, snap, and centroid fast paths.

| Theorem (`file : name`) | Plain meaning | Footprint |
|---|---|---|
| `theories/Distance.v : dist_sq_nonneg` | Squared distance is non-negative. **[exact]** | 3 reals |
| `theories/Distance.v : dist_sq_zero_iff_eq` | Squared distance is zero iff the points coincide (degenerate detection). **[exact]** | 3 reals |
| `theories/Distance.v : dist_le_iff_dist_sq_le` | Comparing distances ⇔ comparing squared distances — justifies the `sqrt`-free fast path. **[exact]** | 3 reals |

These are unconditional, exact-reals results — the most directly citable.

---

## How to cite

When commenting on a JTS/NTS issue, link this file plus the specific
`file : theorem` and quote the **plain meaning + scope qualifier** verbatim.
Lead with the unconditional **[exact]** rows (Phases 0/1 predicates,
Foundational); present **[conditional]** rows as “conditional headline +
extracted oracle”, never as “solved”. Offer a differential oracle (the
`RocqRefRunner` modes) to reproduce/debug concrete cases.
