# Phase 4 completion: native circular arcs (chord approximation)

Phase 4 delivers a verified chord-approximated arc overlay — the
guarantee NTS users get today (arc operations correct up to chord
tolerance), machine-checked. The headline
`arc_overlay_correct_chord_approx` is Qed-closed under two bridge
hypotheses. The 7-session Option B plan plus two follow-ups (IVT
closure, oracle) landed on main 2026-05-29/30. Cycle reflection:
[`phase4-retro.md`](phase4-retro.md).

Two decisions were settled in the audit before any `.v` file:
**Option B** (chord approximation, 7 sessions) over Option A (exact arc,
20+ sessions with an arc-snap-rounding research gap); and **parallel
typeclasses** (`HasArcIntersect` alongside `HasIntersect`) over a
refactor. See
[`audit-phase4-chord-overfitting.md`](audit-phase4-chord-overfitting.md).

## Shipped (Qed-closed)

**Types** — [`theories/CurveGeometry.v`](../theories/CurveGeometry.v):
`CircularArc` (three control points), the curve geometry hierarchy,
`to_geometry : CurveGeometry -> nat -> Geometry` (the chord-approx
bridge), `valid_curve_geometry`.

**Orientation** — [`theories/ArcOrient.v`](../theories/ArcOrient.v):
`inCircle_R` (three-point circumcircle test), `arc_orient`.

**Intersection + IVT** —
[`theories/ArcIntersect.v`](../theories/ArcIntersect.v),
[`theories/ArcIntersectIVT.v`](../theories/ArcIntersectIVT.v):
arc-chord / arc-arc predicates, and
`chord_crosses_arc_circle_implies_circle_intersection` — a sign change
on the chord implies a real circumcircle crossing, via `IVT_cor` on the
continuous polynomial `inCircle_along_chord`. This was the only piece
needing real analysis; it was deferred behind the predicate interface
across S4–S7 and closed in its own cycle.

**Hot-pixel** — [`theories/ArcHotPixel.v`](../theories/ArcHotPixel.v):
`arc_passes_through_hot_pixel` (circle-rectangle decision procedure),
parameterised by `scale` as in Phase 2.

**Sagitta** — [`theories/ArcChordApprox.v`](../theories/ArcChordApprox.v):
`arc_center_equidistant`, `sagitta`, the chord-vs-arc bound
`sagitta_le_arc_radius`, the Pythagorean radius identity.

**Headline** — [`theories/ArcOverlay.v`](../theories/ArcOverlay.v):

```coq
Theorem arc_overlay_correct_chord_approx :
  forall (A B : CurveGeometry) (op : BooleanOp) (p : Point) (n : nat),
    valid_curve_geometry A ->
    valid_curve_geometry B ->
    (forall q, point_set (to_geometry A n) q ->
               arc_close_to_curves q A B (max_sagitta A B)) ->  (* H_A_bridge *)
    (forall q, point_set (to_geometry B n) q ->
               arc_close_to_curves q A B (max_sagitta A B)) ->  (* H_B_bridge *)
    boolean_op op (to_geometry A n) (to_geometry B n) p ->
    arc_close_to_curves p A B (max_sagitta A B).
```

A point in the chord-approximated result is within `max_sagitta` of an
arc curve. The proof is a case split on `op`, each case discharged by a
bridge hypothesis — structurally Phase 3's overlay case split with
`arc_close_to_curves` as the conclusion.

**Oracle** — RocqRefRunner modes `INCIRCLE_SIGN` /
`ARC_CHORD_CROSSES_CIRCLE` / `ARC_PASSES_THROUGH_PIXEL` extracted.

## Open

No `Admitted` anywhere in Phase 4. The open work is named hypotheses and
explicit future scope.

**Boundary vs. region (the honest caveat).** `arc_close_to_curves` is
*boundary* closeness — distance to the 1D arc curve — and the sagitta is
a boundary-distance bound. So `H_A_bridge`/`H_B_bridge` ask that *every*
point of the chord-polygon is close to an arc curve. That holds when the
polygon is close in size to the sagitta, but not for points deep inside
a large polygon, where boundary distance is large while region
membership still matches exactly (`ArcOverlay.v:111–130`). Tightening the
bridge from boundary to region equivalence is Option A's region-level
semantics, not a Phase 4 patch.

**Arc snap-rounding.** No published Hobby analog exists for arcs
(research-grade, like Phase 2's `hobby_lemma_4_3_no_proper`). Deferred to
a contingent Phase 5.

**`Flatten()` dovetail.** Match the corpus's chord approximation to
`NetTopologySuite.Curve`'s actual `Flatten()`. Consumer-driven.

## What "complete" means here

The chord-approximated overlay ships at the conditional level: all the
arc primitives are Qed-closed, the one analytic gap (IVT) is closed, and
the headline holds under two named bridge hypotheses. This is the same
guarantee NTS gives today, now verified. Exact-arc semantics (Option A)
is a separate, clearly-scoped program.

## Next

1. Fix the stale `ArcHotPixel.v:28` comment (it still calls
   `arc_chord_intersect_sound` "Admitted, IVT-blocked"; the IVT closure
   made that obsolete). ~2 lines.
2. `Flatten()` dovetail — consumer-driven.
3. Region-level semantics — Option A entry point.
4. Arc snap-rounding — Phase 5, if a consumer asks for exact arcs (the
   [`audit-phase4-curves.md`](audit-phase4-curves.md) §5 tripwire, ~2031).

## Audit

- No `Admitted` / `Axiom` / `Parameter` across the seven Phase 4 files.
  Open work is named hypotheses, not stubs.
- All Phase 4 files are classic-free (they don't touch the snap layer).
  `ArcIntersectIVT.v` adds Stdlib `IVT_cor` / `Ranalysis_reg`, within the
  same axiom allowlist. None appear in
  [`audit-exceptions.txt`](audit-exceptions.txt).
