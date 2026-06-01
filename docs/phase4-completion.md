# Phase 4 completion: native circular arcs (chord-approximation / Option B)

**Status.** Written 2026-06-01. Phase 4's deliverable — a Qed-closed
`arc_overlay_correct_chord_approx` headline for chord-approximated arc
overlay, with the supporting curve-geometry, orientation, intersection,
hot-pixel, and sagitta layers — landed on main 2026-05-29/30 across the
committed 7-session Option B plan plus two follow-up cycles (IVT-gap
closure, oracle extraction). This doc mirrors
[`docs/phase0-completion.md`](phase0-completion.md) ..
[`docs/phase3-completion.md`](phase3-completion.md); the cycle-by-cycle
reflection lives separately in
[`docs/phase4-retro.md`](phase4-retro.md).

The discipline observed for the earlier completion docs is mirrored
here: current state, what stays open, why this is "Phase 4 complete,"
future paths.

## Current state (2026-05-30, completion point)

The load-bearing strategic decisions were settled in the audit phase
**before** any `.v` file was written: Option B (chord approximation,
7 sessions) over Option A (exact arc, 20+ sessions including an
arc-snap-rounding research gap), and parallel typeclasses
(`HasArcIntersect` coexists with `HasIntersect`) over a refactor — see
[`docs/audit-phase4-chord-overfitting.md`](audit-phase4-chord-overfitting.md)
§4–§7 and [`docs/audit-phase4-curves.md`](audit-phase4-curves.md).

**Shipped, Qed-closed.**

Curve geometry types
([`theories/CurveGeometry.v`](../theories/CurveGeometry.v)):

- `CircularArc` (SQL/MM three-control-point: start / on-arc / end),
  `CurveSegment` / `CurveRing` / `CurvePolygon` / `CurveGeometry`.
- `to_geometry : CurveGeometry -> nat -> Geometry` — the
  chord-approximation bridge into Phase 3's `Geometry`.
- `valid_curve_geometry` — the arc-aware validity predicate.

Arc orientation
([`theories/ArcOrient.v`](../theories/ArcOrient.v)):

- `inCircle_R` — the three-point circumcircle in/out test over ℝ.
- `arc_orient` — three-point arc orientation (sign of curvature),
  reusing `cross_R` as the chord case.

Arc intersection + the IVT closure
([`theories/ArcIntersect.v`](../theories/ArcIntersect.v),
[`theories/ArcIntersectIVT.v`](../theories/ArcIntersectIVT.v)):

- `chord_crosses_arc_circle` + arc-chord / arc-arc intersection
  predicates.
- **`chord_crosses_arc_circle_implies_circle_intersection`** — the
  IVT gap (a sign change on the chord implies a real circumcircle
  crossing) closed via `IVT_cor` on the continuous polynomial
  `inCircle_along_chord`. This was the one piece needing real
  analysis; it was deferred along a clean predicate interface across
  S4–S7 and closed in its own cycle.

Arc hot-pixel
([`theories/ArcHotPixel.v`](../theories/ArcHotPixel.v)):

- `arc_passes_through_hot_pixel` — circle-rectangle decision procedure
  (the four edge-disjuncts + endpoint cases), parameterised by `scale`
  exactly as Phase 2.

Sagitta machinery
([`theories/ArcChordApprox.v`](../theories/ArcChordApprox.v)):

- `arc_center_equidistant`, `arc_radius_sq` (= mid = end),
  `sagitta`, and the chord-vs-arc-curve distance bound
  `sagitta_le_arc_radius` + the Pythagorean radius identity
  `arc_radius_sq_pythagorean`.

Conditional headline
([`theories/ArcOverlay.v`](../theories/ArcOverlay.v)):

- `arcs_of` / `max_sagitta` / `arc_close_to_curves` (boundary
  closeness: proximity to the 1D arc *curve*, `inCircle_R = 0` ∧
  arc-span containment).
- **`arc_overlay_correct_chord_approx`** — HEADLINE. A point in the
  chord-approximated boolean-op result is within `max_sagitta` of an
  arc curve, under two bridge hypotheses:

```coq
Theorem arc_overlay_correct_chord_approx :
  forall (A B : CurveGeometry) (op : BooleanOp) (p : Point) (n : nat),
    valid_curve_geometry A ->
    valid_curve_geometry B ->
    (forall q : Point,
       point_set (to_geometry A n) q ->
       arc_close_to_curves q A B (max_sagitta A B)) ->   (* H_A_bridge *)
    (forall q : Point,
       point_set (to_geometry B n) q ->
       arc_close_to_curves q A B (max_sagitta A B)) ->   (* H_B_bridge *)
    boolean_op op (to_geometry A n) (to_geometry B n) p ->
    arc_close_to_curves p A B (max_sagitta A B).
```

The proof is a clean case split on `op`, each `BooleanOp` case
discharged by `H_A_bridge` / `H_B_bridge` — structurally the Phase 3
case split with `arc_close_to_curves` as the conclusion.

Oracle consumer
([`theories-flocq/Validate_binary64_extract.v`](../theories-flocq/Validate_binary64_extract.v)):

- Hand-rolled RocqRefRunner modes `INCIRCLE_SIGN` /
  `ARC_CHORD_CROSSES_CIRCLE` / `ARC_PASSES_THROUGH_PIXEL` extracted for
  differential testing.

## Open

Unlike Phases 2 and 3, Phase 4 carries **no `Admitted`** — the open
work is expressed as the headline's named bridge hypotheses and as
explicitly-deferred future scope.

### `H_A_bridge` / `H_B_bridge` — boundary vs. region (the honest caveat)

`arc_close_to_curves` is **boundary** closeness (distance to the 1D arc
curve), and the sagitta bound is a boundary-distance bound. The bridge
hypotheses therefore ask the consumer to show that *every* point of the
chord-polygon is close to an arc curve — which holds for polygons close
in size to the sagitta but NOT for points deep inside a large polygon,
where boundary distance is large while region membership still matches
exactly (`ArcOverlay.v:111–130`). Tightening `H_*_bridge` from
boundary-closeness to region-equivalence is Option A's region-level
semantics — it is the seam where exact-arc work would begin, not a
Phase 4 patch.

### Arc snap-rounding (the research gap)

The audit flagged that there is **no published Hobby-theorem analog for
arcs** (`audit-phase4-chord-overfitting.md` §3, NEW PROOF). Option A's
arc snap-rounding theory is research-grade, comparable in shape to
Phase 2's `hobby_lemma_4_3_no_proper`. Deferred to a contingent Phase 5.

### `Flatten()` dovetail

Proving the corpus's chord approximation matches
`NetTopologySuite.Curve`'s actual `Flatten()` implementation —
consumer-driven, queued for when a downstream consumer asks.

## Why this is "Phase 4 complete"

Phase 4's deliverable is a **verified chord-approximated arc overlay**:
the guarantee NTS users actually get today (arc operations correct up
to chord-approximation tolerance), now machine-checked. That shipped
end-to-end at the conditional level:

- **Coq-side**: the curve-geometry types + `to_geometry` bridge, the
  arc orientation / intersection / hot-pixel / sagitta layers, the IVT
  gap closed, and `arc_overlay_correct_chord_approx` Qed-closed under
  two named bridge hypotheses — zero `Admitted` across all seven Phase
  4 theory files.
- **Oracle-side**: three hand-rolled arc modes extracted.

What's open — region-level tightening and exact-arc snap-rounding — is
Option A scope, carried as named hypotheses and explicit future work
rather than assumed. This mirrors Phases 0–3: the chokepoint deliverable
ships at its supported level; the harder completion is a separate,
clearly-scoped engagement.

## Future paths

In rough order of payoff vs. cost:

1. **Doc-drift cleanup** — `ArcHotPixel.v:28` still calls
   `arc_chord_intersect_sound` "(Admitted, IVT-blocked)"; the IVT
   closure made that obsolete. ~2-line bounded fix.
2. **`Flatten()` dovetail** — consumer-driven; matches the corpus's
   chord approximation to `NetTopologySuite.Curve`.
3. **Region-level semantics (Option A entry)** — tighten
   `H_*_bridge` from boundary to region equivalence. Substantial.
4. **Arc snap-rounding (Phase 5)** — the research gap; only if a
   downstream consumer asks for exact arc support (see the
   `audit-phase4-curves.md` §5 tripwire, ~2031).

## Audit summary

- **No `Admitted`, `Axiom`, `Parameter`** across the seven Phase 4
  theory files. The open work is named hypotheses, not stubs.
- **No silent narrowing of contracts.** `H_A_bridge` / `H_B_bridge`
  are the headline's explicit premises; the module documents that they
  are stronger than the bare sagitta bound (boundary vs. region).
- **Clean Stdlib lane.** All Phase 4 files pull only the three
  README-allowlisted classical-reals axioms (no `Classical_Prop.classic`
  — they do not touch the snap layer). `ArcIntersectIVT.v` adds the
  Stdlib `IVT_cor` / `Ranalysis_reg` dependency, within the same
  allowlist. None appear in
  [`docs/audit-exceptions.txt`](audit-exceptions.txt).

## Why this doc lands now

Phase 4 reached its committed endpoint, and the chord-approximation
thread closed the Phase 0–4 chokepoint sequence at the supported level.
This completion doc, alongside the cycle reflection in
[`docs/phase4-retro.md`](phase4-retro.md), closes the documentation
chain Phase 0 → Phase 1 → Phase 2 → Phase 3 → Phase 4 so the history
reads linearly for future contributors.

---

**AI assistance disclosure:** AI-drafted, human-reviewed.
  Assisted-by: Claude
