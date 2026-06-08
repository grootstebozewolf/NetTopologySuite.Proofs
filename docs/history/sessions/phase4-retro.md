# Phase 4 retro — native circular arcs (chord approximation)

2026-05-29/30. One audit session, seven proof sessions, two follow-ups
(IVT closure, oracle extraction). Completion summary:
[`phase4-completion.md`](phase4-completion.md).

## What landed

| Session | Deliverable | Module | Outcome |
|---|---|---|---|
| S1 | chord-overfitting audit + Option B decision | — | docs |
| S2 | `CircularArc`, `to_geometry`, validity | `CurveGeometry.v` | Qed |
| S3 | `inCircle_R`, `arc_orient` | `ArcOrient.v` | Qed |
| S4 | arc-chord + arc-arc intersection predicates | `ArcIntersect.v` | Qed (soundness deferred) |
| S5 | `arc_passes_through_hot_pixel` | `ArcHotPixel.v` | Qed |
| S6 | sagitta, `arc_center_equidistant`, Pythagorean radius | `ArcChordApprox.v` | Qed |
| S7 | `arc_overlay_correct_chord_approx` (headline) | `ArcOverlay.v` | Qed |
| +IVT | `chord_crosses_arc_circle_implies_circle_intersection` | `ArcIntersectIVT.v` | Qed — closes S4 gap |
| +oracle | `INCIRCLE_SIGN` / `ARC_CHORD_CROSSES_CIRCLE` / `ARC_PASSES_THROUGH_PIXEL` | extraction | extracted |
| +PR #146 | `b64_inCircle` soundness + arc-line Scope A | `InCircle_b64_exact.v`, `ArcLineIntersect_b64_exact.v` | Qed — closes issue #64 ask #4b |

Zero `Admitted` across all seven theory files at the end.

## Three things worth carrying forward

**The plan ordering was wrong; the dependency graph was right.** The
audit (§5) planned top-down — chord-approx function and tolerance theorem
first, predicates behind them. Execution ran bottom-up: types →
orientation/inCircle → intersection → hot-pixel → sagitta → headline. The
plan's order would have forced the headline to be stated against
predicates that didn't exist yet. Lesson: decide the strategic fork
(Option A/B, typeclass refactor) in the scoping doc, but decide session
ordering one session ahead from the actual `Require` edges.

**Quarantine the analytic gap behind a predicate.** `arc_chord_intersect_sound`
needed an intermediate-value argument, not algebra. Stating every
consumer (hot-pixel, overlay) against the *predicate* rather than its
soundness let six sessions stay purely algebraic; the IVT witness closed
in one dedicated 210-line cycle (`inCircle_along_chord` is a polynomial,
hence continuous; sign change at the endpoints feeds `IVT_cor`). Same
shape as Phase 3's conditional headline and Stage D's "sum now,
non-overlap later" split.

**The headline's hypotheses are stronger than the sagitta bound — say so
loudly.** `arc_close_to_curves` is boundary closeness (proximity to the
1D arc curve), and the sagitta is a boundary-distance bound. So
`H_A_bridge`/`H_B_bridge` hold for polygons near the sagitta in size but
fail for points deep inside a large polygon, where boundary distance is
large but region membership matches exactly. The module says this
(`ArcOverlay.v:111–130`); it belongs at project level too, because it's
the single most important thing a consumer needs to know about Phase 4 —
and it's exactly where Option A's region-level semantics would pick up.

## Calibration

The 7-session estimate held for the headline, but "complete the phase"
quietly included the IVT closure and the oracle extraction. The honest
unit is "headline + its deferred analytic gap + its oracle mode." The
~70% infrastructure-reuse claim held: the headline's case split *is*
Phase 3's, with `arc_close_to_curves` swapped for the conclusion.

## Open items

- **Arc-line Scope B/C** — PR #146 landed Scope A (`sP`/`sQ`/`dx`/`dy`);
  headline coord identity and forward-error bound still queued.
- **Stale comment** — `ArcHotPixel.v:28` still calls
  `arc_chord_intersect_sound` "(Admitted, IVT-blocked)"; the IVT closure
  made that obsolete. ~2-line fix.
- **Boundary → region** — tightening the bridge hypotheses; Option A
  scope, not a patch.
- **Arc snap-rounding** — research gap, no published Hobby analog.
- **`Flatten()` dovetail** — consumer-driven.

## Axiom footprint

All seven files are classic-free (no snap-layer contact).
`ArcIntersectIVT.v` adds Stdlib `IVT_cor` / `Ranalysis_reg`, within the
allowlist. None in [`audit-exceptions.txt`](audit-exceptions.txt). No
`Admitted` / `Axiom` / `Parameter`.
