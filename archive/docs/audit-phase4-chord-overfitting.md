# Phase 4 Audit: Chord Overfitting Classification

**Status**: Per-theorem audit (complements
`docs/audit-phase4-curves.md` — strategic scoping).
**Date**: 2026-05-29.
**Session**: Phase 4 Session 1.
**Goal**: Map every corpus theorem against arc geometry
requirements.  Output: precise transfer / generalize / new-proof
classification with the load-bearing decision point flagged before
Session 2.

This doc does NOT repeat `audit-phase4-curves.md` §1-§4 (architecture
diagnosis), §5 (tripwire), or §6 (dovetail status).  Those decisions
stand.  This doc is the **theorem-by-theorem accounting** that
Phase 4's session-level planning needs.

---

## §1 — The chord overfitting statement (precise)

Every corpus theorem from Phase 0 through Phase 3 that references
**geometry** (not just structure) assumes one or more of these four
chord-paradigm primitives:

  1. **Linear parametrisation**: `segment_point P0 P1 t :=
     (1-t)*P0 + t*P1` (theories/HotPixel.v:106).
  2. **Proper-intersection of two chords**:
     `segments_intersect_properly P0 P1 Q0 Q1` (Overlay.v:125),
     defined via linear parametrisations.
  3. **4-point intersection signature**: `HasIntersect` typeclass
     (Intersect_b64_exact.v:2153) requires `T -> T -> T -> T ->
     binary64` — two chord segments = four endpoints.
  4. **Linear edge in Liang-Barsky / hot-pixel test**:
     `segment_touches_hot_pixel P0 P1 C scale` (HotPixel.v:110),
     defined via `segment_point`.

Arc geometry (SQL/MM CIRCULARSTRING: three control points on a
circle) violates ALL FOUR.  A circular arc has no linear `t`
parameter, intersects in up to degree-4 (arc-arc) or degree-2
(arc-line) solutions, and the four-control-point signature doesn't
fit.

The "chord overfitting" is structural, not incidental: removing the
chord assumption would propagate through the entire predicate +
noding + overlay pipeline.

---

## §2 — The four violations (per theorem)

### Violation 1: Linear parametrisation

**Affected definitions (chord-only by construction)**:

| Definition | File:line | Form |
|---|---|---|
| `segment_point` | theories/HotPixel.v:106 | `(1-t)*P0 + t*P1` |
| `segments_intersect_properly` | theories/Overlay.v:125 | `(1-t)*px P0 + t*px P1 = ...` |
| `segment_touches_hot_pixel` | theories/HotPixel.v:110 | `exists t, in_hot_pixel (segment_point P0 P1 t) ...` |
| `passes_through_hot_pixel_halfopen` | theories-flocq/PassesThroughHalfopen_b64.v | composes the above |
| `fully_intersected` | theories-flocq/HobbyTheorem_b64.v:75 | composes `segments_intersect_only_at_endpoints` |
| `snap_round_segments` | theories-flocq/HobbyTheorem_b64.v | operates on `list (Point * Point)` chord-segments |

### Violation 2: Intersection degree

**`HasIntersect` typeclass signature is chord-paradigm-specific**:

```coq
Class HasIntersect (T : Type) : Type := {
  intersect_x : T -> T -> T -> T -> binary64;
  intersect_y : T -> T -> T -> T -> binary64;
  intersect_inputs_safe : T -> T -> T -> T -> Prop;
}.
```

Four-point signature = two chord segments × two endpoints each.
Arc-arc intersection has up to 4 solutions over a 3-control-point
input on each side (6 inputs total).  **Not a new instance — a
PARALLEL typeclass** with 2-arc signature.  This is already
documented in `Intersect_b64_exact.v` §6 (lines 1975-2068) as
`HasArcIntersect`.

### Violation 3: Snap-rounding geometry (Hobby Theorem 4.1)

`hobby_theorem_4_1_conditional` (theories-flocq/HobbyTheorem_b64.v:423)
takes `fully_intersected A` for `A : list (Point * Point)` — chord
segments.  Hobby's geometric argument (piecewise-linear ordering on
rotated coordinates) is **line-specific**.  An arc analog would need
a different snap-rounding theory — current literature doesn't have a
direct analog for arcs.

### Violation 4: Hot-pixel intersection test

`b64_passes_through_hot_pixel_halfopen` and the Liang-Barsky
parameter interval (theories-flocq/HotPixel_b64.v) test linear
segments against rectangular hot pixels.  Arc-rectangle
intersection is a different algorithm (circle-rectangle
intersection): no linear parameter interval, instead solve the
quadratic intersection of circle with each rectangle edge.

---

## §3 — Transfer / Generalize / New-Proof classification

The exhaustive per-theorem accounting for Phase 0-3 work.

### TRANSFER (structural / set-theoretic; arc-agnostic)

| Item | File | Reason |
|---|---|---|
| `Ring`, `Polygon`, `Geometry` types | theories/Overlay.v | structural; works for any closed boundary |
| `ring_closed`, `ring_simple` (predicate form) | theories/Overlay.v | depend on edge enumeration, not edge type |
| `valid_polygon`, `valid_geometry` | theories/Overlay.v | structural composition |
| `BooleanOp` enum + `boolean_op` semantics | theories/Overlay.v | pure set theory: `point_set A ∨/∧ point_set B` etc. |
| `point_set` definition | theories/Overlay.v | `exists poly, ...` — agnostic |
| `point_in_polygon` definition | theories/Overlay.v | outer ring + holes — agnostic |
| `TopologyGraph` record | theories/OverlayGraph.v | graph structure |
| `valid_topology_graph` | theories/OverlayGraph.v | structural |
| `EdgeLabel`, `merge_labels`, `merge_labeled_edges` | theories/OverlayGraph.v | labelling rules |
| `merge_in_left_iff` / `merge_in_right_iff` | theories/OverlayGraph.v | label algebra |
| `correct_labels` definition | theories-flocq/OverlayBridge.v | edge-level labelling correctness |
| `correct_labels_{union, intersection, difference, symdiff}` | theories-flocq/OverlayBridge.v | label algebra composed with set operators |
| `correct_labels_all_ops` | theories-flocq/OverlayBridge.v | case-on-op uniform composition |
| `overlay_ng_correct_conditional` shape | theories-flocq/OverlayCorrectness.v (PR #41) | conditional theorem under named gaps |

**Count: ~15 theorems / definitions transfer unchanged.**  The
structural skeleton of Phase 3 is arc-ready.

### GENERALIZE (parametric over a curve abstraction; needs new
instance per curve family)

| Item | File | Generalization shape |
|---|---|---|
| `point_in_ring` | theories/Overlay.v | ray-crossing on `ring_edges`; works if `ring_edges` produces curve-edges, not just chord-edges |
| `edge_crosses_ray` | theories/Overlay.v | linear — needs arc-aware variant for arc edges |
| `ring_edges` | theories/Overlay.v | currently produces chord pairs; needs curve-edge enumeration |
| `BPoint` (coordinate carrier) | theories-flocq/Validate_binary64_bridge.v | works for arc control points too |
| `coord_int_safe` | theories-flocq/Orient_b64_exact.v | bounds binary64 coordinate; arc params (centre, radius) need their own analog `arc_coord_int_safe` |
| `cross_R_BP` (R-side cross product) | theories-flocq/Orient_b64_R.v | three-point sign — directly reused for arc-orient as the chord case of an arc-aware orientation predicate |
| `b64_orient2d` (Stage A / Stage D filter) | theories-flocq/Orient_b64_exact.v, Orient_b64_stage_d.v | chord-case fixed; needs **parallel** `b64_orient_arc` for arc triples (per Orient_b64_exact §6 dovetail) |

**Count: ~7 items generalize via parallel definitions.**  The naming
hygiene already in place (`Orient_b64_exact.v` and
`Intersect_b64_exact.v` dovetail blocks) names the right shape.

### NEW PROOF (no straightforward generalization; new theorems)

| Item | File | What's actually new |
|---|---|---|
| `HasArcIntersect` typeclass | (NEW file in Phase 4) | parallel to `HasIntersect`, 2-arc signature |
| `arc_intersect_*` implementations | (NEW) | quadratic Cramer-like for arc-line; quartic for arc-arc |
| `b64_orient_arc_*` | (NEW) | three-point arc orientation: sign of curvature at arc midpoint |
| `arc_in_hot_pixel` / `arc_passes_through_hot_pixel` | (NEW) | circle-rectangle intersection algorithm + soundness |
| Arc analog of `fully_intersected` | (NEW) | "no two arcs intersect except at endpoints" — same iff form, but `segments_intersect_properly` replaced by `arcs_intersect_properly` |
| Arc analog of `hobby_theorem_4_1_conditional` | (NEW) | **NO published analog of Hobby's theorem for arcs** — research-grade gap |
| `arc_snap_round` + `arc_snap_noding_bridge` | (NEW) | arc snap-rounding correctness — needs new geometric argument |
| `noded_arc_labeled_graph` | (NEW) | analog of `noded_labeled_graph` for arcs |
| `correct_arc_labels_*` | (NEW) | parallel to `correct_labels_*` for arc-edge labelling |

**Count: ~9 new families of theorems.**  Three are unbounded
research gaps (arc Hobby analog, arc snap-rounding, arc fully-
intersected), six are tractable extensions assuming the predicates
are in place.

---

## §4 — The HasIntersect typeclass abstraction question

**Already answered in the corpus**.  See
`theories-flocq/Intersect_b64_exact.v` §6 dovetail (lines
1975-2068), which states:

> the 4-point signature `T -> T -> T -> T -> binary64` is
> chord-paradigm-specific (two chord-chord segments = four
> endpoints).  The arc-bearing analog needs a **parallel** typeclass
> with a 2-argument signature (two arcs, not four points), not a new
> instance of `HasIntersect`.

**Answer: HasIntersect is NOT abstract enough to accommodate arc
intersections directly**.  But the corpus's chosen architecture is
**parallel typeclasses**, not refactoring.  `HasIntersect` stays
chord-specific; `HasArcIntersect` (2-arc) and `HasClothoidIntersect`
(2-clothoid) coexist.  Bridges between them compose refinement
bounds.

**Implication**: Phase 4 does NOT need a Session 1.5 typeclass
refactor.  The first Coq work in Phase 4 (Session 2 onward) can
introduce `HasArcIntersect` as a brand-new typeclass without
touching existing proofs.

---

## §5 — Phase 4 session plan (refined)

Given the audit's findings, the **chord-approximation thesis
direction (Option B)** drives a 7-session plan; the **exact-arc
thesis direction (Option A)** is a 20+ session research program.

### Option B (chord approximation) — 7 sessions

  - **Session 1** (this): chord-overfitting audit.  **DONE.**
  - **Session 2**: `CircularArc` type definition + chord
    approximation function.  Define `arc_to_chords : CircularArc
    -> tolerance -> list Edge`.  Prove approximation distance
    bound: chord error ≤ tolerance under sagitta refinement.
    Estimated 100-200 lines.
  - **Session 3**: Bridge `arc_to_chords` output through the
    existing chord pipeline.  Show that overlay on
    chord-approximated arcs produces a Geometry whose point-set
    agrees with the original arc geometry up to `tolerance`.
    Composes with `overlay_ng_correct_conditional`.
  - **Session 4**: `valid_geometry_with_arcs` predicate — extend
    `valid_geometry` to recognise arc edges in rings + a tolerance
    parameter.  Mostly definitional.
  - **Session 5**: `Curve_overlay_correct_with_tolerance` —
    conditional theorem: chord-approximated overlay matches arc
    overlay within tolerance.  Same epistemic shape as Phase 3
    conditional headline.
  - **Session 6**: dovetail with the existing
    `NetTopologySuite.Curve` extension's `Flatten()` semantics.
    Prove the corpus's chord approximation matches NTS.Curve's
    actual implementation.
  - **Session 7**: corollaries + documentation + audit doc update.

### Option A (exact arc) — 20+ sessions

  - Sessions 2-5: predicate-layer parallel typeclasses
    (`HasArcIntersect`, `HasArcOrient`) + implementations.
  - Sessions 6-10: arc-rectangle intersection + arc-hot-pixel test.
  - Sessions 11-15: arc fully-intersected + arc snap-rounding
    theory (RESEARCH GAP — no published Hobby analog for arcs).
  - Sessions 16-20+: arc overlay pipeline + correctness.

**Recommendation: Option B.**  Three reasons:

  1. **NTS implementation already chord-approximates** (per the
     existing audit-phase4-curves.md §2-§4).  Option B mirrors the
     implementation; Option A diverges from it.
  2. **Option A has a research gap** (arc snap-rounding) that's
     comparable in shape to the hobby_lemma_4_3_no_proper deferred
     entry — thesis-scale, 4-6 weeks if not multi-month.
  3. **Reuses ~15 theorems unchanged** (the TRANSFER list in §3) +
     7 with parallel definitions (GENERALIZE list).  ~70%
     infrastructure reuse vs Option A's ~30%.

This is the load-bearing decision before Session 2.

---

## §6 — Resumption checklist

  - [ ] Read SQL/MM Spatial ISO/IEC 13249-3 §4 (CIRCULARSTRING
        definition) before Session 2.  Specifically: **three
        control points (start, on-arc, end) define a unique
        circular arc on the minor side**.  The unique-circle-
        through-three-points algorithm is the canonical
        constructor.
  - [ ] Confirm HasIntersect abstraction question is settled
        (**done** — answer in §4: parallel typeclasses, no
        refactor).
  - [ ] Check NTS SnapRoundingNoder for arc handling: it
        chord-approximates before noding (per audit-phase4-curves.md
        §2).  Implication: Option B is the right thesis direction.
  - [ ] Check whether Fortune-Van Wyk error bounds extend to
        degree-4 arc intersection.  **Action**: postpone to
        Session 4-5 if Option A is chosen; not relevant to
        Option B.
  - [x] **STRATEGIC DECISION before Session 2** — **CONFIRMED
        2026-05-29: Option B (chord approximation, 7 sessions).**
        Exact arc geometry (Option A, 20+ sessions, includes
        research gap) deferred to a potential Phase 5 contingent on
        downstream demand.
  - [ ] After Session 7 (or whichever Phase 4 endpoint),
        re-evaluate whether downstream consumers (NetTopologySuite,
        upstream JTS PRs) are asking for exact arc support.  If
        yes, the Option A research program can be initiated as a
        follow-up Phase 5.

---

## §7 — Strategic-decision summary

The decision flagged in §6 (Option A exact arc vs Option B chord
approximation) is the load-bearing question for Phase 4.

**DECISION (2026-05-29): Option B confirmed.**

```
═══════════════════════════════════════════════════════════════
  DECISION CONFIRMED 2026-05-29:
    Option B (chord approximation, 7 sessions).
═══════════════════════════════════════════════════════════════

Rationale:
  - Mirrors NTS implementation (Flatten() at every overlay call).
  - Reuses 70%+ of Phase 0-3 infrastructure (TRANSFER + GENERALIZE).
  - Avoids the arc-Hobby research gap (thesis-scale).
  - Provides the same epistemic guarantee NTS users actually get
    today: arc operations are correct up to chord approximation
    tolerance.

When to choose Option A:
  - Downstream consumer asks for exact arc support (NTS upstream
    PR, PostGIS exact-arc feature, JTS native-arc proposal).
  - Budget appears for the arc snap-rounding research piece (~6
    months focused).
  - Tripwire from audit-phase4-curves.md §5 fires (re-evaluate
    around 2031).
═══════════════════════════════════════════════════════════════
```

**Decision recorded 2026-05-29: Option B (chord approximation).**
The 7-session plan in §5 is now the committed Phase 4 program.
Session 2 (CircularArc type + chord approximation function) is
the next concrete deliverable.

---

## §8 — What this session produced

  - This document (`docs/audit-phase4-chord-overfitting.md`).
  - Complements `docs/audit-phase4-curves.md` (strategic scoping,
    architecture diagnosis, tripwire) with **theorem-by-theorem
    classification** (~15 TRANSFER, ~7 GENERALIZE, ~9 NEW PROOF).
  - Confirms the HasIntersect abstraction question (parallel
    typeclasses, no refactor needed).
  - **Records the load-bearing Option B decision (chord
    approximation, 7 sessions).**  Phase 4 program now committed;
    Session 2 ready to start.

No `.v` changes.  No Admitteds.  Registry: unchanged.
