# Issue #64 — Arc primitives for JTS curve awareness: research & gap triage

> **Status:** research/reading pass only (no Coq written). Maps issue #64's
> five asks against the existing corpus, separates *proven* from *gap*, and
> proposes a risk/cost-ordered plan. Branch: `claude/issue-64-research`.
>
> Every file:line citation below was verified by direct grep against the tree
> at the time of writing (corpus HEAD = `main` after PR #72).

## 1. What #64 asks for

Issue #64 ("Immediate") requests mechanically-verified proofs of circular-arc
primitives to back the JTS curve-awareness epic (locationtech/jts#1195) and a
long list of buffer/validity/overlay issues. The five concrete asks:

1. **Exact arc length** `s = r·θ` for control-point sequences.
2. **Central angle / sweep** — robust, atan2-based, picking the short/long arc
   via a mid-point.
3. **Point-on-arc** tests and **chord-arc** relations.
4. **In-circle** tests involving arcs (`b64_inCircle`) for validity — V-CP arc
   self-intersection.
5. **Arc-arc / arc-line intersection parameters** (N-AA, N-AL, overlay,
   predicates).

## 2. Strategic context already on record

Phase 4 of this corpus deliberately chose **Option B (chord approximation)**
over **Option A (exact arc analytic primitives)** as the path for arc support
(`docs/audit-phase4-curves.md`; chord-overfitting audit confirmed 2026-05-29).
Under Option B an arc is handled via its chord polyline + a *sagitta*
(perpendicular-distance) error bound, never via an explicit angle or arc-length
number. This decision is the single most important lens on #64: **asks #1 and
#2 are exactly the Option-A primitives Option B was chosen to avoid.**

A second hard constraint: **Stdlib `Reals` ships no `atan2`.** `theories/Azimuth.v:12-13`
and `theories/PointInRingCorrect.v:421-428` both record that only `Ratan : R→R`
exists; a two-argument `atan2 : R→R→R` would require Coquelicot or
mathcomp-analysis (an ecosystem/axiom-footprint shift), which the corpus has so
far declined. Ask #2 (atan2-based sweep) inherits this blocker.

## 3. Per-ask status

| Ask | Status | Anchor (file:line) | Notes |
|---|---|---|---|
| **#1 Arc length `r·θ`** | **ABSENT** | — | No `arc_length`/`sweep`/`central_angle` definition anywhere in `theories/` or `theories-flocq/`. Not required by Option B (which uses sagitta, not θ). |
| **#2 Central angle / sweep (atan2)** | **ABSENT (blocked)** | `Azimuth.v:73`, `PointInRingCorrect.v:426-428` | No `atan2` in Stdlib Reals; 22 mentions, all comments documenting its deliberate absence. Arc-span instead decided by chord cross-product sign (Option S, `arc_span_contains`), correct only for arcs < π. |
| **#3a Point-on-arc / orientation** | **PROVEN (Qed)** | `ArcOrient.v:89` (`inCircle_R`), `:170` (`arc_interior_side_mid`), `:183` (`arc_orient_mid`) | Structural predicates + mid-point side closed. 3 standard axioms. |
| **#3b Chord-arc crossing (existence)** | **PROVEN (Qed)** | `ArcIntersectIVT.v:174` (`chord_crosses_arc_circle_implies_circle_intersection`) | IVT: opposite `inCircle_R` signs at chord ends ⇒ ∃ point on chord with `inCircle_R = 0` (on the circumcircle). |
| **#3c Chord-arc *soundness*** | **GAP (absent, quarantined)** | `phase4-retro.md:34`; named `arc_chord_intersect_sound` | Promoting "circle crossing" → "arc-span crossing" (minor vs major arc) is **not written** — quarantined behind a predicate, *not* an `Admitted`. The arc `theories/` files are Admitted-free. |
| **#4a in-circle predicate + algebra** | **PROVEN (Qed)** | `ArcOrient.v:89,205` + 8 invariance lemmas (swap/cyclic/translation/scaling/rotation) | `inCircle_R` defining-point zeros and similarity invariants all closed. |
| **#4b `b64_inCircle` soundness** | **GAP (deferred)** | `InCircle_b64_compute.v:33`; `oracle-handroll-migration.md` items 2-3 | Extractable b64 mirror exists; the rounded-value → R-sign exactness theorem is unwritten (no `Admitted`, just absent). |
| **#4c Arc validity (V-CP)** | **PARTIAL** | `ArcHotPixel.v:95` (`arc_passes_through_hot_pixel`), `:124` (`arc_touches_hot_pixel`) | Endpoint disjuncts + 6 disjunct-intro lemmas Qed; edge-crossing soundness rides on #3c. |
| **#5a Arc-line intersection** | **PREDICATE PROVEN; coords ABSENT** | `ArcIntersect.v:90,129` | Existence predicate + sufficient sign-filter proven; no coordinate-extraction theorem. |
| **#5b Arc-arc intersection** | **PREDICATE PROVEN; coords ABSENT** | `ArcIntersect.v:104` | Existence predicate Qed; exact coordinates are a quartic (research-grade), absent. |
| **#5c Arc overlay correctness** | **CONDITIONAL (Qed)** | `ArcOverlay.v` headline `arc_overlay_correct_chord_approx`; bridges `ArcOverlay.v:123,147-152` | Headline Qed under two "every chord point is close to an arc" bridge hypotheses (`H_A_bridge`/`H_B_bridge`), flagged "PRACTICALLY DEMANDING". |

## 4. Inventory of existing arc assets

**R-side (`theories/`, 3 standard axioms, Admitted-free):**
- `CurveGeometry.v` — SQL/MM types (`CircularArc`, `CurveSegment`, `CurveRing`,
  `CurvePolygon`, `CurveGeometry`) + validity + chord-approx bridge.
- `ArcOrient.v` — `cross_R_pt`, `inCircle_R` (`:89`), arc orientation trichotomy
  (`arc_orient`), 11 Qed lemmas (mid-point side + in-circle sign algebra).
- `ArcIntersect.v` — `arc_span_contains` (`:77`), `arc_chord_intersects` (`:90`),
  `arc_arc_intersects` (`:104`), `chord_crosses_arc_circle` (`:129`) + 6 Qed
  symmetry/boundary lemmas.
- `ArcIntersectIVT.v` — `chord_point`, `inCircle_along_chord`, IVT theorem (`:174`).
- `ArcHotPixel.v` — `arc_passes_through_hot_pixel` (`:95`), `arc_touches_hot_pixel`
  (`:124`) + 8 Qed structural lemmas.
- `ArcChordApprox.v` — `arc_center_equidistant` (`:48`), sagitta foundations,
  `sagitta_le_arc_radius` (15 Qed lemmas).
- `ArcOverlay.v` — conditional overlay headline + 6 Qed structural lemmas.
- `Azimuth.v` — direction tooling; explicitly *no* `atan2`.

**Flocq layer (`theories-flocq/`, +`Classical_Prop.classic`):**
- `InCircle_b64_compute.v:33` — `b64_inCircle` (extractable determinant).
- `ArcCircle_b64_compute.v` — `b64_chord_crosses_arc_circle` (extractable
  sufficient filter; SUFFICIENT-only, soundness deferred).
- `ArcPixel_b64_compute.v` — `b64_in_hot_pixel_halfopen`,
  `b64_arc_passes_through_hot_pixel` (extractable).

**Oracle (`oracle/driver.ml:760-763`):** modes `INCIRCLE_SIGN`,
`INCIRCLE_EXACT`, `ARC_CHORD_CROSSES_CIRCLE`, `ARC_PASSES_THROUGH_PIXEL`;
extraction validated bit-exact in `oracle/test_arc.ml`.

## 5. The genuine gaps, by nature

1. **Two true absences (asks #1, #2):** arc length `r·θ` and atan2 sweep. These
   are Option-A primitives; the corpus chose Option B and Stdlib lacks `atan2`.
   Building them is a *strategic reversal*, not an incremental proof — needs a
   scope decision + likely a Coquelicot/half-angle angle representation.
2. **One analytic soundness gap (asks #3c, #4c):** `arc_chord_intersect_sound`
   — promoting circle-crossing to *arc-span* crossing. Quarantined behind a
   predicate (not an Admitted). Blocked on the minor/major-arc disambiguation,
   which itself wants the Option-S `arc_span_contains` extended past π — circular
   with the atan2 gap.
3. **One rounding-soundness gap (ask #4b):** `b64_inCircle` sign-exactness vs
   `inCircle_R` (integer/bounded regime). This is the *same shape* as the
   orientation `b64_orient2d_exact` work already done — a known, tractable
   pattern, just unwritten.
4. **Coordinate extraction (ask #5):** predicates exist; explicit intersection
   coordinates do not. Arc-line is a quadratic (tractable); arc-arc is a quartic
   (research-grade). Option B does not need either.

## 6. Risk/cost-ordered options for the next (Coq) terminal

Ordered cheapest/highest-confidence first, matching the corpus's clearlane
discipline (drive to a Qed or a validated counterexample; pivot off costly
lanes):

- **(A) `b64_inCircle` sign-exactness on integer coords** — *low risk, high
  value.* Direct analogue of the proven `b64_orient2d_exact_for_small_int`
  pattern; closes ask #4b and hardens the V-CP / INCIRCLE oracle. The single
  best Qed terminal here.
- **(B) Arc-line intersection *coordinates* (quadratic)** — *medium.* The
  circle∩chord root formula with a forward-error bound, mirroring
  `Intersect_b64_exact`. Advances ask #5a beyond the existence predicate.
- **(C) `arc_span_contains` correctness for arcs ≥ π** — *medium-high.* Would
  unblock the #3c soundness chain *without* atan2 if a sign/midpoint argument
  can replace angular ordering; risk is it genuinely needs angles.
- **(D) Arc length `r·θ` / atan2 sweep (asks #1, #2)** — *high / strategic.*
  Requires a scope decision (Option A revival) and probably a new angle
  dependency. **Pivot away** unless the user explicitly wants exact arc
  primitives rather than Option-B completion.

## 7. Open scope question for the issue owner

#64 lists both Option-A primitives (arc length, atan2 sweep) and Option-B
completion items (in-circle soundness, intersection coordinates). The corpus
has committed to Option B. **Which does #64 actually want?**

- *Option-B completion* → start with (A) then (B); fully tractable, no new
  axioms.
- *Option-A exact arc primitives* (#1/#2) → needs an explicit angle
  representation (Coquelicot `atan2` or a half-angle/sine-cosine encoding) and
  an axiom-footprint decision before any proof is attempted.

Recommendation: confirm Option-B completion and beeline (A) `b64_inCircle`
sign-exactness as the first Qed terminal, holding (D) until the scope is
explicitly chosen.

## 8. Update (Option-A chosen): atan2 foundation landed

The issue owner selected **Option-A** with the **atan2-from-Stdlib-`Ratan`**
angle foundation. First terminal delivered: `theories/Atan2.v` —
`atan2 : R→R→R` (JTS `Math.atan2(y,x)` convention, range (-π, π]) with the two
load-bearing characterisation theorems `cos_atan2` / `sin_atan2`
(`cos(atan2 y x) = x/r`, `sin = y/r` for `(x,y)≠0`), plus `atan2_on_circle`.
All Qed, no Admitted.

**Empirically confirmed axiom cost (corrects an earlier estimate).** Building
atan2 needs **no new opam dependency** (pure Stdlib), but it is **4-axiom, not
3**: Stdlib's `atan` pulls `Classical_Prop.classic` (verified directly —
`atan_0` surfaces `classic`, while `cos_0` / `sqrt_1` do not). So every
atan2-based primitive (sweep, arc length `r·θ`) inherits `classic`. The
declined implicit-(sin,cos) representation would have stayed 3-axiom — this is
the concrete trade-off of the JTS-faithful choice. `theories/Atan2.v` is
registered in `docs/audit-exceptions.txt` (R-side `classic` lineage, distinct
from the Flocq-float files) and `docs/verified-claims.md` (Phase 4).

**Next terminals (Option-A):** central angle / sweep on three control points
(short-vs-long via the proven mid-point side test), then arc length `s = r·θ`
with `θ` the central angle from `atan2`.
