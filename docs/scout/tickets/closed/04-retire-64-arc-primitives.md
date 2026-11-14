<!-- doc-kind: finding
date: 2026-08-22
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# Retire #64 — arc primitives

**Type:** grilling · **Map:** [Retire the epic block #64–#69](../../map-epic-block-64-69.md)
**Blocked by:** — · **Closed:** 2026-08-22

## Question

#64 (Immediate) asks for arc length, sweep, point-on-arc, in-circle, arc-line and
arc-arc intersection, plus oracle modes. The audit reads it **MOSTLY** satisfied:
three of the body's four round-2 items have closed since the body was written.
Does it close, and where does its residue go?

Satisfied (verify then cite): D-PT distance clamps fully closed
(`fallback_ends_lower`, `arc_dot_max_at_endpoint`); span discharge unconditional
for all sweeps including reflex (`theories/ArcSpanAtan2.v`); the arc-arc quartic —
the body's own "deepest open work" — closed in `theories/ArcArcQuartic.v`
(`arc_arc_intersects_of_atan2_radical_span:316`). Asks 1/2/4b/5a green via
`ArcLength.v`, `Atan2.v`/`AngleBetween.v`, `InCircle_b64_exact.v`,
`ArcLineIntersect_b64_exact.v` (`verified-claims.md:480-483`). New micro-claims
64-b/c/d/e exist and are not in the body at all.

Residue to place, per the closure bar — subtask, new epic, or documented non-goal:

1. **V-CP true-region (Jordan) soundness** — `CurvePolygonValid.v` has only the
   inscribed-chord floor, and #376's survey says the triangle-only toolkit cannot
   discharge it: genuinely new ray-vs-arc crossing geometry is needed. Flagged
   high-risk; this one plausibly deserves its own epic rather than a subtask.
2. `ArcOverlay.v : arc_overlay_correct_chord_approx` — two bridge hypotheses.
3. The permanent interface caveat for float modes `ARC_DISTANCE`,
   `POINT_IN_CURVE_RING`, `RING_ORIENTATION` (transcendental sweep clamp) — a
   documented convention, not closable work. Decide where it is written down so
   it stops reading as residue.

## Resolution

**Closed 2026-08-22. #64 closed on circular-arc scope; residue placed across
four new issues; one correctness trap and one register defect found on the way.**

**Three of #64's four round-2 items had closed since its body was written** —
distance clamps, the span discharge (`ArcSpanAtan2.v:356`, verified to have no
`Section`/`Hypothesis` anywhere in the file, so reflex sweeps are genuinely
covered) and the arc-arc quartic (`ArcArcQuartic.v:316`, the body's own "deepest
open work"). Item ③, V-CP true-region, was already labelled "stretch only".

**The scope question the maintainer raised changed the shape of the answer.**
Exact length is *not* satisfied in the sense the JTS Arc-Native Programme needs:
`doc/EXACT_CURVE_BIBLE.md` §4.2 puts `double length()` on the thin `ExactCurve`
protocol, so every zoo member owes one — and §4.1 names them:
`ExactCircularArc`, `ExactQuadraticBezier`, `ExactEllipticalArc`,
`ExactClothoid`, `ExactNurbsSegment`. #64's *written* ask (`r·θ` for
control-point arcs) is satisfied; the zoo obligation is new surface, so it became
its own epic rather than pinning an `Immediate` epic open behind NURBS.

Two facts worth carrying forward, both of which contradicted assumptions:

- **The length oracle already exists.** `LENGTH_UNIFIED` (`driver.ml:3140`)
  implements CC/CP/Multi aggregation — and has **no Coq companion at all**
  (`grep LENGTH_UNIFIED theories/ theories-flocq/` → nothing). Its parser also
  `failwith`s on `E`/`B` tokens (:3148), so two thirds of the zoo cannot even be
  *measured* today, let alone proven.
- **`TRIAGE_NTS_JTS_ISSUES.md:87` marks M-LEN-CS/CC ✅**, and no wishlist asks
  for length. #508 reopens that row deliberately.

**Residue placed:**

| Issue | Carries |
|---|---|
| **#508** | Exact length across the ExactCurve zoo — Bible §5 order (Quadratic Bézier → Ellipse → Clothoid → single-span NURBS), oracle first. Note the quadratic Bézier *is* a parabolic arc, so its length is closed-form; the corpus's `Bezier3Chord` is **cubic** and not this type. |
| **#509** | V-CP true-region (Jordan) soundness — own epic per #376's survey. The floor is weaker than the ticket implied: `Overlay.hole_inside_outer` is a **single-vertex** witness. |
| **#510** | The three arc conditionals, one issue: `ArcOverlay` (two region-level bridge hypotheses the file itself calls false for large polygons), `ArcChordSound`, `ArcArcSound`. |
| **#511** | Elliptic arcs are a silent **no-op** in `RING_ORIENTATION` (contributes zero signed area) and `POINT_IN_CURVE_RING` (counts zero crossings) — a Bible §2.2/§2.3 violation, and worse than hidden linearisation since it approximates nothing. |
| **#503** | Widened to claims-register accuracy: `verified-claims.md:423` calls the conditional `arc_overlay_correct_chord_approx` an "Unconditional headline"; 64-c has no row. Two mechanical gate rules proposed, with the 36-row triage cost measured. |

**The float-mode caveat was already documented**, contrary to the ticket's
premise — per-mode in `docs/oracle-handrolled-allowlist.txt` (:122-129, :291-303,
:305-316) and mirrored in the `driver.ml` headers. It was missing only from
`oracle/CONSUMERS.md`, which now carries an *Interface-boundary modes* section
pointing at the per-mode entries and naming the `*_INVARIANTS_EXACT` preference
plus the `ARC_SHORTER` decline-rather-than-round idiom.

**Not resolved here, and deliberately left as fog:** the maintainer's
CurvePolygon kit-completeness ask (CUP/CAP/XOR/SUB plus a T-in/T-out Dim9
extension). Bible §8 settles what "kits" means — the **laser kits**
(OverlayNGCurve, CurveExact, MIC/LEC, metrics, DE-9IM), *not* the corpus's seven
`*Kit*.v` JCT files — but "T-in / T-out" is vocabulary this corpus does not have
(`theories/Tin.v` is Triangulated Irregular Networks, a false friend), and
"complete" has a **refuted ancestor**:
`OverlayTouchRow.v:225 phase0_relation_complete_hypothesis_refuted` proves the
7-row family incomplete because the external kiss is a genuine 8th row. Cannot
be ticketed sharply until both are defined.
