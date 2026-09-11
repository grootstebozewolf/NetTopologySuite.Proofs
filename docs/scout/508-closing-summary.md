# #508 closing summary — owner sign-off requested

claimId: `508-h` · witness: `508-h-wrap-up`

This is the wrap-up letter for
[#508](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/issues/508).
It does **not** retire the epic. Owner review retires it.

Bible §4.2 `length()` is discharged in the ledger sense below: each zoo
member has a named theorem against `CurveLength.v : is_curve_length`,
or a named park. This is not "the zoo is unconditionally exact."

**Merge comment (one sentence).** `M-LEN-ZOO` ✅ is paperwork-with-parks:
clothoid unconditional is the unit line, ellipse unconditional is
`rx=ry`, Bézier is an upper bound not `length()`, NURBS additivity is a
list of already-proved spans — not a multi-span NURBS and not "the zoo
is exact."

## Destination (met with the named parks)

The canonical spec is `is_curve_length` (inscribed-polyline lub).
CircularArc `r·θ` meets it. Waypoint additivity and the
reparam/reflect kit are theorems. Equal-weight NURBS collapses onto
Bézier. The golden rational quarter is Category C (`atan`). Knot-list
additivity is induction over `curve_length_additive`, not Cox-de Boor.

A park stays a park where named: elliptic E remains
`increment_squeezed` with **no inhabitant**. Fresnel clothoid now has
a Stdlib-RiemannInt inhabitant (`ClothoidFresnelInhab.v`; Category C;
board #564). Year-1 `CurveSegment` is `CSChord` or `CSArc`. QEX
(`ExactCurveEpic508.v : ticket_508_qed_or_qex`) is not owner accept.

## Bible §4.2 satisfaction — which theorem per zoo member

| Zoo member | What `length()` is | Pin | Regime |
|---|---|---|---|
| CircularArc | `r·θ` is the metric length | `ArcRectifiable.v : arc_r_theta_is_curve_length` | unconditional |
| CircularArc (3-point) | principal sweep on the circumcircle | `ArcParamBridge.v : arc_sweep_param_bridge` | Category C (`atan2`) |
| Aggregation | `L(a,c) = L(a,b) + L(b,c)` | `CurveLength.v : curve_length_additive` | unconditional |
| Reparam / reflect | monotone and orientation-reversing invariance | `CurveLength.v : is_curve_length_reparam`, `CurveLength.v : is_curve_length_reflect` | unconditional (#560) |
| Cubic Bézier | `L ≤` control-polygon length on `[0,1]` | `Bezier3Polygon.v : bezier3_length_le_polygon` | unconditional ceiling, not a closed form |
| Ellipse `rx=ry` | circular discharge `E(t)=r·t` | `EllipseLength_E.v : ellipse_circular_E_discharges` | unconditional on the circle |
| Ellipse general | pack at `E b − E a` | `EllipseSpeedIntegral.v : ellipse_speed_integral_is_curve_length` | engine-conditional (`increment_squeezed`) |
| Clothoid (unit line) | unit-speed straight on `[sd,ed]` | `ClothoidLength_unit.v : unit_line_discharges_window` | unconditional as a straight line |
| Clothoid (Fresnel) | pack at `b − a`; inhabitant length `1` on `[0,1]` | `ClothoidFresnel.v : fresnel_is_curve_length`; `ClothoidFresnelInhab.v : fresnel_unit_window_length_inhab` | pack engine-conditional; inhabitant Category C (#564) |
| Single-span NURBS (golden) | unit quarter = `π/2` | `NurbsConicExact.v : nurbs2_golden_quarter_length` | Category C (`atan`) |
| NURBS ⊃ Bézier | equal weights collapse the denominator | `NurbsQuadraticLength.v : nurbs2_equal_weights_cubic`, `NurbsGeneralLength.v : nurbs3_equal_weights_length` | unconditional inclusion |
| NURBS knot list | span lengths sum | `NurbsKnotSpans.v : nurbs_spans_additive` | unconditional additivity; not Cox-de Boor |
| NURBS two-quarter instance | `π/2 + π/2 = π` | `NurbsConicExact.v : golden_half_circle_length` | two glued 508-a quarters; not a new `π` theorem |

Speed-integral pack (the method, not a zoo member):
`SpeedIntegral.v : speed_integral_is_curve_length`. Bernstein plumbing:
`BernsteinBasis.v : bern_elevate_2`. Neither remints the others.

## Named, not proved / not a #508 child

These are not holes in the original length ask. Do **not** remint
closed letters. Do **not** mint `508-i`.

- **Cox-de Boor multi-span evaluation.** 508-g is knot-list additivity
  plus two glued `nurbs2_param`s. Oracle `N` stays single-span.
  `NurbsGeneralLength.v : nurbs_knot_span_additive` stays the
  two-window special case.
- **Elliptic-E inhabitant.** Technique-park `increment_squeezed`. Do
  not remint `EllipseSpeedIntegral.v`. Fresnel inhabitant is
  `ClothoidFresnelInhab.v` (#564); do not remint the pack
  `ClothoidFresnel.v`.
- **Exact\* zoo types / `CurveSegment` growth.** ADR-0004. Year-1
  engine stays circular-only. QEX recorded the missing constructors.
  QEX is not owner accept.
- **Oracle `LENGTH_UNIFIED` E/B/K/N mint.** Still C/A on the wire.
  ISO 13249-3 projections stay owed.
- **Bible §2.6 densify ≤1.15×.** Implementation-side laser ratchet,
  not a proof obligation.
- **Orientation.** Handled by #560 (`is_curve_length_reflect`).

## Surfaces that must agree

- TRIAGE row: `TRIAGE_NTS_JTS_ISSUES.md` `M-LEN-ZOO`
- Ledger: `docs/verified-claims.md` `#566` / `508-h` paragraph
- Observatory: `docs/508-pstar-rungs.md`
- Glossary: `CONTEXT.md` Metric length

Prose gate: `scripts/validate-claims.sh` over `docs/gated-prose-docs.txt`.

Owner: retire #508 after review if this scope is the accept. This
letter does not close it. Satisfaction lives here; do not treat a
GitHub issue comment as the source of record.
