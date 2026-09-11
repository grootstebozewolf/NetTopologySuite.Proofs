# #508 Phase 7 — P* rungs

Observatory note for Proofs #508 remaining rungs (Notion plan
[Implementation Plan: Proofs 508 ExactCurve zoo length](https://app.notion.com/p/3ca1c9833b0681809eb6f43b905cb946)).

`claimId: none` at the epic.  HOLDs (CurveSegment rewrite, Exact\* zoo
types, ADR-0004 remint) are untouched.  Year-1 engine stays circular-only.

| Priority | Lane | File | Headline | Status |
|---|---|---|---|---|
| P0 | bezier | `theories/Bezier3Polygon.v` | `bezier3_length_le_polygon` — L ≤ control-polygon length on [0,1] | Qed, 3-axiom |
| P1 | ellipse | `theories/EllipseLength_E.v` | `ellipse_circular_E_discharges` — rx=ry inhabits H_E_chord / H_E_approx at E(t)=r·t; general elliptic-E parked | Qed + Technique park, 3-axiom |
| P1 | ellipse | `theories/EllipseSpeedIntegral.v` | `ellipse_speed_integral_is_curve_length` — UC + chord-rate of √σ²; increment_squeezed E σ is the remaining primitive | Qed + Technique park, 3-axiom (#563 / 508-d) |
| P1 | clothoid | `theories/ClothoidLength_unit.v` | `unit_line_discharges_window` — unit-speed straight inhabits the [sd,ed] contract; Euler-spiral integrals stay Route-1 primitives | Qed + Technique park, 3-axiom |
| P1 | clothoid | `theories/ClothoidFresnel.v` + `ClothoidFresnelInhab.v` | pack `fresnel_is_curve_length` (3-axiom conditional); inhabitant `fresnel_unit_window_length_inhab` via Stdlib RiemannInt of (cos,sin)(t²/2) — `[0,1]` length 1 | Qed + inhabitant, Category C (#564 / 508-e) |
| P1 | nurbs | `theories/NurbsGeneralLength.v` | equal-weight rational cubic ↔ cubic; two-window `nurbs_knot_span_additive`; conditional primitive | Qed, 3-axiom |
| P1 | nurbs | `theories/NurbsKnotSpans.v` | `nurbs_spans_additive` — knot-vector induction (3-axiom). Instance `NurbsConicExact.v : golden_half_circle_length` (two 508-a quarters, Category C) | Qed, 3-axiom additivity / Category C instance (#565 / 508-g) |
| P2 | arc | `theories/ArcMidSweep.v` | `valid_arc_sweep_nonzero`; `arc_mid_on_circle_param` | Qed, Category C (atan2; removal tracks AngleBetween) |
| — | framework | `theories/BernsteinBasis.v` | `bern_partition`; `bern_elevate_2` (n=2 instance of `elevate_ctrl`); `bezier3_elevation_pointwise` re-proved through it | Qed, 3-axiom (#562 / 508-f) |
| — | stop | `theories/ExactCurveEpic508.v` | `ticket_508_qed_or_qex` — zoo-on-CurveSegment (QED) or missing constructor (QEX); discharged QEX on the ellipse | Qed, 3-axiom (508-qed-qex) |
| — | wrap-up | `docs/scout/508-closing-summary.md` | TRIAGE `M-LEN-ZOO` ✅ with scope notes; Bible §4.2 satisfaction | paperwork (#566 / 508-h); does not retire #508 |

Oracle `B` stays 8-coord cubic.  `red_length_unified_zoo_tests.py` is
untouched.  No new 64-a r·θ definition.

## 508-c spike (#561)

Route 1 (in-corpus).  `theories/SpeedIntegral.v` packages

`uniformly_continuous_on σ` + `increment_squeezed F σ` + `chord_rate_tight g σ`

over tagged partitions (`chain` + one tag per gap, `riemann_sum`) and
proves `speed_integral_premises → is_curve_length g a b (F b − F a)`.

Heine–Cantor is **not** imported — uniform continuity stays a
hypothesis (3-axiom allowlist).  Coquelicot / `RInt` (Route 2) is
gated off this letter; host-lane metric files stay 3-axiom.  508-d
(elliptic E) and 508-e (Fresnel) instantiate the pack.

## 508-d (#563)

`theories/EllipseSpeedIntegral.v` instantiates the pack on
`ellipse_speed rx ry = √(rx² sin² t + ry² cos² t)`.  Uniform
continuity is Hölder 1/2 (`|σ(t)−σ(s)| ≤ √(K·|t−s|)`).  Chord-rate
uses the exact identity `dist = 2|sin(gap/2)|·σ(mid)`.  Route 1 does
**not** construct the incomplete elliptic integral — `increment_squeezed`
stays the Technique-park hypothesis.  Witness: any such E on the
`rx=3, ry=4` quarter lies in `[3π/2, 4π/2]`.  Does not retire epic 508.
Wrap-up is #566.  Does not remint SpeedIntegral.

## 508-e (#564)

`theories/ClothoidFresnel.v` is a #561 pack instance on the
clothoid-shaped integrands `(cos,sin)(t²/2)`: under
`fresnel_primitives` (`increment_squeezed` on each coordinate),
`fresnel_is_curve_length` gives length `b − a`. Heading `t²/2` is
Lipschitz on a compact window; `chord_rate_tight` discharges.
Uniform continuity of `σ ≡ 1` and pack `F = fun t => 1 * t` are
free. Never global. 3-axiom.

`theories/ClothoidFresnelInhab.v` supplies the concrete inhabitant
`fresnel_Cx` / `fresnel_Cy` as Stdlib `RiemannInt` of those
integrands from 0 (Route 1 / in-corpus; ADR-0001 Coquelicot lane
stays consumer-gated for Halley). Then
`fresnel_primitives_inhab` is unconditional for every `a ≤ b`, and
`fresnel_unit_window_length_inhab` is metric length exactly `1` on
`[0,1]`. Category C via `RiemannInt` → `classic`. Does not remint
`ClothoidFresnel.v`. Does not retire epic 508. Wrap-up is #566.

## 508-f (#562)

`theories/BernsteinBasis.v` consolidates the Bernstein / rational
plumbing that lived in `Bezier3Length.v`, `NurbsQuadraticLength.v`,
and `NurbsGeneralLength.v`.  Public names stay (`bern2_*`, `bern3_*`,
`bezier3_c0/c1/c2`, `norm_triple_le`, `nurbs2_den_lb`).  Elevation
exactness is the n=2 instance of `elevate_ctrl` via `bern_elevate_2`.
Non-negativity is `Rmult_le_pos` / `lra` — Flocq 4.2.1 `nra` cannot
find a cubic witness (CI death on 48a5c3f). Does not retire epic 508.
Wrap-up is #566.

## 508-g (#565)

`theories/NurbsKnotSpans.v` is the n-span knot-vector carrier.
`nurbs_spans_additive` inducts on interior knots over
`curve_length_additive`.  It does not remint
`NurbsGeneralLength.nurbs_knot_span_additive` (two-window special
case).  Not Cox-de Boor.  Oracle `N` stays single-span.  Instance
`NurbsConicExact.v : golden_half_circle_length` glues two 508-a golden quarters
(`π/2 + π/2 = π`); Category C through `atan` only.  Does not
retire epic 508.  Wrap-up is #566.  Board #564 inhabitant landed.

## 508 QED ∨ QEX stop

`theories/ExactCurveEpic508.v` is the ticket-named stop (same shape
as #522 / #523). QED is zoo-on-`CurveSegment`. QEX is a documented
missing constructor. Discharged QEX on the ellipse — the issue's
carrier blocker (`CSChord | CSArc`). Chord and circular-arc inhabit;
every inhabitant is one of those two. Not a `CurveSegment` remint.
Not an Exact* zoo type. QEX is not owner accept. Does not steal
508-e / 508-g / 508-h. Wrap-up is #566.

## 508-h (#566)

Wrap-up letter. TRIAGE `M-LEN-ZOO` flips to ✅ with honest scope
notes. Bible §4.2 satisfaction is
[`docs/scout/508-closing-summary.md`](scout/508-closing-summary.md).
Does not remint `NurbsKnotSpans.v : nurbs_spans_additive` or
`NurbsConicExact.v : golden_half_circle_length`. Does not remint
`SpeedIntegral.v` / `ClothoidLength_unit.v` / `ClothoidFresnel.v`.
Fresnel inhabitant is a later #564 letter (`ClothoidFresnelInhab.v`).
QEX is not owner accept. This letter does
not retire epic 508. Owner review does.
