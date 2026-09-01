# Chart CURVEPOLYGON type honesty

**Type:** grilling · **Map:** [CURVEPOLYGON](../../map-curvepolygon.md)
**Claimed:** wayfinder 2026-09-01 · **Closed:** 2026-09-01
**Blocked by:** —
**claimId:** none · **GitHub:** none · **witness:** none

No dedicated board card. Sibling FCP-S is I/O. Sibling CRV-CC is
COMPOUNDCURVE flatten-elimination (this packet; tickets 29 / 30).

## Question

What does `/wayfinder CURVEPOLYGON` own? Name what is already true,
park what is HOLD, and leave one named leftover so the next session
cannot steal `#509`, steal ticket 30, or invent a second type.

## Resolution

**Grilled 2026-09-01. Living record:
[`docs/scout/map-curvepolygon.md`](../../map-curvepolygon.md).**
This ticket does not implement silent-polygon-collapse.

**Already true.** HELP and READING-GUIDE name CURVEPOLYGON (ISO/IEC
13249-3) and that Flatten-to-chords is lossy. The Coq carrier is
`CurveGeometry.v : valid_curve_polygon` (structural). Named linearise
is `CurveLinearise.v : to_geometry_outer_ring_closed`. NTS rings stay
`Curve`. JTS `getExteriorRing()` is named Option A; the true shell is
`getExteriorCurve()`. V-CP Jordan stays on `#509`. Kit-completeness
stays fog (`OverlayTouchRow.v : phase0_relation_complete_hypothesis_refuted`).

**Three words.** Silent POLYGON collapse is the leftover. Named
`Linearize` / `toLinear` / `chord_approx_ring` is allowed. Structural
F-CP / Jordan true-region is already named (`#509`).

**Parks.** JTS #27 out. JTS #38 (Option C DCEL) off #7. No public
noder. HOLD merge into #7. HOLD a second CurvePolygon type. HOLD
implement for ticket 32 (no Architect SIGN). No type-10 reader PR.
No GEO-TIN 15–17. No DOI. Cite 13249-3 only.

**Frontier.** Ticket 32 names the leftover. HOLD implement stands.
Do not `/implement` from this letter.
