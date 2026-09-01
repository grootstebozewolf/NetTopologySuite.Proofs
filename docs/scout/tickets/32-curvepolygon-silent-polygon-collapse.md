# Silent POLYGON collapse — CURVEPOLYGON type honesty

**Type:** implement · **Map:** [CURVEPOLYGON](../map-curvepolygon.md)
**Blocked by:** ~~[Chart CURVEPOLYGON type honesty](closed/31-curvepolygon-type-chart.md)~~ ✔
**claimId:** none · **GitHub:** none · **witness:** none

HOLD implement stands. No Architect SIGN lifts this leftover.
Sibling COMPOUNDCURVE ticket 30 (this packet) is lineal Flatten, not this.

## Ask

Name or refuse the silent path that still eats `CURVEPOLYGON` at
overlay, hull, or TestBuilder and emits `POLYGON` / `LinearRing`
without a stamp, or treats JTS `getExteriorRing()` as the curve.
A curve polygon stays a curve polygon. Named `Linearize` / `toLinear`
/ `chord_approx_ring` / OverlayNGCurve `APPROX` + `isApproximate()`
stays named. I/O type identity is not op honesty.

Cite ISO/IEC 13249-3. No DOI. No 19125-2.

Do not start this ticket until Architect SIGN lifts HOLD implement.

## In scope

- Engine grill: NTS overlay / hull / TestBuilder sites that still
  consume `CurvePolygon` and emit `Polygon` / `LinearRing` without
  calling `Linearize`. JTS OverlayNGCurve cells that densify with
  `isApproximate()=false`, or that hand `getExteriorRing()` to a
  caller as if it were `getExteriorCurve()`.
- One Proofs honesty pin **only if** it is a new statement. Do not
  remint `CurveGeometry.v : valid_curve_polygon`,
  `CurveLinearise.v : to_geometry_outer_ring_closed`, or
  `WindingNumber.v : winding_decides_membership`.
- Keep the result type named (CURVEPOLYGON vs POLYGON of chords).

## Out of scope

- Merge into JTS #7. Type-10 reader PR. GEO-TIN 15–17.
- A second CurvePolygon type. Public noder. JTS #27. JTS #38.
- `#509` Jordan true-region. FCP-S WKT shell. QG-CURVE-CHORD path-stamp CI.
- COMPOUNDCURVE ticket 30 / flatten-elimination.
- Remint `69-a`, `508-*`, leftover `Ⅰ`–`Ⅹ`.
- Kit-completeness (CUP/CAP/XOR/SUB + T-in/T-out).
- Setting WSJF.

## Done when

A later `/implement`, **after** Architect SIGN, can point at one named
site (engine or Coq) and say whether it refused or stamped. This ticket
stays open until that letter lands. Do not mint `CRV-CP` as a Proofs
claimId unless that letter names a new lemma.
