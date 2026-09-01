# Silent MultiPolygon collapse — MULTISURFACE type honesty

**Type:** implement · **Map:** [MULTISURFACE](../../map-multisurface.md)
**Claimed:** implement 2026-09-01 · **Closed:** 2026-09-01 (GEOS named the leftover)
**Blocked by:** ~~[Chart MULTISURFACE type honesty](35-multisurface-type-chart.md)~~ ✔
**claimId:** none · **GitHub:** none · **witness:** none

HOLD implement stood until `/implement 660` on GEOS.
Sibling CURVEPOLYGON ticket 32 (this packet) is one-surface POLYGON emit,
not this. Sibling MULTICURVE ticket 34 (this packet) is lineal
MULTILINESTRING emit, not this.

## Ask

Name or refuse the silent path that still eats `MULTISURFACE` at
overlay, hull, or TestBuilder and emits `MULTIPOLYGON` / `Polygon[]`
without a stamp, or treats the JTS `MultiPolygon` supertype as
linearized members. A multisurface stays a multisurface. Named
`Linearize` / `toLinear` / `to_geometry` / `chord_approx_ring` /
OverlayNGCurve `APPROX` + `isApproximate()` stays named. I/O type
identity is not op honesty.

Cite ISO/IEC 13249-3. No DOI. No 19125-2.

Do not start this ticket until Architect SIGN lifts HOLD implement.

## In scope

- Engine grill: NTS overlay / hull / TestBuilder sites that still
  consume `MultiSurface` (or WKB type 12) and emit `MultiPolygon`
  without calling `Linearize` / `toLinear`. JTS OverlayNGCurve cells
  that densify with `isApproximate()=false`, or that hand a
  `MultiPolygon` view to a caller as if it were the curve collection.
- One Proofs honesty pin **only if** it is a new statement. Do not
  remint `CurveGeometry.v : valid_curve_geometry`,
  `CurveGeometry.v : to_geometry`,
  `CurveLinearise.v : to_geometry_outer_ring_closed`, or
  `WktGeoJsonRoundtrip.v : wkt_geojson_wkt_roundtrip`.
- Keep the result type named (MULTISURFACE vs MULTIPOLYGON of chords).

## Out of scope

- Merge into JTS #7. Type-12 reader PR. GEO-TIN 15–17.
- A second MultiSurface type. Public noder. JTS #27. JTS #38.
- `#509` Jordan true-region. I/O member-tag degrade. WKB-8-12 I/O.
- QG-CURVE-CHORD path-stamp CI. `615-h` IsValid rung.
- COMPOUNDCURVE ticket 30. CURVEPOLYGON ticket 32. MULTICURVE ticket 34.
- Remint `69-a`, `508-*`, leftover `Ⅰ`–`Ⅹ`.
- Setting WSJF.

## Done when

A later `/implement`, **after** Architect SIGN, can point at one named
site (engine or Coq) and say whether it refused or stamped. This ticket
stays open until that letter lands. Do not mint `CRV-MS` as a Proofs
claimId unless that letter names a new lemma.

## Resolution

**Implemented 2026-09-01 on GEOS** after `/implement 660` SIGN.

Named site: `CascadedPolygonUnion::restrictToSurfaces`. It used
`hasCurvedComponents()`, so an all-linear `CurvePolygon` (no arcs)
was packed into `MultiPolygon`. It now checks `hasCurvedTypes()`.
That is the refuse of silent `MULTIPOLYGON` emit.

`CurveGeometry.v : valid_curve_geometry` stays structural F-MS.
`CurveGeometry.v : to_geometry` stays named linearise. No new Coq
lemma. Do not remint tracker 509. claimId: none. witness: none.
