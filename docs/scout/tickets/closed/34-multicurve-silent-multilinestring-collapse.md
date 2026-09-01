# Silent MultiLineString collapse — MULTICURVE type honesty

**Type:** implement · **Map:** [MULTICURVE](../../map-multicurve.md)
**Claimed:** implement 2026-09-01 · **Closed:** 2026-09-01 (GEOS named the leftover)
**Blocked by:** ~~[Chart MULTICURVE type honesty](33-multicurve-type-chart.md)~~ ✔
**claimId:** none · **GitHub:** none · **witness:** none

HOLD implement stood until `/implement 660` on GEOS.
Sibling COMPOUNDCURVE ticket 30 (this packet) is lineal Flatten, not this.
Sibling CURVEPOLYGON ticket 32 (this packet) is POLYGON emit, not this.

## Ask

Name or refuse the silent path that still eats `MULTICURVE` at
overlay, hull, or TestBuilder and emits `MULTILINESTRING` /
`LineString[]` without a stamp, or treats the JTS `MultiLineString`
supertype as linearized members. A multicurve stays a multicurve.
Named `Linearize` / `toLinear` / `chord_approx_ring` / OverlayNGCurve
`APPROX` + `isApproximate()` stays named. I/O type identity is not
op honesty.

Cite ISO/IEC 13249-3. No DOI. No 19125-2.

Do not start this ticket until Architect SIGN lifts HOLD implement.

## In scope

- Engine grill: NTS overlay / hull / TestBuilder sites that still
  consume `MultiCurve` (or WKB type 11) and emit `MultiLineString`
  without calling `Linearize` / `toLinear`. JTS OverlayNGCurve cells
  that densify with `isApproximate()=false`, or that hand a
  `MultiLineString` view to a caller as if it were the curve
  collection.
- One Proofs honesty pin **only if** it is a new statement. Do not
  remint `CurveGeometry.v : CurveSegment`,
  `CurveGeometry.v : valid_curve_geometry`,
  `CurveLinearise.v : chord_approx_ring_closed`,
  `WktGeoJsonRoundtrip.v : wkt_geojson_wkt_roundtrip`, or
  `CurveLength.v : curve_length_additive`.
- Keep the result type named (MULTICURVE vs MULTILINESTRING of chords).

## Out of scope

- Merge into JTS #7. Type-11 reader PR. GEO-TIN 15–17.
- A second MultiCurve type. Public noder. JTS #27. JTS #38.
- Minting a Coq MultiCurve carrier as the leftover (that is a
  different missing type; HOLD implement stands here too).
- `#509` Jordan true-region. F-MS / MULTISURFACE. WKB-8-12 I/O.
- QG-CURVE-CHORD path-stamp CI. `615-h` IsValid rung.
- COMPOUNDCURVE ticket 30. CURVEPOLYGON ticket 32.
- Remint `69-a`, `508-*`, leftover `Ⅰ`–`Ⅹ`.
- Setting WSJF.

## Done when

A later `/implement`, **after** Architect SIGN, can point at one named
site (engine or Coq) and say whether it refused or stamped. This ticket
stays open until that letter lands. Do not mint `CRV-MC` as a Proofs
claimId unless that letter names a new lemma.

## Resolution

**Implemented 2026-09-01 on GEOS** after `/implement 660` SIGN.

Named site: GEOS OverlayNG + C API overlay. A `MULTICURVE` overlay
result keeps curved types; silent `MULTILINESTRING` emit is a refuse
unless the caller used `getLinearized`.

Coq still has no MultiCurve carrier
(`CurveGeometry.v : valid_curve_geometry` is F-MS-shaped). That
missing type is not this leftover. No new Coq lemma.
claimId: none. witness: none.
