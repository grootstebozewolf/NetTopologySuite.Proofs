# Chart MULTISURFACE type honesty

**Type:** grilling · **Map:** [MULTISURFACE](../../map-multisurface.md)
**Claimed:** wayfinder 2026-09-01 · **Closed:** 2026-09-01
**Blocked by:** —
**claimId:** none · **GitHub:** none · **witness:** none

No dedicated board card. Sibling WKB-8-12 is I/O (type 12). Sibling
tickets: COMPOUNDCURVE 29 / 30, CURVEPOLYGON 31 / 32,
MULTICURVE 33 / 34 — all siblings in this packet.

## Question

What does `/wayfinder MULTISURFACE` own? Name what is already true,
park what is HOLD, and leave one named leftover so the next session
cannot steal ticket 32, steal ticket 34, steal `#509`, or treat
`valid_curve_geometry` as overlay honesty.

## Resolution

**Grilled 2026-09-01. Living record:
[`docs/scout/map-multisurface.md`](../../map-multisurface.md).**
This ticket does not implement silent-multipolygon-collapse.

**Already true.** SQL/MM `ST_MultiSurface` is ISO/IEC 13249-3 §4.2.27,
WKB 12. Coq structural collection is
`CurveGeometry.v : valid_curve_geometry` (`list CurvePolygon`) with
`CurveGeometry.v : valid_curve_geometry_nil` /
`CurveGeometry.v : valid_curve_geometry_cons`. Named collection
linearise is `CurveGeometry.v : to_geometry`. Named ring linearise is
`CurveLinearise.v : to_geometry_outer_ring_closed`. JTS has Option A
(`MultiSurface extends MultiPolygon`) and named `toLinear`. NTS has
`OgcGeometryType.MultiSurface = 12`. Linear WKT/GeoJSON is
`WktGeoJsonRoundtrip.v : wkt_geojson_wkt_roundtrip` (no MULTISURFACE
constructor). HELP names CS / CC / CP and does not name MULTISURFACE.

**Three words.** Silent MultiPolygon collapse is the leftover. Named
`Linearize` / `toLinear` / `to_geometry` is allowed. Collection /
member list is already the structural pin.

**Parks.** JTS #27 out. JTS #38 off #7. No public noder. HOLD merge
into #7. HOLD a second MultiSurface type. HOLD implement for ticket 36
(no Architect SIGN). No type-12 reader PR. No GEO-TIN 15–17. No DOI.
Cite 13249-3 only. Do not steal `615-h`. Do not remint `#509`.

**Frontier.** Ticket 36 names the leftover. HOLD implement stands.
Do not `/implement` from this letter.
