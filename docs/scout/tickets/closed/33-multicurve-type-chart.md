# Chart MULTICURVE type honesty

**Type:** grilling · **Map:** [MULTICURVE](../../map-multicurve.md)
**Claimed:** wayfinder 2026-09-01 · **Closed:** 2026-09-01
**Blocked by:** —
**claimId:** none · **GitHub:** none · **witness:** none

No dedicated board card. Sibling WKB-8-12 is I/O (type 11). Sibling
CRV-CC is COMPOUNDCURVE flatten-elimination (this packet; tickets 29 / 30).
Sibling CRV-CP is CURVEPOLYGON silent POLYGON collapse (this packet;
tickets 31 / 32).

## Question

What does `/wayfinder MULTICURVE` own? Name what is already true,
park what is HOLD, and leave one named leftover so the next session
cannot steal ticket 30, steal ticket 32, steal `#509`, or invent a
Coq MultiCurve carrier as already true.

## Resolution

**Grilled 2026-09-01. Living record:
[`docs/scout/map-multicurve.md`](../../map-multicurve.md).**
This ticket does not implement silent-multilinestring-collapse.

**Already true.** SQL/MM `ST_MultiCurve` is ISO/IEC 13249-3 §4.2.25,
WKB 11. JTS has Option A (`MultiCurve extends MultiLineString`) and
named `toLinear`. NTS has `OgcGeometryType.MultiCurve = 11`. Coq
member alphabet is `CurveGeometry.v : CurveSegment`. Named linearise
is `CurveLinearise.v : chord_approx_ring_closed`. Linear WKT/GeoJSON
is `WktGeoJsonRoundtrip.v : wkt_geojson_wkt_roundtrip` (no MULTICURVE
constructor). `CurveGeometry.v : valid_curve_geometry` is a list of
curve polygons — not MultiCurve. HELP names CS / CC / CP and does
not name MULTICURVE.

**Three words.** Silent MultiLineString collapse is the leftover.
Named `Linearize` / `toLinear` / `chord_approx_ring` is allowed.
Collection / member list is named on the engine and missing in Coq.

**Parks.** JTS #27 out. JTS #38 off #7. No public noder. HOLD merge
into #7. HOLD a second MultiCurve type. HOLD implement for ticket 34
(no Architect SIGN). No type-11 reader PR. No GEO-TIN 15–17. No DOI.
Cite 13249-3 only. Do not steal `615-h`. Do not remint `#509`.

**Frontier.** Ticket 34 names the leftover. HOLD implement stands.
Do not `/implement` from this letter.
