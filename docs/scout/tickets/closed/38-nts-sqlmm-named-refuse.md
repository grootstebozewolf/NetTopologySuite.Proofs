# NTS WKT named refuse for §4.2.1 curve types

**Type:** implement · **Map:** [COMPOUNDCURVE](../../map-compoundcurve.md) (packet-wide I/O)
**Claimed:** implement 2026-09-02 · **Closed:** 2026-09-02 (NTS named refuse)
**Blocked by:** ~~[SQL/MM WKT oracle](closed/37-sqlmm-wkt-oracle.md)~~ ✔
**claimId:** none · **GitHub:** none · **witness:** none

## Ask

GEOS already names `CLOTHOID`, `CIRCLE`, `GEODESICSTRING`,
`NURBSCURVE`, and `SPIRALCURVE` and refuses. NTS WKT still says
`Unknown type`, which is a lie: they are instantiable ST_Curve
subtypes in ISO/IEC 13249-3 §4.2.1, not optional extras.

Name them and refuse. Do not grow a carrier. Do not flatten to
`LINESTRING`. A genuine unknown token still says `Unknown type`.
`COMPOUNDCURVE (CLOTHOID …)` must hit the same named refuse, not
`Unexpected token`.

Cite ISO/IEC 13249-3. No DOI. No 19125-2.

## In scope

- NTS `WKTReader` top-level dispatch and `ReadCurveText` members.
- Tests that the five types (and Z form) refuse with §4.2.1 in the
  message, and that `NOTATYPE` stays `Unknown type`.
- ELLIPTICALCURVE (§4.2.9) is instantiable too — same named refuse.

## Out of scope

- Carriers. `CurveSegment` growth. `508-*` remint. Leftover `Ⅺ`.
- Type-9/10/11/12 reader PRs. JTS #7 3-arg CLOTHOID-in-COMPOUNDCURVE
  (SFA, not ST_Clothoid). Koc railway compound.
- Inventing WKB codes. Parsing SPIRALTYPE (that is oracle
  `SQLMM_WKT`, ticket 37).
- Ticket 10 / #506.

## Resolution

**Implemented 2026-09-02 on NTS** (`cursor/sqlmm-type-honesty-ccfa`).

Named site: `WKTReader` dispatch + `ReadCurveText`. Message:
`SQL/MM type is not optional (ISO/IEC 13249-3 §4.2.1) and is not
implemented`. `NOTATYPE` still says `Unknown type`. CIRCLE does not
steal CIRCULARSTRING (dim-suffix matcher, not `IsTypeName`).

Pins: `CurveWktTest.SqlMmSection421TypesAreNamedRefusesNotUnknown`
(31 CurveWktTest passed). No carrier. Do not remint `508-*`.
claimId: none. witness: none.
