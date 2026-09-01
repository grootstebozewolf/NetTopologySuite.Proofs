# Map — MULTISURFACE type honesty

A wayfinder map. Charted 2026-09-01. This is **not** a `wayfinder:map`
GitHub issue, **not** a remint of `#509` / `69-a` / `508-*` / leftover
`Ⅰ`–`Ⅹ`, **not** COMPOUNDCURVE ticket 30, **not** CURVEPOLYGON ticket
32, and **not** MULTICURVE ticket 34. It does **not** implement
silent-MultiPolygon elimination. It does **not** mint a second
MultiSurface type. It does **not** merge into JTS #7. No dedicated
board card; sibling WKB-8-12 is I/O (type 12).

> Architect SIGN 16 Aug 2026 on FCP-S / WKB-8-12: HOLD type I/O 13–17
> / 18–20. Off #7 for anything not already landed. Do not mark pass.
> Cite 13249-3 for types 8–12 only. No invented DOI. **No SIGN lifts
> HOLD implement for this leftover.** Named linear fallback stays
> named. No GEO-TIN 15–17. No type-12 reader PR. No second MultiSurface
> type. No priority.

topics: arc, wkt
claimId: none
witness: none

## Destination

**Name the silent MultiPolygon-collapse leftover so the next
`/implement` cannot steal ticket 32, steal ticket 34, steal `#509`,
treat `valid_curve_geometry` as overlay honesty, or treat I/O
round-trip as op honesty.**

SQL/MM `ST_MultiSurface` (ISO/IEC 13249-3 §4.2.27; WKB type 12) is a
collection of ST_Surface members. Members may be ST_CurvePolygon /
ST_Polygon. The ask is honesty: a multisurface stays a multisurface.
Silent emit of `MULTIPOLYGON` / `Polygon[]` chords for overlay, hull,
or TestBuilder is a refuse. Named `Linearize` / `toLinear` /
`to_geometry` is not that refuse. JTS `MultiSurface` extending
`MultiPolygon` is the named Option-A contract, not the leftover —
`toLinear` is the named collapse to `MultiPolygon`.

This letter does not retire a tracker and does not mint an epic.
Epic creation stays owner-scope. `#509` stays OPEN (Jordan is a
per-member true-region leftover; it is not this collection).

## Three words that say "collapse"

| Word | What it is | Park | Status |
|---|---|---|---|
| Silent MultiPolygon collapse | Overlay / hull / TestBuilder eat `MULTISURFACE` and emit `MULTIPOLYGON` / `Polygon[]` chords with no stamp; or treat the JTS `MultiPolygon` supertype as if members were linearized | leftover **silent-multipolygon-collapse** | Named on GEOS `restrictToSurfaces` (`hasCurvedTypes`). Ticket 36 closed. Distinct from ticket 32 (single CURVEPOLYGON → POLYGON) and ticket 34 (MULTICURVE → MULTILINESTRING). |
| Named linear fallback | `Linearize` / `toLinear` / `to_geometry` / `chord_approx_ring` / OverlayNGCurve `APPROX` + `isApproximate()` | technique (named) | Allowed. JTS `MultiSurface.toLinear` returns `MultiPolygon` and is named. Coq `CurveGeometry.v : to_geometry` maps `list CurvePolygon` to linear `Geometry`. `CurveLinearise.v : to_geometry_outer_ring_closed` is the named ring bridge. |
| Collection / member list | Members stay ST_Surface / CurvePolygon; the collection is not one CurvePolygon | already landed (structural) | Coq `CurveGeometry.v : valid_curve_geometry` is `Forall valid_curve_polygon` on `list CurvePolygon`. Nil/cons: `CurveGeometry.v : valid_curve_geometry_nil` / `CurveGeometry.v : valid_curve_geometry_cons`. Structural only. Not Jordan. Not overlay honesty. |

I/O type identity is not op honesty. WKB-8-12 names type 12. GML
`MultiSurface` in NTS core `GMLReader.ReadMultiSurface` returns
`MultiPolygon` — SFSQL/GML3 name, not SQL/MM `ST_MultiSurface`.
JTS curve README notes a written `MULTISURFACE(CURVEPOLYGON(…))` can
re-read as `MultiSurface[Polygon]` because inner-member tags are not
yet emitted — I/O member-tag degrade, sibling of WKB-8-12, not this
leftover. Do not cite ISO 19125-2 (a JTS test file comment does; this
corpus cites 13249-3 only).

## What is already true

| Surface | Pin | Honesty |
|---|---|---|
| 60s reader | `docs/HELP.md` BIM Bea card; `docs/READING-GUIDE.md` | Names CIRCULARSTRING / COMPOUNDCURVE / CURVEPOLYGON. **Does not name MULTISURFACE.** Name gap, not a drop. |
| SQL/MM type | ISO/IEC 13249-3 §4.2.27; clause book §1 | Instantiable collection of ST_Surface. WKB 12 (`docs/iso13249-3-curve-type-bindings-2026-08.md` Table 15). Cite 13249-3, not 19125-2. |
| Structural collection | `CurveGeometry.v : valid_curve_geometry` | `list CurvePolygon`. This is the F-MS-shaped Coq carrier the MULTICURVE letter refused to steal. Structural `Forall` only. |
| Nil / cons | `CurveGeometry.v : valid_curve_geometry_nil` / `CurveGeometry.v : valid_curve_geometry_cons` | Empty collection and cons of a valid member. Not overlay honesty. |
| Member structural | `CurveGeometry.v : valid_curve_polygon` | Each member is a structural CurvePolygon. True-region waits on `#509`. |
| Named collection linearise | `CurveGeometry.v : to_geometry` | Option B map of every member ring to a linear `Geometry`. Named. Not silent MULTIPOLYGON emit. |
| Named ring linearise | `CurveLinearise.v : to_geometry_outer_ring_closed` | Combinatorial faithfulness of the *named* linearise of one outer ring. |
| Linear WKT/GeoJSON alphabet | `WktGeoJsonRoundtrip.v : wkt_geojson_wkt_roundtrip` | `GTMultiPolygon` / `OgcMultiPolygon` only. No MULTISURFACE constructor. |
| Completeness fog | `OverlayTouchRow.v : phase0_relation_complete_hypothesis_refuted` | Kit-completeness stays fog. CUP/CAP/XOR/SUB + T-in/T-out is not this leftover. |
| JTS Option A | `org.locationtech.jts.geom.curve.MultiSurface` | Extends `MultiPolygon`. `toText` uses `CurveWKTWriter` (refuse flatten of members). `toLinear` is named. Ops route `CurveOps`. OverlayNGCurve may return an exact `MultiSurface` of operands (disjoint CUP / XOR) — named exact collection, not collapse. |
| NTS type code | `OgcGeometryType.MultiSurface = 12` | Enum exists on `develop`. Dedicated `MultiSurface.cs` is on the curve-foundation branch (clause book §1). |
| WKB-8-12 I/O | Notion WKB-8-12; type 12 | Writers must not call `toLinear`. Readers must emit first-class types. I/O identity, not op honesty. Off #7. |
| F-CP / F-MC / F-MS TRIAGE | `#64` residue / `#509` | Bundled row says "structural model exists; true-region deferred". Structural collection is this pin. Jordan stays on `#509`. This letter does not flip the bundled row. |
| Rung-1 IsValid | clause book §6.2 | MultiSurface has no rung-1 override. Members fail-closed. Wiring is `615-h`-lane. Do not steal `615-h`. |

## Leftover table

Parks follow ADR-0002. Value and priority are orthogonal. This letter
does not set WSJF.

| Id | Leftover | Kind | Park | Status | Do not |
|---|---|---|---|---|---|
| silent-multipolygon-collapse | Silent emit of `MULTIPOLYGON` / `Polygon[]` at overlay / hull / TestBuilder, or treating the `MultiPolygon` supertype as linearized members | CRV-MS | technique | Named on GEOS `CascadedPolygonUnion::restrictToSurfaces` (`hasCurvedTypes`, not `hasCurvedComponents`). Ticket 36 closed. OverlayNG already kept MULTISURFACE. NTS/JTS leftover sites stay an engine grill. | steal ticket 32; steal ticket 34; steal `#509`; treat `to_geometry` / WKB-8-12 as overlay honesty; merge into JTS #7; mint a second MultiSurface type |
| — | CURVEPOLYGON silent POLYGON collapse | CRV-CP / ticket 32 | technique | Sibling in this packet. One surface. | steal ticket 32 for a MultiSurface site |
| — | MULTICURVE silent MultiLineString collapse | CRV-MC / ticket 34 | technique | Sibling in this packet. Lineal collection. | steal ticket 34 |
| — | COMPOUNDCURVE flatten-elimination | CRV-CC / ticket 30 | technique | Sibling in this packet. Single contiguous compound. | steal ticket 30 |
| — | V-CP Jordan true-region | `#509` | technique | Per-member true-region. Stays OPEN. | remint `#509`; pull Jordan into CRV-MS |
| — | I/O member-tag degrade | WKB-8-12 / JTS README | sequencing | Written `MULTISURFACE(CURVEPOLYGON(…))` can re-read as `MultiSurface[Polygon]`. I/O, not overlay. | open a type-12 reader PR from this letter |
| — | GML3 `MultiSurface` → `MultiPolygon` | NTS core I/O | sequencing | SFSQL/GML3 name. Not SQL/MM type 12. | treat GML as this leftover |
| — | HELP name gap | 60s reader | sequencing | Bea card does not name MULTISURFACE. | treat a HELP edit as overlay honesty |
| — | Kit-completeness (CUP/CAP/XOR/SUB + T-in/T-out) | fog | research | OverlayNGCurve already names some exact MultiSurface cells. Completeness has a refuted ancestor. | mint a completeness epic |
| — | QG-CURVE-CHORD path stamp | sibling board card | sequencing | HOLD implement. Does not join this leftover. | invent EXACT / NAMED-APPROX / CHORD-PATH CI on this letter |
| — | MultiSurface IsValid rung-1 | `615-h` lane | sequencing | Clause book §6.2. | steal `615-h` |
| — | JTS #27 OverlayNG-for-circles | JTS #27 | sequencing | **Out.** | fold into this map; merge into #7 |
| — | JTS #38 package-private curve DCEL | JTS #38 | sequencing | Off #7 unless PO says merge. No public noder. | make the DCEL public |
| — | Second MultiSurface type | board HOLD | sequencing | The existing JTS / NTS-enum / Coq `CurveGeometry` carriers stay. | mint a parallel type; join GEO-TIN 15–17 |
| — | 3-D Multi* / GEO-TIN / PRF-TIN15 | sibling TIN cards | sequencing | Types 15–17 are not type 12. HOLD implement. | join GEO-TIN 15–17 |

## Decisions so far

- MULTISURFACE is SQL/MM ISO/IEC 13249-3, WKB 12. Cite that standard.
  There is no DOI. Do not cite ISO 19125-2.
- A MultiSurface is a collection of surfaces. A CurvePolygon is one
  surface. They are different types.
- Bea 60s reader names CS / CC / CP and does not name MULTISURFACE.
  That is a name gap, not this leftover.
- Silent MultiPolygon collapse is the one leftover this card owns.
  It is not leftover `Ⅵ`, not `CRV-MS` as a Proofs claimId, not
  `#509`, and not a new epic.
- Named linear fallback stays named. Silent MultiPolygon emit is a
  refuse.
- JTS `MultiSurface extends MultiPolygon` is named Option A.
  `toLinear` → `MultiPolygon` is named.
- `CurveGeometry.v : valid_curve_geometry` is the structural
  collection pin. `to_geometry` is the named linearise of that
  collection. Neither is overlay honesty.
- `#509` owns Jordan. F-CP / F-MC / F-MS TRIAGE rows do not flip.
- Tickets 30 / 32 / 34 stay siblings.
- JTS #27 is out. JTS #38 stays off #7. No public noder.
- HOLD merge into #7. HOLD a second MultiSurface type. No priority
  from this letter.
- `/implement 660` on GEOS named the leftover:
  `CascadedPolygonUnion::restrictToSurfaces` now checks
  `hasCurvedTypes()`. Ticket 36 closed. See
  [`closed/36-multisurface-silent-multipolygon-collapse.md`](tickets/closed/36-multisurface-silent-multipolygon-collapse.md).

## Fog

- **Which NTS / JTS overlay entry still emits MultiPolygon without a
  stamp** is an NTS/JTS engine leftover, not a Coq lemma. GEOS
  OverlayNG already keeps MULTISURFACE;
  `restrictToSurfaces` now keeps all-linear CurvePolygon members.
  OverlayNGCurve already has named exact MultiSurface cells; unnamed
  cells still densify.
- **NTS `develop` has the enum and not the class.** The clause-book
  path is the curve-foundation branch.
- **HELP still says `Flatten()`** while the NTS method is `Linearize`.
  Name drift on CS / CC / CP. MULTISURFACE was never on that card.
- **QG-CURVE-CHORD** stays a separate card.

## Frontier

Ticket 35 (this chart) is closed. Ticket 36 is closed on GEOS:
`restrictToSurfaces` checks `hasCurvedTypes()`. NTS/JTS overlay
sites stay an engine grill. Next useful session is an NTS or JTS
letter, or stop.

Sibling COMPOUNDCURVE tickets 29 / 30 live in this packet
(`map-compoundcurve.md`). Sibling CURVEPOLYGON tickets 31 / 32
live in this packet (`map-curvepolygon.md`). Sibling MULTICURVE
tickets 33 / 34 live in this packet (`map-multicurve.md`).
Numbered 35 / 36 so the leftovers stay distinct.

```
HELP / READING-GUIDE ════════════ CS / CC / CP named ── MULTISURFACE absent
valid_curve_geometry ══════════ list CurvePolygon ── structural F-MS
to_geometry ══════════════════ named collection linearise ── not this leftover
I/O type 12 / WKB-8-12 ════════ identity, not op honesty ── off #7
JTS MultiSurface ══════════════ Option A + named toLinear
#509 V-CP Jordan ══════════════ per-member true-region ── stays OPEN
CRV-CP ticket 32 ══════════════ one-surface POLYGON emit ── sibling, closed on GEOS
CRV-MC ticket 34 ══════════════ lineal MULTILINESTRING emit ── sibling, closed on GEOS

silent-multipolygon-collapse ── ticket 36 closed on GEOS
#27 ── out
#38 ── Option C DCEL ── off #7 ── no public noder
second type / type-12 reader / GEO-TIN 15–17 ── HOLD
```

## Do not

- Remint `#509` / `69-a` / `508-*` / `522-*` / leftover `Ⅰ`–`Ⅹ` / `615-h`.
- Mint leftover `Ⅺ` or `CRV-MS` as a Proofs claimId.
- Mint a GitHub child from this map.
- Implement silent-multipolygon-collapse in this letter.
- `/implement` ticket 36 while HOLD implement stands.
- Steal tickets 30 / 32 / 34.
- Treat `CurveGeometry.v : to_geometry` as silent collapse.
- Merge into JTS #7. Open a type-12 reader PR. Join GEO-TIN 15–17.
- Invent a DOI. Cite 19125-2. Copy clothoid Zenodo.
- Treat GML3 `MultiSurface` as SQL/MM type 12.
- Flip F-CP / F-MC / F-MS TRIAGE status.
- Set backlog priority.
