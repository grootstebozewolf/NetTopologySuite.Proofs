# Map — MULTICURVE type honesty

A wayfinder map. Charted 2026-09-01. This is **not** a `wayfinder:map`
GitHub issue, **not** a remint of `#509` / `69-a` / `508-*` / leftover
`Ⅰ`–`Ⅹ`, **not** COMPOUNDCURVE ticket 30, and **not** CURVEPOLYGON
ticket 32. It does **not** implement silent-MultiLineString
elimination. It does **not** mint a second MultiCurve type. It does
**not** merge into JTS #7. No dedicated board card; sibling WKB-8-12
is I/O (type 11).

> Architect SIGN 16 Aug 2026 on FCP-S / WKB-8-12: HOLD type I/O 13–17
> / 18–20. Off #7 for anything not already landed. Do not mark pass.
> Cite 13249-3 for types 8–12 only. No invented DOI. **No SIGN lifts
> HOLD implement for this leftover.** Named linear fallback stays
> named. No GEO-TIN 15–17. No type-11 reader PR. No second MultiCurve
> type. No priority.

topics: arc, wkt
claimId: none
witness: none

## Destination

**Name the silent MultiLineString-collapse leftover so the next
`/implement` cannot steal ticket 30, steal ticket 32, steal `#509`,
invent a Coq MultiCurve carrier as "already true", or treat I/O
round-trip as overlay honesty.**

SQL/MM `ST_MultiCurve` (ISO/IEC 13249-3 §4.2.25; WKB type 11) is a
collection of ST_Curve members. Members need not be contiguous — that
is COMPOUNDCURVE (§4.2.13 / §7.10.1). The ask is honesty: a multicurve
stays a multicurve. Silent emit of `MULTILINESTRING` / `LineString[]`
chords for overlay, hull, or TestBuilder is a refuse. Named
`Linearize` / `toLinear` / `chord_approx_ring` is not that refuse.
JTS `MultiCurve` extending `MultiLineString` is the named Option-A
contract, not the leftover — `toLinear` is the named collapse to
`MultiLineString`.

This letter does not retire a tracker and does not mint an epic.
Epic creation stays owner-scope. `#509` stays OPEN (Jordan is a
surface leftover; it is not this collection).

## Three words that say "collapse"

| Word | What it is | Park | Status |
|---|---|---|---|
| Silent MultiLineString collapse | Overlay / hull / TestBuilder eat `MULTICURVE` and emit `MULTILINESTRING` / `LineString[]` chords with no stamp; or treat the JTS `MultiLineString` supertype as if members were linearized | leftover **silent-multilinestring-collapse** | Named on GEOS OverlayNG. Ticket 34 closed. Distinct from ticket 30 (single compound Flatten) and ticket 32 (CURVEPOLYGON → POLYGON). |
| Named linear fallback | `Linearize` / `toLinear` / `chord_approx_ring` / OverlayNGCurve `APPROX` + `isApproximate()` | technique (named) | Allowed. JTS `MultiCurve.toLinear` returns `MultiLineString` and is named. Coq `CurveLinearise.v : chord_approx_ring_closed` is the named ring bridge, not a MultiCurve pin. |
| Collection / member list | Members stay ST_Curve; the collection is not a COMPOUNDCURVE splice | already named on the engine; **missing in Coq** | JTS type exists. NTS `OgcGeometryType.MultiCurve = 11`. Coq has `CurveGeometry.v : CurveSegment` (`CSChord` \| `CSArc`) as a *member* alphabet and no MultiCurve carrier. `CurveGeometry.v : valid_curve_geometry` is `list CurvePolygon` (F-MS-shaped). Do not cite it as MultiCurve. |

I/O type identity is not op honesty. WKB-8-12 names type 11. GML
`MultiCurve` in NTS core `GMLReader.ReadMultiCurve` returns
`MultiLineString` — SFSQL/GML3 name, not SQL/MM `ST_MultiCurve`.
WKB/WKT may round-trip type 11 and still lie in overlay unless the
op carries a path stamp (sibling QG-CURVE-CHORD; HOLD implement;
does not join this leftover).

## What is already true

| Surface | Pin | Honesty |
|---|---|---|
| 60s reader | `docs/HELP.md` BIM Bea card; `docs/READING-GUIDE.md` | Names CIRCULARSTRING / COMPOUNDCURVE / CURVEPOLYGON. **Does not name MULTICURVE.** Name gap, not a drop of a type that was never on the card. |
| SQL/MM type | ISO/IEC 13249-3 §4.2.25; clause book §1 | Instantiable collection of ST_Curve. WKB 11 (`docs/iso13249-3-curve-type-bindings-2026-08.md` Table 15). Cite 13249-3, not 19125-2. |
| Member alphabet | `CurveGeometry.v : CurveSegment` | `CSChord` \| `CSArc`. A MultiCurve *member* may be those. The collection type is not in Coq. |
| Not a MultiCurve pin | `CurveGeometry.v : valid_curve_geometry` | `Forall valid_curve_polygon`. That is a list of curve polygons (F-MS-shaped), not ST_MultiCurve. |
| Named Option B bridge | `CurveLinearise.v : chord_approx_ring_closed` | Combinatorial faithfulness of the *named* linearise of a ring. Not silent MultiLineString emit. |
| Linear WKT/GeoJSON alphabet | `WktGeoJsonRoundtrip.v : wkt_geojson_wkt_roundtrip` | `GTMultiLineString` / `OgcMultiLineString` only. No MULTICURVE constructor. |
| Compound length additivity | `CurveLength.v : curve_length_additive` | Contiguous COMPOUNDCURVE member sum. Not a MultiCurve collection sum. Do not remint `508-*`. |
| Completeness fog | `OverlayTouchRow.v : phase0_relation_complete_hypothesis_refuted` | Kit-completeness stays fog. Same ancestor as the CURVEPOLYGON letter. |
| JTS Option A | `org.locationtech.jts.geom.curve.MultiCurve` | Extends `MultiLineString`. `toText` uses `CurveWKTWriter` (refuse flatten of members). `toLinear` is named. Ops route `CurveOps`. |
| NTS type code | `OgcGeometryType.MultiCurve = 11` | Enum exists on `develop`. Dedicated `MultiCurve.cs` is on the curve-foundation branch (clause book §1); this `develop` tree still returns a `GeometryCollection` of `Curve` from `CurvePolygon.Boundary` and calls a dedicated MultiCurve type "roadmap". |
| WKB-8-12 I/O | Notion WKB-8-12; type 11 | Writers must not call `toLinear`. Readers must emit first-class types. I/O identity, not op honesty. Off #7. |
| F-CP / F-MC / F-MS TRIAGE | `#64` residue / `#509` | Bundled row says "structural model exists". For MultiCurve that overclaims Coq. This letter does not flip the bundled row. |
| Rung-1 IsValid | clause book §6.2 | MultiCurve has no rung-1 override. Members fail-closed. Wiring is `615-h`-lane. Do not steal `615-h`. |

## Leftover table

Parks follow ADR-0002. Value and priority are orthogonal. This letter
does not set WSJF.

| Id | Leftover | Kind | Park | Status | Do not |
|---|---|---|---|---|---|
| silent-multilinestring-collapse | Silent emit of `MULTILINESTRING` / `LineString[]` at overlay / hull / TestBuilder, or treating the `MultiLineString` supertype as linearized members | CRV-MC | technique | Named on GEOS OverlayNG (MULTICURVE ∪ POINT does not emit MULTILINESTRING). Ticket 34 closed. Coq still has no MultiCurve carrier. NTS/JTS leftover sites stay an engine grill. | steal ticket 30; steal ticket 32; steal `#509`; treat WKB-8-12 as overlay honesty; merge into JTS #7; mint a Coq MultiCurve carrier as this leftover; mint a second MultiCurve type |
| — | COMPOUNDCURVE flatten-elimination | CRV-CC / ticket 30 | technique | Sibling in this packet. Single contiguous compound. | steal ticket 30 for a MultiCurve site |
| — | CURVEPOLYGON silent POLYGON collapse | CRV-CP / ticket 32 | technique | Sibling in this packet. Surface type. | steal ticket 32 |
| — | F-MS / MULTISURFACE | sibling | sequencing | `CurveGeometry.v : valid_curve_geometry` is closer to this than to MultiCurve. Not this letter. | pull F-MS into CRV-MC; remint the bundled F-CP / F-MC / F-MS row as done |
| — | V-CP Jordan true-region | `#509` | technique | Surface leftover. Stays OPEN. | remint `#509`; pull Jordan into CRV-MC |
| — | Coq MultiCurve carrier | missing type | technique | Honest gap. Not a proof in this letter. HOLD implement stands. | invent `valid_multi_curve` and call ticket 33 done |
| — | HELP name gap | 60s reader | sequencing | Bea card does not name MULTICURVE. | treat a HELP edit as overlay honesty |
| — | GML3 `MultiCurve` → `MultiLineString` | NTS core I/O | sequencing | SFSQL/GML3 name. Not SQL/MM type 11. | open a type-11 reader PR to "fix" GML |
| — | WKB type-11 reader PR | I/O | sequencing | Type 11 is already named on #7 I/O 8–12. | open a reader-only PR from this letter |
| — | QG-CURVE-CHORD path stamp | sibling board card | sequencing | HOLD implement. Does not join this leftover. | invent EXACT / NAMED-APPROX / CHORD-PATH CI on this letter |
| — | MultiCurve IsValid rung-1 | `615-h` lane | sequencing | Clause book §6.2. | steal `615-h` |
| — | JTS #27 OverlayNG-for-circles | JTS #27 | sequencing | **Out.** | fold into this map; merge into #7 |
| — | JTS #38 package-private curve DCEL | JTS #38 | sequencing | Off #7 unless PO says merge. No public noder. | make the DCEL public |
| — | Second MultiCurve type | board HOLD | sequencing | The existing JTS / NTS-enum / clause-book carriers stay. | mint a parallel type; join GEO-TIN 15–17 |
| — | 3-D Multi* / GEO-TIN | sibling TIN card | sequencing | Do not confuse with WKB 11. HOLD implement. | join GEO-TIN 15–17 |

## Decisions so far

- MULTICURVE is SQL/MM ISO/IEC 13249-3, WKB 11. Cite that standard.
  There is no DOI. Do not cite ISO 19125-2.
- A MultiCurve is a collection. A CompoundCurve is a contiguous splice.
  They are different types.
- Bea 60s reader names CS / CC / CP and does not name MULTICURVE.
  That is a name gap, not this leftover.
- Silent MultiLineString collapse is the one leftover this card owns.
  It is not leftover `Ⅵ`, not `CRV-MC` as a Proofs claimId, not
  `#509`, and not a new epic.
- Named linear fallback stays named. Silent MultiLineString emit is
  a refuse.
- JTS `MultiCurve extends MultiLineString` is named Option A.
  `toLinear` → `MultiLineString` is named.
- Coq has no MultiCurve carrier. `valid_curve_geometry` is not one.
- `#509` owns Jordan. F-CP / F-MC / F-MS TRIAGE rows do not flip.
- COMPOUNDCURVE ticket 30 and CURVEPOLYGON ticket 32 stay siblings.
- JTS #27 is out. JTS #38 stays off #7. No public noder.
- HOLD merge into #7. HOLD a second MultiCurve type. No priority
  from this letter.
- `/implement 660` on GEOS named the leftover: OverlayNG keeps
  MULTICURVE. Ticket 34 closed. See
  [`closed/34-multicurve-silent-multilinestring-collapse.md`](tickets/closed/34-multicurve-silent-multilinestring-collapse.md).

## Fog

- **Which NTS / JTS overlay entry still emits MultiLineString without
  a stamp** is an NTS/JTS engine leftover, not a Coq lemma. GEOS
  OverlayNG already keeps MULTICURVE.
- **NTS `develop` has the enum and not the class.** The clause-book
  path is the curve-foundation branch. Do not treat the missing
  `.cs` file on `develop` as Bea dropping the type.
- **HELP still says `Flatten()`** while the NTS method is `Linearize`.
  Name drift on CS / CC / CP. MULTICURVE was never on that card.
- **QG-CURVE-CHORD** stays a separate card.

## Frontier

Ticket 33 (this chart) is closed. Ticket 34 is closed on GEOS:
OverlayNG keeps MULTICURVE. Coq still has no MultiCurve carrier.
NTS/JTS overlay sites stay an engine grill. Next useful session
is an NTS or JTS letter, or stop.

Sibling COMPOUNDCURVE tickets 29 / 30 live in this packet
(`map-compoundcurve.md`). Sibling CURVEPOLYGON tickets 31 / 32
live in this packet (`map-curvepolygon.md`). Numbered 33 / 34
so the leftovers stay distinct.

```
HELP / READING-GUIDE ════════════ CS / CC / CP named ── MULTICURVE absent
CurveSegment ══════════════════ member alphabet, not the collection
valid_curve_geometry ══════════ list CurvePolygon ── F-MS-shaped, not this
I/O type 11 / WKB-8-12 ════════ identity, not op honesty ── off #7
JTS MultiCurve ════════════════ Option A + named toLinear
#509 V-CP Jordan ══════════════ surface ── stays OPEN
CRV-CC ticket 30 ══════════════ lineal Flatten ── sibling, closed on GEOS
CRV-CP ticket 32 ══════════════ POLYGON emit ── sibling, closed on GEOS

silent-multilinestring-collapse ── ticket 34 closed on GEOS
#27 ── out
#38 ── Option C DCEL ── off #7 ── no public noder
second type / type-11 reader / GEO-TIN 15–17 ── HOLD
Coq MultiCurve carrier ── missing ── not this leftover
```

## Do not

- Remint `#509` / `69-a` / `508-*` / `522-*` / leftover `Ⅰ`–`Ⅹ` / `615-h`.
- Mint leftover `Ⅺ` or `CRV-MC` as a Proofs claimId.
- Mint a GitHub child from this map.
- Implement silent-multilinestring-collapse in this letter.
- `/implement` ticket 34 while HOLD implement stands.
- Steal COMPOUNDCURVE ticket 30 or CURVEPOLYGON ticket 32.
- Cite `CurveGeometry.v : valid_curve_geometry` as a MultiCurve pin.
- Merge into JTS #7. Open a type-11 reader PR. Join GEO-TIN 15–17.
- Invent a DOI. Cite 19125-2. Copy clothoid Zenodo.
- Treat GML3 `MultiCurve` as SQL/MM type 11.
- Flip F-CP / F-MC / F-MS TRIAGE status.
- Set backlog priority.
