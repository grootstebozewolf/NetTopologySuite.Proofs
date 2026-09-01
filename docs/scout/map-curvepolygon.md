# Map — CURVEPOLYGON type honesty

A wayfinder map. Charted 2026-09-01. This is **not** a `wayfinder:map`
GitHub issue, **not** a remint of `#509` / `69-a` / `508-*` / leftover
`Ⅰ`–`Ⅹ`, and **not** COMPOUNDCURVE ticket 30. It does **not** implement
silent-POLYGON elimination. It does **not** mint a second CurvePolygon
type. It does **not** merge into JTS #7. No dedicated board card; sibling
cards FCP-S (I/O) and TB-T (draw) stay where they are.

> Architect SIGN 16 Aug 2026 on FCP-S: HOLD type I/O 13–17 / 18–20.
> Off #7 for anything not already landed. Do not mark pass. Cite 13249-3
> for types 8–12 only. No invented DOI. **No SIGN lifts HOLD implement
> for this leftover.** Named linear fallback stays named. No GEO-TIN
> 15–17. No type-10 reader PR. No second CurvePolygon type. No priority.

topics: arc, wkt
claimId: none
witness: none

## Destination

**Name the silent POLYGON-collapse leftover so the next `/implement`
cannot steal `#509`, steal COMPOUNDCURVE ticket 30, invent a second
CurvePolygon type, or treat I/O round-trip as overlay honesty.**

SQL/MM `ST_CurvePolygon` (ISO/IEC 13249-3 §4.2.15 / §8.2.1; WKB type
10) is already a first-class type. Rings are ST_Curve values that are
rings (closed ∧ simple). The ask is honesty: a curve polygon stays a
curve polygon. Silent emit of `POLYGON` / `LinearRing` for overlay,
hull, or TestBuilder is a refuse. Named `Linearize` / `toLinear` /
`chord_approx_ring` is not that refuse. JTS
`Polygon.getExteriorRing()` returning a derived `LinearRing` is the
named Option-A contract, not the leftover — the true shell is
`getExteriorCurve()`.

This letter does not retire a tracker and does not mint an epic.
Epic creation stays owner-scope. `#509` stays OPEN.

## Three words that say "collapse"

| Word | What it is | Park | Status |
|---|---|---|---|
| Silent POLYGON collapse | Overlay / hull / TestBuilder eat `CURVEPOLYGON` and emit `POLYGON` / `LinearRing` chords with no stamp; or treat JTS `getExteriorRing()` as if it were the curve | leftover **silent-polygon-collapse** | Named here. HOLD implement stands. Ticket 32. Distinct from COMPOUNDCURVE ticket 30 (lineal chord Flatten). |
| Named linear fallback | `Linearize` / `toLinear` / `chord_approx_ring` / OverlayNGCurve `APPROX` + `isApproximate()` | technique (named) | Allowed. NTS `ILinearizable<Polygon>.Linearize`. JTS `toLinear`. Coq `CurveLinearise.v : to_geometry_outer_ring_closed` and `CurveLinearise.v : chord_approx_ring_closed`. |
| Structural F-CP / Jordan | Rings stay `Curve` on NTS; Coq `CurvePolygon` is structural; true-region waits on `#509` | already landed / `#509` | NTS `CurvePolygon.ExteriorRing => _shell` (`Curve`). `CurveGeometry.v : valid_curve_polygon` is structural only. V-CP Jordan is `#509`. Do not remint `#509`. |

I/O type identity is not op honesty. FCP-S keeps WKT
`CURVEPOLYGON((CIRCULARSTRING …))` exposing `getExteriorCurve()` as a
curve and writing CIRCULARSTRING back. WKB/WKT may round-trip type 10
and still lie in overlay unless the op carries a path stamp (sibling
card QG-CURVE-CHORD; HOLD implement; does not join this leftover).

## What is already true

| Surface | Pin | Honesty |
|---|---|---|
| 60s reader | `docs/HELP.md` BIM Bea card; `docs/READING-GUIDE.md` | Names CIRCULARSTRING / COMPOUNDCURVE / CURVEPOLYGON and that Flatten-to-chords is lossy. Method name on the NTS tree is now `Linearize`, not `Flatten` — name drift, not a drop. |
| SQL/MM type | `CurveGeometry.v : valid_curve_polygon` | Structural only (each ring's arcs valid). Clause book: `docs/iso13249-3-curve-type-bindings-2026-08.md` §2.3. Cite 13249-3, not 19125-2. Rings are ST_Curve, closed ∧ simple. |
| Ring simplicity | `CurvePolygonSimple.v : curve_polygon_outer_not_simple_of_witness` | Witness-sound outer not-simple. Not Jordan. |
| Holes-inside-shell floor | `CurvePolygonValid.v : valid_curve_polygon_cp` / `CurvePolygonValid.v : valid_curve_polygon_cp_hole_witness` | Conservative inscribed control polygon. True-region waits on `#509`. |
| Named Option B bridge | `CurveLinearise.v : to_geometry_outer_ring_closed` | Combinatorial faithfulness of the *named* linearise of the outer ring. Not silent POLYGON emit. |
| Chord-only rect | `RelateCurveAreaPoint.v : valid_rect_curve_polygon` | A rectangular `CurvePolygon` of chords. No curve→matrix soundness. |
| Linear winding | `WindingNumber.v : winding_decides_membership` | Linear ring. Not curve Jordan. Do not treat as `#509`. |
| Kit-completeness fog | `OverlayTouchRow.v : phase0_relation_complete_hypothesis_refuted` | CUP/CAP/XOR/SUB + T-in/T-out stays fog. T-in/T-out is vocabulary this corpus does not have. "Complete" has a refuted ancestor. |
| NTS F-CP contract | `CurvePolygon` extends `Surface<Curve>` | `ExteriorRing => _shell` stays `Curve`. Never collapsed to `LinearRing` at the accessor. Off `develop` without further design. |
| JTS Option A | `CurvePolygon` extends `Polygon` | Legacy `getExteriorRing()` is a derived `LinearRing` from control points (not `toLinear`). True arc is `getExteriorCurve()`. Named, not silent. |
| FCP-S I/O | Notion FCP-S; WKB type 10 | Exterior stays a curve on WKT read. HOLD type I/O 13–17 / 18–20. Off #7. Do not mark pass. |
| F-CP / V-CP TRIAGE | `#64` residue / `#509` | Structural model + validity/simplicity witness-sound; true-region deferred. This letter does not flip those rows. |

## Leftover table

Parks follow ADR-0002. Value and priority are orthogonal. This letter
does not set WSJF.

| Id | Leftover | Kind | Park | Status | Do not |
|---|---|---|---|---|---|
| silent-polygon-collapse | Silent emit of `POLYGON` / `LinearRing` at overlay / hull / TestBuilder, or treating `getExteriorRing()` as the curve | CRV-CP | technique | Named here. HOLD implement stands (no Architect SIGN on this leftover). Ticket 32. | steal `#509`; steal COMPOUNDCURVE ticket 30; treat FCP-S I/O as overlay honesty; merge into JTS #7; mint a second CurvePolygon type |
| — | V-CP Jordan true-region | `#509` | technique | Already the V-CP true-region epic. Stays OPEN. | remint `#509`; pull Jordan into CRV-CP |
| — | COMPOUNDCURVE flatten-elimination | CRV-CC / ticket 30 | technique | Sibling in this packet. Lineal compound chord Flatten. | steal ticket 30 for a CURVEPOLYGON site |
| — | QG-CURVE-CHORD path stamp | sibling board card | sequencing | HOLD implement. Does not join silent-polygon-collapse. | invent EXACT / NAMED-APPROX / CHORD-PATH CI on this letter |
| — | FCP-S WKT shell | sibling visual case | sequencing | I/O identity. HOLD type I/O 13–17 / 18–20. Do not mark pass. | open a type-10 reader PR to "see" it |
| — | TestBuilder draw CurvePolygon | sibling TB-T card | sequencing | Never POLYGON. TB-\* is not proof-relevant in TRIAGE. | treat draw UX as this leftover |
| — | Kit-completeness (CUP/CAP/XOR/SUB + T-in/T-out) | fog | research | T-in/T-out is missing vocabulary. Completeness has a refuted ancestor. | mint a completeness epic; remint leftover `Ⅰ`–`Ⅹ` |
| — | JTS #27 OverlayNG-for-circles (Option B) | JTS #27 | sequencing | **Out.** | fold into this map; merge into #7 |
| — | JTS #38 package-private curve DCEL (Option C) | JTS #38 | sequencing | Off #7 unless PO says merge. No public noder. | make the DCEL public |
| — | Second CurvePolygon type | board HOLD | sequencing | The existing NTS / JTS / Coq carriers stay. | mint a parallel type; join GEO-TIN 15–17 |
| — | WKB type-10 reader PR | I/O | sequencing | Type 10 is already named on #7 I/O 8–12. | open a reader-only PR from this letter |

## Decisions so far

- CURVEPOLYGON is SQL/MM ISO/IEC 13249-3, WKB 10. Cite that standard.
  There is no DOI. Do not cite ISO 19125-2.
- Bea 60s reader is met on Proofs HELP + READING-GUIDE.
- Silent POLYGON collapse is the one leftover this card owns. It is not
  leftover `Ⅵ`, not `CRV-CP` as a Proofs claimId, not `#509`, and not
  a new epic.
- Named linear fallback stays named. Silent POLYGON emit is a refuse.
- JTS `getExteriorRing()` → `LinearRing` is named Option A. The
  leftover is treating that accessor as the curve, or emitting
  `POLYGON` from an op with no stamp.
- NTS F-CP (`ExteriorRing` typed `Curve`) is already the structural
  contract. This letter does not remint it.
- `#509` owns Jordan true-region. F-CP / V-CP TRIAGE rows do not flip.
- Kit-completeness stays fog.
- COMPOUNDCURVE ticket 30 stays a lineal Flatten leftover.
- JTS #27 is out. JTS #38 stays off #7. No public noder.
- HOLD merge into #7. HOLD a second CurvePolygon type. HOLD implement
  for ticket 32. No priority from this letter.

## Fog

- **Which NTS / JTS overlay entry still emits POLYGON without a stamp**
  is an engine grill for a later implement, not a Coq lemma in this
  letter. HOLD implement stands until Architect SIGN.
- **HELP still says `Flatten()`** while the NTS method is `Linearize`.
  Name drift. Do not treat it as Bea dropping CURVEPOLYGON again.
- **T-in / T-out** is vocabulary this corpus does not have.
- **QG-CURVE-CHORD** stays a separate card.

## Frontier

Ticket 31 (this chart) is closed. Ticket 32 names the leftover.
HOLD implement stands. Next useful session is Architect SIGN on
ticket 32, or stop. Do not `/implement` ticket 32 from this letter.

Sibling COMPOUNDCURVE tickets 29 / 30 live in this packet
(`map-compoundcurve.md`). Numbered 31 / 32 so the leftovers stay
distinct.

```
HELP / READING-GUIDE ════════════ CURVEPOLYGON named ── Bea met
CurveGeometry + CurvePolygon* ══ structural F-CP / V-CP floor
I/O type 10 / FCP-S ════════════ identity, not op honesty ── off #7
#509 V-CP Jordan ══════════════ true-region ── stays OPEN
CRV-CC ticket 30 ══════════════ lineal Flatten ── sibling, not this

silent-polygon-collapse ────── ticket 32 ── HOLD implement stands
#27 ── out
#38 ── Option C DCEL ── off #7 ── no public noder
second type / type-10 reader / GEO-TIN 15–17 ── HOLD
kit-completeness ── fog
```

## Do not

- Remint `#509` / `69-a` / `508-*` / `522-*` / leftover `Ⅰ`–`Ⅹ`.
- Mint leftover `Ⅺ` or `CRV-CP` as a Proofs claimId.
- Mint a GitHub child from this map.
- Implement silent-polygon-collapse in this letter.
- `/implement` ticket 32 while HOLD implement stands.
- Steal COMPOUNDCURVE ticket 30.
- Merge into JTS #7. Open a type-10 reader PR. Join GEO-TIN 15–17.
- Invent a DOI. Cite 19125-2. Copy clothoid Zenodo.
- Treat `WindingNumber.v : winding_decides_membership` as curve Jordan.
- Treat FCP-S I/O as overlay honesty.
- Flip F-CP / V-CP TRIAGE status.
- Set backlog priority.
