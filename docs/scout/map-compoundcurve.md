# Map — COMPOUNDCURVE flatten-elimination

A wayfinder map. Charted 2026-09-01. This is **not** a `wayfinder:map`
GitHub issue, **not** a remint of `424-b` / `69-a` / `508-*` /
`615-b`, and **not** leftover `Ⅰ`–`Ⅹ`. It does **not** implement
flatten-elimination. It does **not** mint a second CompoundCurve type.
It does **not** merge into JTS #7. Board card: Notion **CRV-CC**.

> Architect SIGN 16 Aug 2026: HOLD implement is lifted for
> flatten-elimination only. HOLD merge into #7. Keep COMPOUNDCURVE /
> CIRCULARSTRING (ISO/IEC 13249-3). Do not silently flatten. Named
> linear fallback stays named. Option C / curve DCEL. No public noder.
> #27 out. #38 off #7. No type-9 reader PR. No GEO-TIN 15–17. Cite
> 13249-3. No DOI. HOLD a second CompoundCurve type. No priority.

topics: arc, wkt
claimId: none
witness: none

## Destination

**Name the flatten-elimination leftover so the next `/implement` cannot
steal a closed letter, invent a second CompoundCurve type, or treat I/O
round-trip as overlay honesty.**

SQL/MM `ST_CompoundCurve` (ISO/IEC 13249-3 §4.2.13 / §7.10.1; WKB type
9) is already a first-class type. The ask is honesty: a compound stays
a compound. Silent chord densify for overlay, hull, or TestBuilder is
a refuse. Named `Linearize` / `toLinear` / `chord_approx_ring` is not
that refuse.

This letter does not retire a tracker and does not mint an epic.
Epic creation stays owner-scope.

## Three words that say "flatten"

| Word | What it is | Park | Status |
|---|---|---|---|
| Silent chord Flatten | Overlay / hull / TestBuilder eat `COMPOUNDCURVE` as `Coordinate[]` / `LineString` chords with no stamp | leftover **flatten-elimination** | Named on GEOS. Ticket 30 closed. `ensureNoCurvedComponents` refuses and names `getLinearized`. NTS/JTS overlay path still `Coordinate[]`. |
| Named linear fallback | `Linearize` / `toLinear` / `chord_approx_ring` / OverlayNGCurve `APPROX` + `isApproximate()` | technique (named) | Allowed. NTS `ILinearizable.Linearize`. JTS `toLinear`. Coq `CurveLinearise.v : chord_approx_ring_closed`. Clothoid / uncertified mix stays named. |
| Member / splice flatten | LEC min-over-members; ISO nested-CC splice into the component list | already landed | `LECFlattenRow.v : empty_disk_flatten_iff`. #615-b nested-CC splice (`2c4c7bc`) is §7.10.1, not chord densify. Do not remint `615-b`. |

I/O type identity is not op honesty. JTS `SqlMmTypes.refuseFlatten` and
`IoFlattenHonestyTest` keep WKT/WKB/GML/KML/GeoJSON from writing a
control polygon. WKB/WKT may round-trip type 9 and still lie in
overlay unless the op carries a path stamp (sibling card QG-CURVE-CHORD;
HOLD implement; does not join this leftover).

## What is already true

| Surface | Pin | Honesty |
|---|---|---|
| 60s reader | `docs/HELP.md` BIM Bea card; `docs/READING-GUIDE.md` | Names CIRCULARSTRING / COMPOUNDCURVE / CURVEPOLYGON and that Flatten-to-chords is lossy. Joost card JOOST-CC-HELP is met on Proofs. Method name on the NTS tree is now `Linearize`, not `Flatten` — name drift, not a drop. |
| SQL/MM type | `CurveGeometry.v` (`CurveRing` = `CSChord` \| `CSArc`) | All-arc ring is CIRCULARSTRING; mixed ring is COMPOUNDCURVE. Clause book: `docs/iso13249-3-curve-type-bindings-2026-08.md` §2.2. Cite 13249-3, not 19125-2. |
| Named Option B bridge | `CurveLinearise.v : chord_approx_ring_closed` | Combinatorial faithfulness of the *named* linearise. Not silent Flatten. |
| Length additivity | `CurveLength.v : curve_length_additive` | Compound = member sum. TRIAGE M-LEN-CC. Do not remint `508-*`. |
| Offset keeps structure | `CurveRingOffset.v : curve_ring_offset_arcs_valid` | Segment count survives. Not overlay honesty. |
| Hull leftover already named | `HullExactExtrema.v : h_cc_still_densify` | CompoundCurve (`h_cc_input`) is not the PR #8 CurveExact cell. H-CC stays on **#424** (JTS #6). Do not remint `424-b`. |
| OverlayNGCurve Phase 0 | `OverlayNGCurve.v : overlayng_curve_phase0_exact_cells` | Self / empty / disjoint / covers collapse without densify. APPROX cells stay named. |
| LEC member flatten | `LECFlattenRow.v : empty_disk_flatten_iff` | Typed min-fold, not chords. |
| Koc railway assembly | `CompoundCurveKoc.v` / `CompoundCurveAssembly.v` | Surveyor's clothoid+arc alignment (EN 13803-1). **Not** SQL/MM `ST_CompoundCurve`. Do not join them. |
| NTS I/O | `WKTReader` / `WKTWriter` / `OgcGeometryType.CompoundCurve = 9` | Type identity. Nested COMPOUNDCURVE rejected as a *member of another* (`ReadRejectsNestedCompoundCurves`); #615-b splices on the foundation branch. Off #7. |
| JTS I/O refuse | `SqlMmTypes.refuseFlatten`; `IoFlattenHonestyTest` | Core writers refuse a CompoundCurve control polygon. Already on the curve branch. No type-9 reader PR from this letter. |

## Leftover table

Parks follow ADR-0002. Value and priority are orthogonal. This letter
does not set WSJF.

| Id | Leftover | Kind | Park | Status | Do not |
|---|---|---|---|---|---|
| flatten-elimination | Silent chord path at overlay / hull / TestBuilder | CRV-CC | technique | Named on GEOS (`ensureNoCurvedComponents` refuse + `getLinearized`). Ticket 30 closed. NTS `Operation/` has no `CompoundCurve` overlay path — the data plane is still `Coordinate[]` (`docs/audit-phase4-curves.md`). JTS OverlayNGCurve kits exist for some CompoundCurve shells; unnamed cells densify with `isApproximate()`. | steal `424-b`; treat I/O refuse as overlay honesty; merge into JTS #7; mint a second CompoundCurve type; remint `615-b` / LEC flatten as this leftover |
| — | H-CC CompoundCurve hull | #424 | technique | Already a leftover of `424-b`. JTS #6. | remint `424-b`; pull H-CC into CRV-CC |
| — | QG-CURVE-CHORD path stamp | sibling board card | sequencing | HOLD implement. Does not join flatten-elimination. | invent EXACT / NAMED-APPROX / CHORD-PATH CI on this letter |
| — | TestBuilder draw CompoundCurve | sibling TB card | sequencing | tb-t-1/2 not SIGNed. TB-\* is not proof-relevant in TRIAGE. | open a type-9 reader PR to "see" it |
| — | JTS #27 OverlayNG-for-circles (Option B, OV-P2) | JTS #27 | sequencing | **Out.** | fold into this map; merge into #7 |
| — | JTS #38 package-private curve DCEL (Option C, OV-P2) | JTS #38 | sequencing | Off #7 unless PO says merge. No public noder. | make the DCEL public; steal leftover kits as this leftover |
| — | Second CompoundCurve type | board HOLD | sequencing | The existing NTS / JTS / Coq carriers stay. | mint a parallel type; join GEO-TIN 15–17 |
| — | WKB type-9 reader PR | I/O | sequencing | Type 9 is already named on #7 I/O 8–12. | open a reader-only PR from this letter |

## Decisions so far

- COMPOUNDCURVE is SQL/MM ISO/IEC 13249-3, WKB 9. Cite that standard.
  There is no DOI. Do not cite ISO 19125-2.
- Joost / Bea 60s reader is met on Proofs HELP + READING-GUIDE.
- Flatten-elimination is the one leftover this card owns. It is not
  leftover `Ⅵ`, not `CRV-CC` as a Proofs claimId, and not a new epic.
- Named linear fallback stays named. Silent Flatten is a refuse.
- Member-min flatten and nested-CC splice are other words. They stay
  where they landed.
- Koc compound curves stay a railway-alignment satellite. They do not
  satisfy CRV-CC.
- JTS #27 is out. JTS #38 stays off #7. No public noder.
- HOLD merge into #7. HOLD a second CompoundCurve type. No priority
  from this letter.
- `/implement 660` on GEOS named the leftover: hull / centroid /
  buffer refuse via `ensureNoCurvedComponents` and stamp via
  `getLinearized`. Ticket 30 closed. See
  [`closed/30-compoundcurve-flatten-elimination.md`](tickets/closed/30-compoundcurve-flatten-elimination.md).
- ST_Clothoid, ST_Circle, ST_GeodesicString, ST_NURBSCurve, and
  ST_SpiralCurve are instantiable in ISO/IEC 13249-3 §4.2.1. They
  are not optional extras. GEOS WKT refuses them as SQL/MM types.
  Oracle mode `SQLMM_WKT` parses type identity (ticket 37). NTS WKT
  names them and refuses (ticket 38), matching GEOS. Do not remint
  `508-*`. Do not grow `CurveSegment`. Not leftover `Ⅺ`.

## Fog

- **Which NTS overlay entry still densifies without a stamp** is an
  NTS/JTS engine leftover, not a Coq lemma. GEOS named the refuse
  (`ensureNoCurvedComponents`) and the stamp (`getLinearized`). The
  audit-phase4 `Flatten()` at `CurveGeometryOverlay.cs:36` names the
  historical `.Curve` extension; this NTS clone has `Linearize` and no
  `Flatten()` on curve types.
- **HELP still says `Flatten()`** while the NTS method is `Linearize`.
  Name drift. Do not treat it as Bea dropping COMPOUNDCURVE again.
- **Option C leftover kits** wait on JTS #38. This map does not level
  them.
- **QG-CURVE-CHORD** stays a separate card.

## Frontier

Ticket 29 (this chart) is closed. Ticket 30 is closed on GEOS:
`ensureNoCurvedComponents` refuses and names `getLinearized`.
Ticket 38 is closed on NTS: `WKTReader` names the §4.2.1 types and
refuses (not `Unknown type`). JTS overlay still has no CompoundCurve
path. Next useful session is a JTS letter, or stop.

Sibling CURVEPOLYGON / MULTICURVE / MULTISURFACE leftovers
(tickets 32 / 34 / 36) are also closed on GEOS in this packet.

```
HELP / READING-GUIDE ════════════ COMPOUNDCURVE named ── Joost met
CurveGeometry + CurveLinearise ═ named Option B bridge
I/O type 9 ════════════════════ identity, not op honesty ── off #7
LEC / #615-b ══════════════════ member/splice flatten ── not this leftover
424-b h_cc_still_densify ══════ H-CC stays on #424

flatten-elimination ────────── ticket 30 closed on GEOS
#27 ── out
#38 ── Option C DCEL ── off #7 ── no public noder
second type / type-9 reader / GEO-TIN 15–17 ── HOLD
```

## Do not

- Remint `424-b` / `69-a` / `508-*` / `522-*` / `615-b`.
- Mint leftover `Ⅵ` or `CRV-CC` as a Proofs claimId.
- Mint a GitHub child from this map.
- Implement flatten-elimination in this letter.
- Merge into JTS #7. Open a type-9 reader PR. Join GEO-TIN 15–17.
- Invent a DOI. Cite 19125-2. Copy clothoid Zenodo.
- Conflate Koc railway compound with SQL/MM COMPOUNDCURVE.
- Treat `LECFlattenRow.v : empty_disk_flatten_iff` as chord honesty.
- Set backlog priority.
