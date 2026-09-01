# Flatten-elimination — silent COMPOUNDCURVE chord path

**Type:** implement · **Map:** [COMPOUNDCURVE](../../map-compoundcurve.md)
**Claimed:** implement 2026-09-01 · **Closed:** 2026-09-01 (GEOS named the leftover)
**Blocked by:** ~~[Chart COMPOUNDCURVE flatten-elimination](29-compoundcurve-flatten-chart.md)~~ ✔
**claimId:** none · **GitHub:** none · **witness:** none

Board card: Notion CRV-CC. Architect SIGN lifted HOLD implement for
**this leftover only**.

## Ask

Name or refuse the silent chord path that still eats
`COMPOUNDCURVE` at overlay, hull, or TestBuilder without a stamp.
A compound stays a compound. Named `Linearize` / `toLinear` /
`chord_approx_ring` / OverlayNGCurve `APPROX` + `isApproximate()`
stays named. I/O type identity is not op honesty.

Cite ISO/IEC 13249-3. No DOI. No 19125-2.

## In scope

- Engine grill: NTS overlay / hull / TestBuilder sites that still
  consume `CompoundCurve` as `Coordinate[]` without calling
  `Linearize`. JTS OverlayNGCurve cells that densify with
  `isApproximate()=false`.
- One Proofs honesty pin **only if** it is a new statement. Do not
  remint `HullExactExtrema.v : h_cc_still_densify`.
- Keep the result type named (COMPOUNDCURVE vs LineString of chords).

## Out of scope

- Merge into JTS #7. Type-9 reader PR. GEO-TIN 15–17.
- A second CompoundCurve type. Public noder. JTS #27. JTS #38.
- H-CC hull (`424-b` / #424 / JTS #6). QG-CURVE-CHORD path-stamp CI.
- Remint `615-b`, `LECFlattenRow.v : empty_disk_flatten_iff`,
  `508-*`, leftover `Ⅰ`–`Ⅹ`, `69-a`.
- Koc railway compound. Setting WSJF.

## Done when

A later `/implement` can point at one named site (engine or Coq)
and say whether it refused or stamped. This ticket stays open until
that letter lands. Do not mint `CRV-CC` as a Proofs claimId unless
that letter names a new lemma.

## Resolution

**Implemented 2026-09-01 on GEOS** (`cursor/sqlmm-type-honesty-ccfa`).

Named site: `geos::util::ensureNoCurvedComponents` (hull / centroid /
buffer / …). It **refuses** a `COMPOUNDCURVE` with curved components
and names `getLinearized` as the only allowed linear fallback.

GEOS OverlayNG already keeps `COMPOUNDCURVE` / `CIRCULARSTRING` when
`CurveToLineParams` is unset. C API overlay does not flatten just
because those params are registered.

H-CC exact hull stays on tracker 424
(`HullExactExtrema.v : h_cc_still_densify`). No new Coq lemma.
claimId: none. witness: none.
