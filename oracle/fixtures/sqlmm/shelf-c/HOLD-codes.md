<!-- doc-kind: guide -->
# HOLD WKB codes (not signed I/O)

claimId: none (docs)

ISO/IEC 13249-3 §5.1.68 Table 15 codes that this factory must **not**
advertise as signed I/O (JTS #7 contract; `SqlMmSignedTag.v`
`sqlmm_hold_code`):

- **13–17** — Triangle / PolyhedralSurface / TIN / … as HOLD
- **18–21** — preview codes (ellipse / Bézier / NURBS theatre)

Also not signed:

- **Circle-as-18** — CIRCLE is a signed *name* with κ=none
- **Clothoid-as-22** — CLOTHOID is a signed *name* with κ=none
- **WKB 13 as GEODESICSTRING** — well-formed geodesic bags `MkChord`;
  τ=`TagLineString`; emit is LINESTRING / code 2

Shelf C may later mint labelled `HOLD-*.wkb.hex` dumps. This slice
names the HOLD and stops. Do not add those dumps to the signed
round-trip suite.
