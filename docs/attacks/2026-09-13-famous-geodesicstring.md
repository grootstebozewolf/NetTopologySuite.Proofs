# ATTACK famous-geodesicstring
- claimId: 0007-famous-geodesicstring
- file:lemma: theories/IntakeFamousGeodesic.v:ticket_0007_famous_geodesicstring_qed_or_qex
- class: honesty-park
- epic: ADR-0007
- topic: overlay
- verdict: fixtures-qed / named-qex
- H1-shaped: no

Target behaviour: the two Science / arXiv:1804.07389
(Chabukswar & Mukherjee) endpoints lock as WKT fixtures on
existing μ (`0007-intake-geodesic`). They bag as
`TGeodesicString` `MkChord`-only, same bag as the matching
`LINESTRING`. τ is LINESTRING. This is not an Earth geodesic
length proof.

## Repro

```sh
rg -n '0007-famous-geodesicstring' CONTEXT.md docs/verified-claims.md
rg -n 'GEODESICSTRING \(66.6666666667' tools/WktIntakeWalker/smoke.sh theories/IntakeFamousGeodesic.v
bash tools/WktIntakeWalker/smoke.sh
make host
make ci-guards
```

Expected:

- claimId `0007-famous-geodesicstring` (do not remint
  `0007-intake-geodesic` / #744 or tools #745)
- Water WKT:
  `GEODESICSTRING (66.6666666667 25.2833333333, 162.2333333333 58.6166666667)`
- Land WKT:
  `GEODESICSTRING (118.6333333333 24.55, -8.9166666667 37.0333333333)`
- Each bag-string equals the LineString bag for those points
- `first_slice_tag = Some TagLineString`; `cst_prod_tag = None`;
  no `TagGeodesic`; κ does not gain 13
- Empty / singleton / spiral still `ID_Empty` /
  `ID_BadPointCount` / `ID_SpiralCurve`
- Named QEX uninhabited: Earth length / ETOPO1 / WGS84 /
  branch-and-bound / emit-WKB-13

## What collapses

Silent chord demote framed as “we proved the Science path
length.” `MkGeodesic` / `geodesic_eval` as γ. First-cook
expand. Remint of #744 / #745.

## OUTCOME

QED: both famous fixtures bag as `TGeodesicString` `MkChord`
only, same bag as matching `LINESTRING`; τ honesty; empty /
singleton / spiral Decline names stand.
QEX: Earth great-circle length (~32090 km / ~11241 km) or
angular span (~288°35′ / ~101°6′); ETOPO1 land/water mask /
“longest uninterrupted”; sphere vs WGS84 ellipsoid / geoid;
optimality of branch-and-bound; emit of GEODESICSTRING bytes /
WKB 13 as signed I/O.
