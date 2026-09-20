# Spec — Directed Hausdorff on NTS and GEOS

An implementation spec. Written 2026-09-02 from the grill
([`map-hausdorff-functions.md`](map-hausdorff-functions.md),
Proofs PR 663). This is **not** leftover `Ⅰ`–`Ⅹ`, **not** leftover
`Ⅺ`, **not** a remint of `423-a` / `423-b` / `508-*` / `D-HF` /
`M.1`. It does **not** implement. Tickets live on the Notion
[NTS RGR Board](https://app.notion.com/p/b494beb4c5d04a08886e1169be9b6cb1),
not as GitHub issues and not as scout tickets 39+.

> Grill verdict: the non-discrete class is still missing on NTS
> develop and GEOS. JTS has `DirectedHausdorffDistance` (JTS 1182,
> merged). NTS#812 is open. `GEOSHausdorffDistance` is discrete.

topics: metric
claimId: none (children: `NTS-812`, `GEOS-DHD`)
witness: none

## Destination

Port the JTS locus class — max-min over **every point** of A, not
just vertices — to NTS and to GEOS. Two independent engine letters.
Proofs remaining asks stay the two ticket-10 lines on tracker 423
(densification bound; `HAUSDORFF_DIRECTED` / `HAUSDORFF_SYMM`).
Do not take ticket 10. Do not remint `423-a`.

## Why the grill is the source, not a re-grill

PR 663 named the surface. Do not re-verify these unless the trees
moved:

| Claim | Where |
|---|---|
| JTS locus class | `DirectedHausdorffDistance.java` — `distance` / `distancePoints` / `hausdorffDistance` / `isFullyWithinDistance`; `tolerance` = accuracy in map units |
| NTS develop has discrete only | `DiscreteHausdorffDistance.cs` + TestRunner `DistanceFunctions` |
| NTS#812 API list | open upstream issue; Notion card `NTS-812` |
| `feat/d-hf-curve-hausdorff` is still discrete | `CurveDiscreteHausdorffDistance` arc-length sample |
| GEOS C API is discrete | `GEOSHausdorffDistance` / `Densify` / `WithPoints` → `DiscreteHausdorffDistance` since 3.2 |
| `423-a` is Green | `HausdorffDiscrete.v : directed_discrete_hausdorff_max_min` |

## Contract (both engines)

`h(A,B) = max_{a ∈ A} min_{b ∈ B} ‖a−b‖`. Asymmetric.
Symmetric HD = `max(h(A,B), h(B,A))`. Empty operand → `NaN` (JTS)
or documented equivalent refuse (GEOS C API returns 0 on exception
today; empty must not silently report 0 as a distance).

`tolerance` is **accuracy in coordinate units**, not a densify
fraction in `(0, 1]`. Negative tolerance throws.

Do not say **DHD** as a type name. JTS comments use that
abbreviation for both the discrete value and the locus value.

Class-comment formula `max_a (max_b distance)` is farthest-pair.
Do not copy it. The algorithm is max-min.

### Witness the grill already named

Discrete under-estimate (JTS `DiscreteHausdorffDistance` remarks):

```
A = LINESTRING (0 0, 100 0, 10 100, 10 100)
B = LINESTRING (0 100, 0 10, 80 10)
discrete ≤ 22.360679774997898
locus HD ≈ 47.8
```

Acceptance: locus `h(A,B)` (or symmetric HD, whichever the test
calls) is nearer 47.8 than 22.36. Oriented discrete on the same
pair is not this letter.

JTS core tests live in `DirectedHausdorffDistanceTest`. Port those
pins. Curve bulge / IWD / PERF-GATE tests are JTS-curve (`D-HF` /
`M.1`). They are **not** this spec. Do not remint those cards.

## Slice NTS — `NTS-812`

Board: [NTS #812 · DirectedHausdorff port](https://app.notion.com/p/3b11c9833b0681aa9312e5e15b19f5da).
Already red. Do not mint a second parent.

**Branch.** New `cursor/<name>-ccfa` off NTS `develop`. Not the
SQL/MM honesty branch. Not `feat/d-hf-curve-hausdorff`.

**File.** `src/NetTopologySuite/Algorithm/Distance/DirectedHausdorffDistance.cs`

**API** (from NTS#812 / JTS):

```
Distance(A, B)
Distance(A, B, tolerance)
DistancePoints(A, B)
DistancePoints(A, B, tolerance)
HausdorffDistance(A, B)
HausdorffDistancePoints(A, B)
IsFullyWithinDistance(A, B, maxDistance)
IsFullyWithinDistance(A, B, maxDistance, tolerance)
new DirectedHausdorffDistance(B)  // prepared target
  FarthestPoints(A)
  IsFullyWithinDistance(A, maxDistance)
```

**Also.** Port `DirectedHausdorffDistanceTest`. Add TestRunner
`directedHausdorffDistance` / `directedHausdorffLine` /
`hausdorffLine`. `clippedDirectedHausdorffLine` is TestBuilder
linear-ref + directed — optional, not the class gate.

**Not this slice.** `feat/d-hf-curve-hausdorff`.
`DiscreteHausdorffDistance.OrientedDistance`. `HausdorffSimilarityMeasure`
stays densified discrete unless a later letter asks. JTS
`exactOrientedPoints` (two certified curve pairs) is `D-HF` / `M.1`,
not NTS#812.

**Gate.** Class exists on develop-equivalent; NTS#812 API compiles;
core tests ported; the 22.36-vs-47.8 pair fails discrete and passes
locus. Flip Notion `NTS-812` to green only when that is true.

## Slice GEOS — `GEOS-DHD`

Board: created by this spec (see Notion tickets below). No GEOS
card existed.

**Branch.** New `cursor/<name>-ccfa` off GEOS `main`. Not the
SQL/MM honesty branch.

**C++.** `include/geos/algorithm/distance/DirectedHausdorffDistance.h`
+ `src/algorithm/distance/DirectedHausdorffDistance.cpp`. Same
public verbs as JTS (`distance`, `distancePoints`,
`hausdorffDistance`, `isFullyWithinDistance`, prepared target).

**C API — new symbols.** Do **not** change
`GEOSHausdorffDistance` / `Densify` / `WithPoints` (discrete since
3.2). Add:

| Symbol | Meaning |
|---|---|
| `GEOSDirectedHausdorffDistance` (+ `_r`) | `h(A,B)` |
| `GEOSDirectedHausdorffDistanceWithPoints` (+ `_r`) | realizing pair |
| `GEOSDirectedHausdorffDistanceWithin` (+ `_r`) | `isFullyWithinDistance` |
| `GEOSSymmetricHausdorffDistance` (+ `_r`) | `max(h(A,B), h(B,A))` — new name so it cannot steal `GEOSHausdorffDistance` |

Optional accuracy overloads take a map-unit `tolerance`, not a
densify fraction.

**geosop.** New op (`directed-hausdorff` / `symmetric-hausdorff`).
Do not overwrite the existing `hausdorff` op (discrete).

**Not this slice.** Renaming the discrete C API. Curve closed-form
pairs (`D-HF`). Changing buffer XML matchers (they stay densified
discrete on boundaries).

**Gate.** New class + C API + unit tests; existing
`GEOSHausdorffDistanceTest` still discrete; the 22.36-vs-47.8 pair
distinguishes the two. Flip Notion `GEOS-DHD` to green only when
that is true.

## Parks

Do not remint `423-a` / `423-b` / `D-HF` / `M.1` / `NTS-812`. Do
not take tracker ticket 10. Do not mint leftover `Ⅺ` or `CRV-*`.
Do not grow year-1 `CurveSegment`. Do not treat
`Linearise.v : hausdorff_le` as the engine. Notion is the ticket
system. Off JTS #7.

## Notion tickets

| ClaimId | Card | Slice | Blocked by |
|---|---|---|---|
| `NTS-812` | [NTS #812 · DirectedHausdorff port](https://app.notion.com/p/3b11c9833b0681aa9312e5e15b19f5da) | NTS locus class + tests + TestRunner | — |
| `GEOS-DHD` | [GEOS · DirectedHausdorff port](https://app.notion.com/p/3cf1c9833b068108921aee227f1fa84f) | GEOS class + new C API + geosop | — |

Independent. Either engine can land first. Proofs oracle modes are
not a blocker.
