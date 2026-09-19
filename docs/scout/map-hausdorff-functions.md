# Grill — HausdorffDistance functions

A grilling record. Charted 2026-09-02. This is **not** leftover `Ⅰ`–`Ⅹ`,
**not** leftover `Ⅺ`, **not** a remint of `423-a` / `423-b` / `508-*`,
and **not** an NTS port. It does **not** grow `CurveSegment`. It does
**not** treat `Linearise.v : hausdorff_le` as the engine.

> Formal cluster: Proofs [#423](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/issues/423)
> (`topic: metric`). Engine ask already named:
> [NTS#812](https://github.com/NetTopologySuite/NetTopologySuite/issues/812)
> (open) ← JTS [#1182](https://github.com/locationtech/jts/issues/1182)
> (merged). Ticket 10 already names the two remaining Proofs asks
> (densification bound; `HAUSDORFF_DIRECTED` / `HAUSDORFF_SYMM`). Do
> not take ticket 10. Do not remint `423-a`.

topics: metric
claimId: none
witness: none

## Destination

**Name the Hausdorff function surface so “the non-discrete
version” cannot be mistaken for oriented discrete, densified
discrete, or `feat/d-hf-curve-hausdorff`.**

## Verdict

The non-discrete class is **still not on NTS develop**. It is also
absent from GEOS. JTS core has it: `DirectedHausdorffDistance`.
NTS develop and GEOS ship only `DiscreteHausdorffDistance` (vertex
max-min, optional densify fraction). NTS remote
`feat/d-hf-curve-hausdorff` is still discrete — it samples
`CircularString` / `CompoundCurve` by **arc length**
(`CurveDiscreteHausdorffDistance`). That is not the JTS locus class.

`423-a` (`HausdorffDiscrete.v : directed_discrete_hausdorff_max_min`)
is the discrete max-min, already Green. It does not close the
continuous engine port and does not close the densification bound.

## Three words that say “Hausdorff”

| Word | What it is | Engine home | Status |
|---|---|---|---|
| Discrete Hausdorff | Vertex (optionally densified-segment) max-min. `DHD ≤ HD`. Approaches HD as densify fraction → 0 | JTS / NTS / GEOS `DiscreteHausdorffDistance` | Ported. NTS TestRunner + `HausdorffSimilarityMeasure` + buffer validators live here |
| Oriented discrete | One-sided discrete (`orientedDistance`). Still vertices / densified chords | JTS + NTS `DiscreteHausdorffDistance` | Ported. Not the locus class |
| Directed Hausdorff | Locus max-min over **every point** of A. Asymmetric. Symmetric HD = max of both directions. `isFullyWithinDistance` short-circuits | JTS `DirectedHausdorffDistance` only | **Unported** on NTS develop and GEOS. NTS#812 still open |

Do not say **DHD** as a type name. JTS `DiscreteHausdorffDistance`
uses DHD for the discrete value; JTS `DirectedHausdorffDistance`
uses DHD for the directed locus value. The collision is in the
upstream comments.

## Function inventory

### JTS core

`modules/core/.../algorithm/distance/`

| Class / method | Kind | Notes |
|---|---|---|
| `DiscreteHausdorffDistance.distance(A,B)` | discrete, symmetric | max of both oriented discrete |
| `DiscreteHausdorffDistance.distance(A,B, densifyFrac)` | densified discrete | fraction in `(0, 1]` — **not** map units |
| `DiscreteHausdorffDistance.orientedDistance` | oriented discrete | one-sided |
| `DiscreteHausdorffDistance.orientedDistanceLine` | realizing pair | |
| `DiscreteHausdorffDistance.exactOrientedPoints` | laser, two certified pairs | package-visible. Disc–disc or single-arc–segment. `DirectedHausdorffDistance` consults this first |
| `DirectedHausdorffDistance.distance(A,B)` | directed locus | `NaN` if either empty. Prepared: `new DirectedHausdorffDistance(B)` then `farthestPoints(A)` |
| `DirectedHausdorffDistance.distance(A,B, tolerance)` | directed locus | `tolerance` = **accuracy in coordinate units**, not a densify fraction |
| `DirectedHausdorffDistance.distancePoints` | realizing pair `[farthest A, nearest B]` | |
| `DirectedHausdorffDistance.hausdorffDistance` | symmetric locus | `max(h(A,B), h(B,A))` |
| `DirectedHausdorffDistance.hausdorffDistancePoints` | realizing pair of the larger direction | |
| `DirectedHausdorffDistance.isFullyWithinDistance` | predicate | every point of A within `maxDistance` of B. Heuristic short-circuit |

The class comment on `DirectedHausdorffDistance` writes
`max_a (max_b distance(a,b))`. That is farthest-pair, not Hausdorff.
The prose and the algorithm are **max-min**. Do not copy the
max-max formula.

### JTS TestBuilder (`DistanceFunctions`)

Curve operands are linearised (`arc` / `linearizeForDistanceTol`)
before discrete / directed / Fréchet, except `distance` /
`isWithinDistance` (instance methods the curve types override).

| Function | Kind |
|---|---|
| `orientedDiscreteHausdorffDistance` | oriented discrete; CurveExact laser if certified |
| `orientedDiscreteHausdorffLineDensify` | densify **fraction** `(0, 1]` |
| `directedHausdorffDistance(A,B, distTol)` | directed locus; `distTol` = accuracy |
| `directedHausdorffLine` / `directedHausdorffLineTol` | realizing segment, **full extent** (free ends dominate) |
| `hausdorffLine` | symmetric locus realizing segment |
| `clippedDirectedHausdorffLine` | project A onto B first, then directed — path-to-path, not full-extent |
| `frechetDistance` / `frechetDistanceLine` | discrete Fréchet after quadratic linearise |

### JTS curve tests (not a second class)

`DirectedHausdorffDistanceCurveTest` / `BulgeTest` / `IwdTest` /
`PerfGateTest` under `modules/curve`. Public
`DirectedHausdorffDistance` owns Curve\* after linearise or the
two certified closed forms. Public `DiscreteHausdorffDistance`
still sees chords in general.

### NTS develop

| Surface | Kind | Missing |
|---|---|---|
| `Algorithm/Distance/DiscreteHausdorffDistance.cs` | discrete + densify + `OrientedDistance` | no `exactOrientedPoints`; no locus class |
| `Algorithm/Match/HausdorffSimilarityMeasure.cs` | densified discrete | |
| `Operation/Buffer/Validate/BufferDistanceValidator.cs` | discrete | |
| TestRunner `DistanceFunctions` | `DiscreteHausdorffDistance` / `Densified…Line` / `DiscreteOriented…` | no `directedHausdorff*`, no `hausdorffLine`, no `clippedDirected*`, no `isFullyWithinDistance` |

Target named by NTS#812:
`src/NetTopologySuite/Algorithm/Distance/DirectedHausdorffDistance.cs`.
That file is not on `origin/develop`.

### NTS `feat/d-hf-curve-hausdorff` (not develop)

`CurveDiscreteHausdorffDistance` — TAG D-HF, arc-length densify of
CS / CC, fall-through to `DiscreteHausdorffDistance`. Still discrete.
Merging that branch would not close NTS#812.

### GEOS

Last port comment: JTS-1.10 `DiscreteHausdorffDistance`. No
`DirectedHausdorffDistance`.

| Surface | Kind |
|---|---|
| `algorithm::distance::DiscreteHausdorffDistance` | discrete + densify |
| C API `GEOSHausdorffDistance` / `GEOSHausdorffDistanceDensify` (+ `WithPoints`) | discrete, despite the name |
| `geosop` `hausdorff` | discrete |
| Buffer XML matchers | densified discrete on boundaries |

### Proofs #423 (formal, not the engine)

| Already Green | Remaining ask (ticket 10; do not remint) |
|---|---|
| `HausdorffDiscrete.v : directed_discrete_hausdorff_max_min` (`423-a`) | Densification bound landed: `HausdorffDensify.v : densify_step_bound` (line 1); line 2 below remains |
| `HausdorffMetricSym.v` / `HausdorffMetricInstance.v` (HKR symmetrization, discrete instance) | Oracle modes `HAUSDORFF_DIRECTED` / `HAUSDORFF_SYMM` |
| `FrechetDiscrete.v` / `423-b` discrete Fréchet | — |
| `Linearise.v : hausdorff_le` sandwich | **Not** the engine. Do not steal it as the densify bound |

`docs/hausdorff-penetration.md` still says the discrete max-min is
RED-by-design. That sentence is stale (`423-a` is Green). Ticket 10
owns the issue-body resync. This grill does not take ticket 10.

## What a later `/implement` may own

Spec: [`spec-hausdorff-functions.md`](spec-hausdorff-functions.md).
Tickets on the Notion NTS RGR Board (`NTS-812`, `GEOS-DHD`), not
GitHub issues. Do not remint `423-a`. Do not take ticket 10.

## Parks

- Do not remint `423-a` / `423-b`.
- Do not take ticket 10.
- Do not mint leftover `Ⅺ` or `CRV-*` as a Proofs `claimId`.
- Do not grow year-1 `CurveSegment`.
- Do not treat `Linearise.v` as the engine port.
- Cite ISO/IEC 13249-3 only. No DOI dump. Off JTS #7.

## Decisions so far

- Non-discrete = JTS `DirectedHausdorffDistance`. Still unported on
  NTS develop and GEOS.
- Oriented discrete and densified discrete are already on NTS.
- `feat/d-hf-curve-hausdorff` is still discrete.
- `GEOSHausdorffDistance` is discrete.
- Remaining Proofs asks stay the two ticket-10 lines on #423.
