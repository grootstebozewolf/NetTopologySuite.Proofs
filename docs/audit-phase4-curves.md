# Phase 4 Audit: Native Curve Primitives in NetTopologySuite

**Status**: Strategic scoping document (not formal proof work)
**Date**: May 2026
**Goal**: Understand why native curve support has been stalled for ~5 years and decide how (or whether) the formal corpus should engage with it.

## 1. Executive Summary

OGC SFA-CA admits curves at the type level, and NTS *does* have `Curve`, `CircularString`, and `CompoundCurve` as first-class subclasses of `Geometry`. The stall is one level down: curves exist at the type level but cannot survive contact with the algorithm layer because every major operation consumes and emits `Coordinate[]` via `SegmentString` / `NodedSegmentString`. Linearisation is not a preprocessing choice — it is architecturally enforced. The existing extension (`NetTopologySuite.Curve`) wraps every overlay call in a `Flatten()` that converts curves to chords *before* any computation runs. The robust-predicates layer (`Orientation.Index`, `RobustLineIntersector`) is the only place curves could plug in without rewriting the data plane.

## 2. Code & History Archaeology

**Findings from local scout (file:line citations):**

- `Curve` base class merged on `upstream/enhancement/curved` (`0c950b7f`); `CircularString` / `CompoundCurve` exist on `enhancement/curved-circularstring-tin` (`255e00a2`), marked PLAYGROUND. No merge to `develop` in 5+ years.
- `NetTopologySuite.Curve` (this maintainer's extension) implements arcs as 3-control-point primitives (start, on-arc, end) and linearises via `Arc.Linearize(tolerance)` with per-arc sagitta tolerance. Linearisation is invoked at every overlay entry: `CurveGeometryOverlay.cs:36`.
- Upstream JTS (Java) has the same status: `Curve`/`CircularString` base types stubbed in `org.locationtech.jts.geom` but no operation layer supports them natively. PostGIS supports `CIRCULARSTRING` via LWGEOM at the type level, but `ST_Intersection`, `ST_Union`, and `ST_Buffer` all linearise internally before computing.

**Root causes (lift-difficulty table):**

| Layer | Chord Assumption Strength | Lift Difficulty | Concrete Evidence |
|-------|---------------------------|-----------------|-------------------|
| API / Types | Low | Low | `Curve` base class already exists; `CircularString` implemented. Hard-coded type checks (`IsSimpleOp.cs:88`, `BoundaryOp.cs:105`) silently fall through for curves but the type system itself is ready. |
| Robust predicates (orientation, intersection) | Low | Low | `Orientation.Index(p1, p2, q)` (`Algorithm/Orientation.cs:56`) is pure on three coordinates — arc-aware overrides are mechanical. `RobustLineIntersector.ComputeIntersect()` similarly clean. **This is the natural seam.** |
| Noding | High | High | `SegmentString` hardcodes `Coordinate[]` (`Noding/SegmentString.cs:13`). `GetSegmentOctant()` (`:128`) is undefined for arcs. Monotone-chain decomposition (`MCIndexNoder`) assumes X/Y-monotone straight runs — arcs can loop back on either axis. |
| OverlayNG | High | High | `EdgeNodingBuilder.cs:327, 405, 418` does `var pts = line.Coordinates;` then `new NodedSegmentString(pts, info)`. No `CircularString` branch. The entire edge-extraction pipeline assumes a flat `Coordinate[]` representation. |
| Snap Rounding | Medium | Medium | `HotPixel` (`Noding/Snapround/HotPixel.cs:53`) is grid-cell logic; segment-agnostic in principle. The blocker is upstream: snap-rounding consumes `SegmentString`s, so anything fed to it has already been chord-flattened. |
| Test suite & assertions | Very High | High | 117 calls to `.Coordinates` across `NetTopologySuite/test`; assertions rely on exact chord lengths and `Coordinates` returning all geometrically relevant points (false for arcs — a 5-point `CircularString` is 2 arcs, not 5 vertices). |
| `.Curve` extension (workaround) | High | High | `Flatten()` called at every overlay entry (`CurveGeometryOverlay.cs:36`). The extension empirically proves the data-plane blocker: it exists, it works, and it linearises on entry because no other path is available. |

## 3. Blockage Diagnosis

**Primary blocker**: **Architectural.** Curves exist at the type level but cannot reach the algorithm layer because the data structure that carries geometry through every operation (`Coordinate[]` inside `SegmentString` / `NodedSegmentString`) is structurally incapable of representing an arc. Linearisation is therefore not a preprocessing choice — it is forced at every entry point.

**Key insight**:
> "The chord paradigm is sticky not because arcs are impossible, but because **every algorithm beneath the geometry API consumes and emits `Coordinate[]` via `SegmentString`, so curves must be flattened before any computation can run — even when both endpoints of the pipeline could in principle handle them.**"

The `NetTopologySuite.Curve` extension is the empirical proof: it exists, it works, and it linearises every input. That's not a workaround — it's the only path the architecture allows.

## 4. Formalization Consequences

**Recommended stance for Phases 2/3: Hybrid (B-leaning).**

- **Option A (concrete, chord-first) is the right tactical choice for the next 12-24 months.** Phase 2 (HotPixel + snap-rounding) and Phase 3 (proper-crossing overlay) operate inside the `Coordinate[]` data plane. Trying to abstract over straight-vs-arc here would balloon the proof obligations without any consumer ready to use the generic form.
- **Option B (generic) is the right strategic option for the predicates layer specifically.** `b64_orient2d` and `b64_intersect_point` already operate on triples/pairs of points — the natural place to introduce an `OrientableSegment` typeclass-style abstraction. This is a clean seam: arc-arc orientation reduces to a similar Stage-A filter with bounded-curvature corrections, and the soundness theorems would parameterise cleanly.
- **Concrete first step**: when Phase 1 Coordinate Story lands, *do not* prematurely abstract the predicate signatures. But document in `Orient_b64_R.v` and `Orient_b64_exact.v` that the soundness theorems are stated over abstract points (`BPoint`), and a future arc-bearing variant could specialise the cross-product witness. That keeps the door open without paying the abstraction tax now.

**Decision**: Proceed with concrete chord-first formalization for Phases 2 and 3. Keep predicate signatures (`BPoint`-based) generic enough that an arc-bearing implementation can be added later without breaking existing proofs. Re-evaluate at the start of Phase 4 once we know whether anyone (the user's own `.Curve`, an upstream PR, a downstream consumer) is asking for arc-aware predicates.

## 5. Tripwire & Success Criteria (5-year bet)

**Success (by ~2031)**:
- A Qed-closed native arc-arc or arc-segment orientation primitive exists in the corpus.
- At least one of {upstream NTS, JTS, GEOS, PostGIS} has shipped native curve support in *one* algorithm (likely intersection or boundary), and the formal corpus is referenced as soundness evidence.
- `NetTopologySuite.Curve` no longer needs `Flatten()` at every overlay call — at least the predicate layer routes through arc-aware versions.

**Failure (consider fork)**:
- All four upstream projects still linearise everywhere at the algorithm boundary.
- The formal corpus has only ever been used for the chord-only predicate layer.
- `Curve` / `CircularString` are still marked PLAYGROUND on a 10-year-old branch.

**Personal tripwire**: If by 2031 the failure conditions hold, treat the chord paradigm as load-bearing for the foreseeable future. Forking to build an arc-native geometry stack with the formal predicates as the foundation becomes a legitimate strategic option, not an emotional reaction.
