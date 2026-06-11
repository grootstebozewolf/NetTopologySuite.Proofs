# Phase 4 Audit: Native Curve Primitives in NetTopologySuite

**Status**: Strategic scoping document (not formal proof work)
**Date**: May 2026
**Goal**: Understand why native curve support has been stalled for ~5 years and decide how (or whether) the formal corpus should engage with it.

> **Status note (2026-06-09).** §4/§6 record the May-2026 stance — chord-first
> Option B, "do *not* prematurely abstract the predicate signatures,
> re-evaluate at the start of Phase 4." Phase 4 has since arrived and the
> issue-owner chose **Option A (exact arc primitives)**, so that recommendation
> is overtaken (the chord/Option-B line also still stands; the two coexist):
>
> - **Landed (Qed-closed):** `theories/Atan2.v`, `theories/AngleBetween.v`,
>   `theories/ArcLength.v` (`r·θ`), and the binary64 in-circle layer
>   `theories-flocq/InCircle_b64_exact.v` — full-plane `b64_inCircle` sign
>   exactness at **3 axioms** (same exact-ℤ-determinant route as
>   `b64_orient2d_exact`; see `docs/phase0-completion.md`) — plus arc-line
>   Scope A (`theories-flocq/ArcLineIntersect_b64_exact.v`). The R-side arc
>   predicates `ArcOrient.v` / `ArcIntersect.v` / `ArcHotPixel.v` /
>   `ArcChordApprox.v` / `ArcOverlay.v` are Qed.
> - So §6's "what this defers — concrete `Orient_arc_*` / `HasArcIntersect`
>   modules" is partly discharged. Per-issue status:
>   `docs/verified-claims.md` Phase 4, `docs/issue-64-arc-primitives-triage.md`,
>   and `../TRIAGE_NTS_JTS_ISSUES.md`.

## 1. Executive Summary

SQL/MM Spatial (ISO/IEC 13249-3) defines the curve types (`CircularString`, `CompoundCurve`, `CurvePolygon`) atop OGC Simple Feature Access's abstract `Curve`/`Surface` hierarchy — these are **not** OGC SFA types (see the §6 attribution note in `docs/audit-phase3-overlay.md`) — and NTS *does* have `Curve`, `CircularString`, and `CompoundCurve` as first-class subclasses of `Geometry`. The stall is one level down: curves exist at the type level but cannot survive contact with the algorithm layer because every major operation consumes and emits `Coordinate[]` via `SegmentString` / `NodedSegmentString`. Linearisation is not a preprocessing choice — it is architecturally enforced. The existing extension (`NetTopologySuite.Curve`) wraps every overlay call in a `Flatten()` that converts curves to chords *before* any computation runs. The robust-predicates layer (`Orientation.Index`, `RobustLineIntersector`) is the only place curves could plug in without rewriting the data plane.

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

## 6. Dovetailing Status (2026-05-16 — documentation-only)

Per §4's stance ("do *not* prematurely abstract the predicate signatures") the corpus has now applied a **documentation-only** dovetail rather than introducing typeclass shells. Three anchors are in place:

- **`theories-flocq/Orient_b64_exact.v`** — chord-paradigm dovetail block between the last theorem and the axiom audit. Names the chord carrier (`BPoint`), the chord-chord witness (`cross_R_BP`), and the three pieces an arc-bearing variant would need (an `ArcTriplet` carrier, a separate `b64_orient2d_arc` primitive with its own Stage-A filter, and a chord-refinement bridge theorem). Explicitly *no* `HasOrient` typeclass introduced.
- **`theories-flocq/Orient_b64_R.v`** — chord-paradigm scope callout in the header. Notes that the four R-side identities (antisymmetry / cyclic / translation / vertex coincidence) would *not* generalise without re-proof on an arc-aware witness, and points downstream to the Orient_b64_exact dovetail.
- **`theories-flocq/Intersect_b64_exact.v`** — refined the existing `HasIntersect` aspirational comment. Previous wording suggested "a future `ArcTriplet` instance" of the same typeclass; this was confused because the 4-point signature `T -> T -> T -> T -> binary64` is chord-paradigm-specific (two chord-chord segments = four endpoints). The arc-bearing analog needs a **parallel** typeclass with a 2-argument signature (two arcs, not four points), not a new instance of `HasIntersect`. The two typeclasses coexist; bridging between them composes refinement bounds with the existing chord instance.

`coqchk -silent -o` post-dovetail diff against the pre-dovetail baseline: **zero output**. Pure documentation, byte-identical axiom closure.

What this preserves:
- No abstraction tax paid today on predicate signatures.
- The seam is named at the source-file level, not just in this audit document, so future arc-aware work has visible landing points.
- A correctness slip in the existing `HasIntersect` aspirational comment is fixed (its old `ArcTriplet` instance hint did not match the 4-point signature).

What this defers:
- Any concrete `HasArcIntersect` / `Orient_arc_*` modules.
- Any refinement-bridge lemma between chord and arc paths.
- Re-evaluation at the start of Phase 4 once a consumer (e.g. `NetTopologySuite.Curve`, an upstream PR) is asking for arc-aware predicates.

### 6.1 Clothoid case — external-development citation seam

The `Intersect_b64_exact.v` dovetail block now covers a **family** of parallel typeclasses (chord today, arc / clothoid / ... as future hooks), not just an arc-arc analog. The clothoid case is the first concrete future hook where an external formal-verification effort has already discharged the R-side mathematics:

- **External project**: [`grootstebozewolf/clothoid-halley-coq`](https://github.com/grootstebozewolf/clothoid-halley-coq) (Merkator Group, 2026). Coq 8.13.1 / 8.20.1 + Coquelicot 3.x. Proves the six derivative identities for the chord-length residual `f(L) = L²(P²+Q²) - d²` used in Halley iteration for the G¹ Hermite clothoid interpolation problem (Bertolazzi-Frego 2015 / 2018). No `Admitted`, no `Axiom` beyond the four standard Coquelicot axioms.
- **Stack mismatch (porting cost)**: that project uses Coquelicot's real-analysis primitives (`RInt`, `is_derive`, `Derive`). Our corpus targets Rocq 9.1.1 + Flocq 4.2.2. The R-side identities would need re-proof in Flocq's native `Reals` framework (Coquelicot's `RInt` ↔ `RiemannInt`, `is_derive` ↔ Flocq's derivative predicate). Estimated ~3-5 days of mechanical translation: the tactic recipes (`auto_derive`, `Derive` rewrites, `ring`) are tactic-name preserved.
- **Licence**: clothoid-halley-coq is **proprietary, source-available** (`LicenseRef-Merkator-Proprietary-NoAITraining`) with explicit permission for *academic citation* and *unmodified reproduction of paper results*. Theorem statements may be **cited** and parallel proofs **re-derived** in our BSD-3-Clause corpus; theorem text and proof scripts may **not** be copied without a separate licence.
- **Differential-testing oracle already available**: the 9,058-record `golden_vectors.json` from ProRail Spoorgeometrie clothoid transitions, bit-identical across Python / C# / Java / TypeScript implementations within 1e-9 m chord-length agreement and matching iteration counts. Symmetric infrastructure to our `oracle/extracted.ml` (see `theories-flocq/Validate_binary64_extract.v`): a future `b64_clothoid_intersect` extraction can be bit-compared against this oracle before any Flocq-side soundness claim is made.
- **Termination model**: the L-form residual under the monotone-branch precondition (from clothoid-halley-coq's filtering pipeline) converges to machine precision in ≤4 Halley iterations on the empirical 9,058-record corpus (Merkator paper, table 3). In our Rocq formalisation this becomes a **bounded-iteration** termination lemma — not a fixpoint-domain argument — which is structurally simpler than a general convergence proof.

This places clothoid integration **strategically ahead** of the arc-arc case (which has no comparable external formalisation or golden oracle), even though tactically both remain deferred until a downstream consumer appears.

### 6.2 Bridge status (2026-05-16 — bidirectional)

The clothoid-halley-coq corpus released **v1.0.3** (`ffbbf6d`) with a retitle to *"A Verified-Azimuth, Zero-Friction Halley Solver for the Chord-Length Parameter L in Clothoid G¹ Hermite Interpolation"* and a new Section 7 ("Cross-Corpus Bridge to NetTopologySuite") in the accompanying paper. The bridge is now **bidirectional**:

- **clothoid-halley-coq → NetTopologySuite.Proofs**: the paper cites three lemmas from [`theories/Azimuth.v`](../theories/Azimuth.v) by name as scholarly references — `turn_sign_eq_cross`, `sin_half_turn_sq`, `miter_ratio_le_iff` — framing adoption in a pipeline that already uses NetTopologySuite as a **zero-friction call-site substitution** rather than a porting effort.
- **NetTopologySuite.Proofs → clothoid-halley-coq**: `Azimuth.v`'s footer now carries a cross-corpus block (citing v1.0.3 by short SHA) naming the bridge, and `theories-flocq/Intersect_b64_exact.v`'s `HasClothoidIntersect` aspirational comment continues to cite the upstream R-side derivative identities (§6.1 above).
- **Licence preservation**: the clothoid-halley-coq LICENSE file (`f0ca7b1`) added a `CROSS-CORPUS BSD-3-CLAUSE BRIDGE` clause stating explicitly that theorem statements and function signatures from this corpus that the paper reproduces under its scholarly-citation permission "**remain governed by the BSD-3-Clause licence of the Sibling Corpus**". That is, the proprietary licence of the paper does not contaminate the BSD-3 status of the lemmas it cites; readers wishing to use, modify, or redistribute the Sibling Corpus consult this repo's LICENSE only. The "no AI training" reservation of the paper does **not** extend to this repo.

**Next concrete Azimuth.v target** (cross-corpus, optional): the clothoid paper's monotone-branch precondition `|κᵢ L| ≤ π` is connected to `f'(L) > 0` via a continuous-turning monotonicity argument that "lives naturally in Azimuth.v" (paper, Section 7). Formalising that bridge lemma is the obvious next addition to `Azimuth.v` if a downstream consumer wants the Halley termination model machine-checked end-to-end. Not yet on the critical path.

### 6.3 Linearisation-bridge structural faithfulness (CIRCULARSTRING / COMPOUNDCURVE)

`theories/CurveGeometry.v` models a SQL/MM **COMPOUNDCURVE** as `CurveRing := list CurveSegment` (`CSChord` | `CSArc`), with the all-arc case being a **CIRCULARSTRING**, and `to_geometry` / `chord_approx_ring` linearise it (Option B) to a Phase-3 `Geometry`. `theories/CurveLinearise.v` closes the **combinatorial faithfulness** of that bridge: a valid (adjacent + closed) curve ring — circular *or* compound, handled uniformly — linearises to a `ring_closed` Phase-3 ring (`chord_approx_ring_closed`, axiom-free), and hence every outer ring and hole of `to_geometry cg n` is closed for a valid `cg` (`to_geometry_outer_ring_closed`, `to_geometry_hole_ring_closed`). This is the `ring_closed` conjunct of `valid_polygon` for the linearised curve geometry — the curve analogue of `RingExtract.face_walk_closed`, and the structural prerequisite for feeding linearised circularstrings/compoundcurves into the `extract_rings_valid` / overlay machinery. Three-axiom; no Admitted. The remaining curve-side residuals (sagitta/`ring_simple` of the approximation, `hole_inside_outer`) are the same analytic seams tracked elsewhere, not new debt.

## 7. Curve-buffer lane opened (2026-06-11)

The §4 stance ("re-evaluate once a consumer is asking for arc-aware
work") has its first concrete consumer-driven landing beyond the
predicate layer: with issue #64's arc-line Scope B/C closed
(`b64_arc_line_point_{x,y}_forward_error`, absolute `bpow 13`), issue
#65's curve-aware buffer lane is unblocked, and its first proof brick is
in: **`theories/ArcOffset.v`** (Stage 2a-curve seam of
[`buffer-noder-pipeline.md`](buffer-noder-pipeline.md) §2.2). The offset
of a circular arc at signed distance `d` is the concentric radius-`r+d`
arc: exactly-at-distance-`|d|` from the whole source circle (up to the
`d = −r` singularity), tangent a positive multiple of the source tangent
(no kink/reversal), direction reversal past the singularity
(`tangent dot = r(r+d)`), a `Qed` witness that the parallel-curve
property *fails* for `d < −r`, and the `arc_length` offset bridge.
Three-axiom throughout. This stays inside the Option-A/Option-B division
of labour: exact-arc geometry on the R side, chord machinery untouched.
See [`audit-rgr-comparison.md`](audit-rgr-comparison.md) §7 for the
execution log and the remaining #65 ladder (three-point bridge → emitted
edge lists → `CurvePolygon` topology).

Rung 2 (same day): the three-point bridge is closed —
`theories/ArcOffsetThreePoint.v` proves `arc_offset_preserves_arc` (the
radial offset of a valid SQL/MM `CircularArc` is again a valid
`CircularArc`, same `arc_center`, `arc_radius = r + d`; pure rational
arithmetic, extractable) and discharges the circumcenter-uniqueness
lemma `CurveGeometry.v` §2 had deferred
(`equidistant_point_is_arc_center`). Three-axiom. The ladder advances to
emitted edge lists → `CurvePolygon` topology.

Rung 3 (same day): segment-wise COMPOUNDCURVE offset —
`theories/CurveRingOffset.v`. Per-arc validity and segment count survive
(`curve_ring_offset_arcs_valid`); G1 joins with consistent unit normals
offset continuously (`arc_join_offset_continuous`); and the honest
negative `tangent_continuity_insufficient_for_offset` (S-curve/inflection
witness — the offset tears despite tangent-line continuity, the arc-side
JTS#1147 class). Three-axiom. Next: join/cap edge emission for non-G1
joins, all-G1 closedness lifting, `CurvePolygon` topology.

Rung 4 (same day): the ring-level lift — `CurveRingOffset.v` §§5–7. A
uniform normal field makes one join lemma cover all segment-kind
combinations (`segment_join_offset_continuous`), and list induction
yields the capstone `curve_ring_offset_valid`: a smooth (all-consistent-
normals) compound ring offset within the per-arc safety bound is again
a `valid_curve_ring`. Three-axiom. Next: non-G1 join edges, curved
endcaps, `CurvePolygon` topology.

Rung 5 (same day): the round join arc — `CurveRoundJoin.v`. The non-G1
join edge emitted as a valid SQL/MM `CircularArc` with circumcircle
exactly `(P, |d|)` (second consumer of the circumcenter-uniqueness
lemma), splicing onto the adjacent offset segments via the uniform
normal field. Three-axiom. Next: the assembly rung (splice join arcs
into offset rings), curved endcaps, `CurvePolygon` topology.

Rung 6 (same day): assembly capstone — `CurveOffsetAssembly.v`.
`curve_ring_offset_round` splices round-join arcs at non-G1 joins
(abstract G1 decision oracle, spec-conditional only) and
`curve_ring_offset_round_valid` proves the assembled ring is again a
`valid_curve_ring` for arbitrary non-U-turn compound rings;
`offset_walk_smooth_eq_map` shows it conservatively extends the smooth
case. Three-axiom. Remaining: U-turn double-arc joins, curved endcaps,
`CurvePolygon` topology.
