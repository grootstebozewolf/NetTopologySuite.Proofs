# Issue #67 — RelateNG / DE-9IM predicates: research & gap triage

> **Status:** research/reading pass only (no Coq written). Maps issue #67's
> asks against the existing corpus, separates *proven* from *gap*, and
> proposes a risk/cost-ordered plan. Branch: `claude/issue-67-relateng-triage`.
>
> Corpus HEAD at time of writing: `main` after PR #146 (`InCircle_b64_exact`).

## 1. What #67 asks for

Issue #67 ("Immediate") requests mechanically-verified proofs for **RelateNG**
and **prepared-geometry** spatial predicates — the DE-9IM intersection matrix
and the standard relate family (Contains, Intersects, Touches, Disjoint, …).

Concrete goals from the issue body:

1. **DE-9IM matrix computation** — dimensionally-extended 3×3 intersection
   matrix between two geometries (Interior / Boundary / Exterior of A vs B).
2. **Standard predicate semantics** — Contains, Covers, Crosses, Disjoint,
   Equals, Intersects, Overlaps, Touches, Within (and custom matrix patterns).
3. **Boundary handling** — correct treatment of boundary points, endpoint
   touches, and `BoundaryNodeRule` (default MOD2).
4. **Prepared mode** — `RelateNG.prepare(A)` caches spatial indexes; repeated
   `evaluate(B)` must agree with one-shot `relate(A,B)`.
5. **Oracle / differential testing** — extracted or bit-exact reference modes
   for NTS/JTS predicate ports (R-CONT, R-PR, V-CP curve validity, etc.).

**Key external references (triaged):**

| Ref | Status | Relevance |
|-----|--------|-----------|
| [JTS#1175](https://github.com/locationtech/jts/issues/1175) — `computeLineEnds()` skips boundary points on disjoint line components | **Fixed** ([JTS#1200](https://github.com/locationtech/jts/pull/1200)) | Boundary/line-end regression; good counterexample target |
| [NTS#819](https://github.com/NetTopologySuite/NetTopologySuite/issues/819) — prepared A-L cache (JTS#1099) | Open (perf) | Prepared correctness must be **result-independent of cache path** |
| Overlay/relate bugs (#1000, #1122, …) | Mixed | Predicate errors often surface via overlay validity |

## 2. Strategic context already on record

**Phase 3 overlay ≠ Phase 7 predicates.** The corpus has a strong overlay
story (`boolean_op`, `TopologyGraph`, `overlay_ng_correct_conditional`) but
overlay answers *set combination* ("what is A ∪ B?"), while RelateNG answers
*topological classification* ("does A contain B?"). They share noding and
segment intersection machinery but need a **new DE-9IM layer**.

**Reuse spine (already Qed):**

- Segment intersection decision + completeness (`theories/Intersect.v`).
- Point-in-polygon via crossing parity (`Overlay.v` `point_in_ring` /
  `point_in_polygon`).
- Labelled planar graph after noding (`OverlayGraph.v` — edge `in_left` /
  `in_right` flags).
- Conditional point-in-ring ↔ interior (`PointInRingCorrect.v`,
  `JordanCurveSeam.v`, `JCT.v`).

**Hard constraints inherited from overlay/JCT work:**

- Full `point_in_ring_correct` without named hypotheses is **not** closed —
  the parity ↔ interior seam (`parity_characterises_interior_cont_strict`) is
  the genuine JCT content. Predicate proofs that reduce to "point in polygon"
  inherit this seam honestly (conditional headlines or guarded special cases).
- No `RelateNG`, `IntersectionMatrix`, or `DE-9IM` types exist anywhere in
  `theories/` or `theories-flocq/` (grep 2026-06-08: zero hits).

## 3. Per-ask status

| Ask | Status | Anchor (file:line) | Notes |
|-----|--------|-------------------|-------|
| **#1 DE-9IM matrix type + entries** | **ABSENT** | — | No 3×3 dimension matrix (`{0,1,2,F,T}`) or `IntersectionMatrix` record. |
| **#2 Standard predicate definitions** | **ABSENT** | — | No `Contains` / `Disjoint` / `Touches` as formal Props tied to DE-9IM. |
| **#3a Segment intersection (line-line)** | **PROVEN (Qed)** | `Intersect.v:900` (`segment_intersection_decision`), `:243` (`strict_completeness`) | Feeds `Intersects`/`Crosses`/`Touches` for line-line; collinear case closed (`collinear_share_iff_1d_overlap`). |
| **#3b Point-in-polygon (area-point)** | **DEFINED; correctness PARTIAL** | `Overlay.v:183-203` (`point_in_ring`, `point_in_polygon`, `point_in_geometry`) | Algorithm defined; full correctness is conditional on JCT seam (`point_in_ring_correct_jct_cont` in `PointInRingCorrect.v`). |
| **#3c Boundary / endpoint semantics** | **PARTIAL** | `Overlay.v:149` (`edge_crosses_ray` — strict, excludes endpoint on ray) | Generic-position guards documented (`no_horizontal_edge_at`, `ray_avoids_vertices`); no line-end / MOD2 boundary-node formalisation. |
| **#4 RelateNG algorithm** | **ABSENT** | — | No noding + matrix-fill pipeline; JTS uses point-local topology + union semantics for collections. |
| **#5 Prepared-mode correctness** | **ABSENT** | — | NTS#819 is perf-only; proof obligation is `evaluate(B) = relate(A,B)` regardless of cache. |
| **#6 Oracle / extraction** | **ABSENT** | `oracle/driver.ml` | No `RELATE_*` modes; orientation/intersect/oracle pattern exists as template. |
| **#7 Curve-aware predicates (V-CP, R-*)** | **DEFERRED** | `docs/issue-64-arc-primitives-triage.md` | Curve polygons need chord-approx or Option-A semantics before relate on arcs. |

## 4. Inventory of reusable assets

**R-side (`theories/`, 3 axioms, Admitted-free on these modules):**

- `Overlay.v` — `Geometry`, `valid_geometry`, `point_in_ring`, `point_in_polygon`,
  `boolean_op`, `edge_crosses_ray`, `segments_intersect_properly`.
- `Intersect.v` — segment intersection decision, strict/collinear completeness.
- `OverlayGraph.v` — `TopologyGraph`, `EdgeLabel`, `correct_labels_all_ops`.
- `PointInRingCorrect.v` — `segment_crosses_ray` bool soundness, JCT-conditional
  headlines, generic-position guards.
- `Bbox.v` — `bbox_disjoint` (necessary but not sufficient for geometry
  disjoint).

**Flocq layer (`theories-flocq/`):**

- `Intersect_b64.v` / `Intersect_b64_exact.v` — robust segment intersection
  (feeds line-line noding for relate).
- `OverlayCorrectness.v` — conditional overlay headline (not predicate-level).

**Oracle (`oracle/`):**

- `driver.ml` — protocol for ORIENT / INTERSECT / INCIRCLE / …; no relate
  modes yet.

## 5. The genuine gaps, by nature

1. **Foundational absence (#1–#2):** No DE-9IM formalisation at all. Every
   predicate proof must start with matrix types + pattern matching (JTS
   `IntersectionMatrixPattern` analogue).

2. **Algorithm gap (#4):** RelateNG is a full arrangement classifier (point,
   line, area, collection, zero-length lines, union semantics). Much larger than
   a single primitive — comparable to Phase 3 overlay in scope.

3. **Inherited JCT seam (#3b):** Area-point predicates (Contains, Within,
   Covers) that reduce to `point_in_ring` inherit the parity ↔ interior
   obligation unless proved for guarded special cases (axis-aligned rectangle,
   right triangle — see `RectangleJCT.v`, `RightTriangleJCT.v`).

4. **Boundary policy gap (#3c):** MOD2 boundary-node rule, line-end inclusion
   on disjoint components (JTS#1175 regression class), and endpoint-vs-
   interior classification are not formalised.

5. **Prepared cache (#5):** Correctness of memoisation is a **refinement**
   theorem (optimisation preserves semantics) — tractable once base `relate`
   is specified, but base must exist first.

6. **Curve extension (#7):** Deferred until curve polygon carriers and
   boundary semantics are fixed (issue #64 / Option B chord approx).

## 6. Risk/cost-ordered options for the next (Coq) terminal

Ordered cheapest/highest-confidence first (clearlane discipline):

- **(A) `DE9IM.v` — matrix type + pattern algebra** — *low risk, foundation.*
  Define `DimEntry`, `IntersectionMatrix`, `matrix_matches_pattern`, and
  encode the nine standard predicates as pattern tables (mirroring JTS
  `RelatePredicate`). No geometry algorithm yet — pure data + logic. Enables
  oracle protocol design and documentation cross-walk.

- **(B) Line-line predicate slice** — *low-medium.* Formalise `LineString`
  (two endpoints) and prove `Intersects`/`Crosses`/`Touches`/`Disjoint` align
  with DE-9IM rows using existing `Intersect.v` theorems. No JCT dependency.

- **(C) JTS#1175 boundary-endpoint witness** — *low-medium, high value.*
  Machine-check a counterexample or regression class for "disjoint line
  components whose boundary endpoints must appear in the matrix" — pins the
  bug class JTS#1200 fixed. Good oracle adversarial vector.

- **(D) Area-point Contains (guarded rectangle)** — *medium.* Special-case
  `Contains(poly, point)` via `RectangleJCT.v` unconditional parity ↔ interior,
  linked to DE-9IM pattern `T*F**F***`. Extends guarded playbook from buffer
  depth (`BufferDepthGuarded.v`).

- **(E) Full RelateNG pipeline** — *high / multi-session.* Noding + matrix
  fill + collections + prepared cache — Phase-3-scale engagement. **Pivot away**
  until (A)+(B) land.

- **(F) Prepared A-L cache correctness** — *medium after (E).* Show cached
  `evaluate` = uncached `relate` for area-line pairs (NTS#819 proof companion).

## 7. Open scope question for the issue owner

#67 spans both **foundational predicate semantics** (DE-9IM + standard names)
and **production RelateNG implementation fidelity** (prepared cache, collection
union semantics, boundary rules). The corpus should confirm:

- *Predicate-semantics first* → start with **(A)** then **(B)**; tractable,
  no new axioms, builds oracle vocabulary.
- *Regression-hardening first* → start with **(C)** (JTS#1175 class) alongside
  **(A)**.
- *Full RelateNG parity* → explicit multi-milestone program like Phase 3 audit;
  not a single PR.

**Recommendation:** confirm predicate-semantics first; beeline **(A) `DE9IM.v`**
as the first Qed terminal, then **(B) line-line** as the first geometry-linked
slice. Hold prepared-cache proofs (**F**) until base `relate` is specified.

## 8. Proposed milestone sketch (if accepted)

| Session | Deliverable | Depends on |
|---------|-------------|------------|
| S1 | `theories/DE9IM.v` — matrix type, pattern match, standard predicate Props | — |
| S2 | `theories/RelateLineLine.v` — line-line DE-9IM via `Intersect.v` | S1 |
| S3 | JTS#1175 regression witness + doc | S2 |
| S4 | Guarded `Contains` for axis-aligned rectangle | S1 + `RectangleJCT.v` |
| S5+ | Area-line / area-area / RelateNG pipeline / prepared cache | S1–S4 |

Oracle: add `RELATE_MATRIX` / `RELATE_PREDICATE` modes after S2, following
`oracle/driver.ml` extraction pattern.