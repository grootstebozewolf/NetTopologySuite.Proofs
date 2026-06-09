# Triage — NTS / JTS open issues vs. NetTopologySuite.Proofs corpus

> **Source of record for the curve-awareness proof batch (#64–#69).** This is
> the report every batch issue cites. It maps the open NTS/JTS issues that the
> formal-proof corpus is meant to back onto **what is actually proven today**
> (`theories/`, `theories-flocq/`, `docs/verified-claims.md`), separating
> *proven* from *gap*, and recording priority and ordering decisions.
>
> Generated from the 2026-06-03 issue batch; last reconciled **2026-06-09**
> against corpus HEAD `5b16d25`. This file is the cross-cutting overview; the
> per-area detail lives in the GitHub issues and the sibling docs
> `docs/issue-64-arc-primitives-triage.md` and
> `docs/issue-67-relateng-triage.md`.

## Scope

The corpus produces **Qed-closed Rocq theories + extractable oracles** that the
Java (JTS) and .NET (NTS) implementations can be *differentially verified*
against. These are **soundness statements**, not a verified re-implementation.
Regimes used below match `docs/verified-claims.md`: `[exact]` exact reals,
`[int-b64]` integer-coordinate binary64 (`|coord| ≤ 2²⁵`), `[int-b64-arc]` the
degree-4 `b64_inCircle` chain (`|coord| ≤ 2¹¹`), `[full-b64]` all finite
binary64, `[cond]` under named hypotheses, `[oracle]`
extracted/differential-testable.

The driving feature work is the **JTS Curve Awareness EPIC** (locationtech/jts#1195,
Option A structural `CurvePolygon`) and the NTS align epic (NTS#828). Umbrella
tracker: **#69**.

## Per-area status

| Issue | Area | Priority | Proof state | Verdict |
|---|---|---|---|---|
| **#64** | Circular-arc primitives (length, sweep, in-arc, in-circle) | `Immediate` | **Most progressed; top gap closed.** Asks #1/#2: `Atan2.v` + `AngleBetween.v` + `ArcLength.v` (`r·θ`, `chord_le_arc_length`) Qed. **Ask #4b PROVEN & merged (PR #146):** `InCircle_b64_exact.v` — full-plane `b64_inCircle` sign exactness at **3 axioms, no `classic`** (integer-ℤ determinant, matching orient2d's full-plane result — see [`docs/phase0-completion.md`](docs/phase0-completion.md)) + `2¹¹` integer-regime value exactness + Perron worst-case witness. **Ask #5a partial:** `ArcLineIntersect_b64_exact.v` Scope A (pre-division Cramer prefix bit-exact); coordinate identity (Scope B/C) and arc-arc deferred. `ArcOrient`/`ArcIntersect`/`ArcIntersectIVT`/`ArcHotPixel`/`ArcChordApprox`/`ArcOverlay` Qed. | Keep Immediate — only #5a Scope B/C + arc-arc remain |
| **#65** | Buffer / offset curve correctness | `Urgent` | Heaviest existing corpus: 18 `Buffer*.v` files + `ExtractBufferRings.v`, plus 3 documented counterexamples (depth enclosure / horizontal-edge / vertex-graze). Coverage is **linear** buffer; curve-aware `CurvePolygon` output not yet proven (blocked on #64 arc coords). | Trimmed Immediate → Urgent (2026-06-08) |
| **#66** | Precision / snap-rounding / OverlayNG soundness | `Urgent` | **Strongest coverage of the batch.** `SnapRounding_b64`, `HotPixel*`, `Hobby*`, the `PassesThrough_*` family (JTS#752/#1133 segment-reversal asymmetry root + C1 grid-exactness reduction), `Overlay*`, `RingArea979` (JTS#979). Multiple honest machine-checked **negatives** (rounded filter unsound/incomplete/asymmetric). | Keep Urgent — largely delivered, closing gaps |
| **#67** | RelateNG / 9IM matrix & boundary handling | `Immediate` | **Now under active construction (was a blank page on 2026-06-08).** Per `docs/issue-67-relateng-triage.md`: `theories/DE9IM.v` (matrix type + pattern algebra, S1), `theories/RelateLineLine.v` (line-line DE-9IM soundness via `Intersect.v`, S2), `theories/RelateIntDetBound.v` (integer determinant range bound, S0), + `oracle/de9im_line_line_vectors.txt` (S3). Remaining: boundary/MOD2 policy, area-line/area-area, RelateNG pipeline, prepared cache. Headline ref JTS#1175 fixed upstream (jts#1200). | Bumped Urgent → Immediate (2026-06-08); now the active frontier |
| **#68** | Delaunay triangulation / Voronoi correctness | `Non-urgent` | `Triangle.v`, `Tin.v`, `GeneralTriangle{Parity,Separation}.v`, `RightTriangle*` exist; no empty-circle Delaunay / Voronoi proofs yet. **Core primitive now available:** `inCircle_R` / `b64_inCircle` proven via #146. | Correctly labeled — primitive unblocked, not yet started |
| **#69** | Umbrella / epic tracker | `Expectant` | Tracking issue only. | Keep open as the epic tracker |

## JTS #1195 TAG → proof-area mapping

The driving EPIC (locationtech/jts#1195) is structured as ~40 self-contained
**TAGs** across 7 phases ("one TAG per PR"). This maps the proof-relevant TAGs
onto the batch issues and the corpus artifacts that back them. Status:
**✅ proven** (Qed and/or extracted oracle) · **🟡 partial** (foundation/predicate
proven, soundness or coordinates open) · **⬜ planned** (not yet started) ·
**—** not proof-relevant (rendering / structural plumbing).

| JTS TAG | What it is | Proof issue | Corpus artifact / oracle | Status |
|---|---|---|---|---|
| **F-CP / F-MC / F-MS** | Structural `CurvePolygon` / `MultiCurve` / `MultiSurface` (preserve ring/member curves) | #69, #64 | `theories/CurveGeometry.v` (SQL/MM types, `CurveRing`, validity, chord bridge) | 🟡 structural model exists |
| **B-CP / B-MS** | Boundary of curve composites | #69 | — | ⬜ |
| **M-LEN-CS / M-LEN-CC** | Arc / compound-curve length (`r·θ`) | #64 | `ArcLength.v`, `Atan2.v`, `AngleBetween.v`; oracle `ARC_LENGTH_INVARIANTS_EXACT` / `ARC_SHORTER` | ✅ exact invariants; float length is interface-boundary |
| **M-AREA-CP** | `CurvePolygon` area (Green's theorem + circular-segment correction) | #64 | oracle `ARC_AREA_INVARIANTS_EXACT` | ✅ exact rational invariants; float area interface-boundary |
| **M-DIM** | Dimension of curve geometries | #69 | — | ⬜ structural |
| **V-CP / V-CS** | Arc-aware validity (arc self-intersection, orientation via sector area, holes-in-shell) | #64 | `ArcOrient.v`, `ArcHotPixel.v`, `theories-flocq/InCircle_b64_exact.v` | 🟡 in-circle sign ✅ (full-plane, 3-ax); arc-span/self-intersect soundness open (`arc_chord_intersect_sound`) |
| **D-PT** | Analytical point-to-arc distance | #64 | `Distance.v` (foundation) + arc primitives | 🟡 |
| **D-AA** | Arc-arc distance | #64 | `ArcIntersect.v` (predicate) | 🟡 |
| **C-\*** | Centroid of curve geometries | #69 | `Centroid.v` (linear) | ⬜ curve case planned |
| **H-\*** | Hulls over curve inputs | #69 | `Convex.v` (linear) | ⬜ curve case planned |
| **S-\*** | Simplification of curves | #69 | `Simplify.v`, `Linearise.v` (linear) | ⬜ curve case planned |
| **AT-\*** | Affine transforms (non-similarity → detect-and-densify, §7 risk) | #69 | — | ⬜ |
| **LRF-\*** | Linear referencing on curves | #69 | — | ⬜ |
| **DSF** | Densifier (curve → chords internally) | #64, #65 | `ArcChordApprox.v` (sagitta bound), `CurveLinearise.v` (`chord_approx_ring_closed`) | ✅ chord-approx faithfulness (closure); sagitta/`ring_simple` open |
| **BUF-1 / BUF-N** | Single-/multi-arc buffer → `CurvePolygon` | #65 | 18× `Buffer*.v` (linear), `ExtractBufferRings.v` | 🟡 linear proven; arc-output blocked on #64 coords |
| **OFF** | Offset curve (arc-preserving) | #65 | `BufferOffset.v` | 🟡 linear; arc planned |
| **VBF** | Variable-distance buffer | #65 | — | ⬜ |
| **N-AL** | Arc-line noding / intersection | #64 | `theories-flocq/ArcLineIntersect_b64_exact.v` (Scope A), `ArcIntersect.v`, `ArcIntersectIVT.v` | 🟡 Scope A (pre-division) ✅; coordinate identity (Scope B/C) queued |
| **N-AA** | Arc-arc noding / intersection | #64 | `ArcIntersect.v` (`arc_arc_intersects` predicate) | 🟡 existence predicate ✅; quartic coordinates open |
| **N-SS** | `SegmentString` / `Noder` for curves | #66 | `SnapRounding_b64.v`, `HotPixel*`; oracle `CURVE_SNAP_DECISION` | 🟡 linear noding ✅; curve-snap decision oracle ✅ |
| **PRC-SN** | `PrecisionModel.makePrecise` on curves | #66 | oracle `CURVE_SNAP_DECISION` / `CURVE_SNAP_INVARIANTS_EXACT` (exact-`Q`) | ✅ curve-snap grid-friendliness |
| **OV** | Arc-preserving overlay output | #66, #64 | `Overlay*.v`, `ArcOverlay.v` | 🟡 conditional headline (`arc_overlay_correct_chord_approx`, 2 bridge hyps) |
| **R-\* (R-CONT, R-PR)** | Predicates / relate on curved inputs | #67 | `theories/DE9IM.v`, `RelateLineLine.v`, `RelateIntDetBound.v` | 🟡 line-line DE-9IM ✅; arc-aware planned |
| **PLG** | Polygonizer accepting `CompoundCurve` edges | #69, #66 | `RingExtract.v` / overlay ring assembly | ⬜ (linear `extract_rings_valid` is the live deferred entry) |
| **TRI-DT** | Delaunay on (densified) curved boundaries | #68 | `theories-flocq/InCircle_b64_exact.v` (primitive), `Triangle.v`, `Tin.v` | 🟡 in-circle primitive ✅; Delaunay proper planned |
| **TRI-VR** | Voronoi on curved input | #68 | — | ⬜ |
| **TB-\* / F-RD** | TestBuilder rendering / `ShapeWriter` hooks | — | — | — not proof-relevant |

**Reading the table against the EPIC's Definition of Done (§10).** JTS#1195's
DoD requires curve-preserving output "**where mathematically sound**" — which is
exactly what the ✅ rows certify and the 🟡 rows bound. The §7 "arc intersection
performance" risk concerns the N-AA/N-AL primitives whose *exactness* is already
proven here (`InCircle_b64_exact` / `ArcLineIntersect_b64_exact`): the corpus
supplies the soundness oracle while JTS settles the performance design.

## Referenced upstream issues

Status of the JTS/NTS issues the batch cites as drivers. Re-check before
spending further proof effort — several are stale.

| Upstream | Cited in | Status |
|---|---|---|
| JTS#1195 — Curve Awareness EPIC | #64, #65, #66, #68, #69 | Open — primary driver |
| JTS#1175 — RelateNG.computeLineEnds() skips boundary points | #64, #66, #67 | **Fixed (jts#1200)** — struck through in #64/#66/#67 |
| JTS#979 — buffer with fixed precision removes hole | #64, #65, #66 | Open — backed by `RingArea979.v` |
| JTS#752 — TopologyException in UnaryUnionNG (floating precision) | #66 | Open — root captured in `PassesThrough_b64_compute_asymmetric.v` |
| JTS#1133 — snapRoundingNoder on polygons returns MultiLineString | #66 | Open — same order-dependence root |
| JTS#1106 — orientation robustness summary | #64, #66 | Open — `Orient_b64_exact*` is the ground-truth spec |
| JTS#1147, #739, #1028, #178, #180, #592, #866, #876, #908, #1102, #1183 — buffer/offset quality | #64, #65 | Open — "summary of failures" refs need re-check vs current JTS |
| JTS#1000 — OverlayNG failures summary | #64, #66, #67 | Open |
| JTS#865 — OverlayNG intersection rotates vertices | #64, #66 | Open |
| JTS#1122 — CoverageValidator misses gap if tolerance too large | #64, #66, #67 | Open |
| JTS#1190, #1138, #1039, #20 — Delaunay/Voronoi robustness | #68 | Open |
| NTS#828 — align epic | #69 | Open |
| NTS#815 — OffsetCurve miter for polygonal (JTS#1109) | #64, #65, #69 | Open — port target |
| NTS#819 — RelateNG cache for prepared A-L (JTS#1099) | #67 | Open |
| NTS#247, #570 — curves / GML curves | #64, #69 | Open — old but relevant |
| NTS#719, #638 — GeometryPrecisionReducer / buffer holes | #66 | Open |

## Cross-cutting findings

1. **This file exists and is the source of record.** Cited by every batch issue;
   created 2026-06-08, refreshed 2026-06-09. Per-area detail now lives in the
   sibling docs `docs/issue-64-arc-primitives-triage.md` and
   `docs/issue-67-relateng-triage.md` (the umbrella/detail split #69 describes).
2. **Stale upstream refs.** JTS#1175 is fixed (jts#1200) and is struck through
   with the PR ref in #64, #66, #67. The buffer/overlay "summary of failures"
   refs (JTS#1102, #1000, etc.) should still be re-checked against current JTS
   before more proof spend.
3. **Label vs. reality reconciled (2026-06-08).** #67 bumped `Urgent → Immediate`
   (was the under-built area); #65 trimmed `Immediate → Urgent` (linear buffer
   foundation mature, curve output blocked on #64).
4. **Progress since 2026-06-08 (2026-06-09).** PR #146 merged: #64 ask #4b
   (`b64_inCircle` sign exactness) closed at 3 axioms full-plane, arc-line
   Scope A landed. #67 moved from blank to S0–S3 (`DE9IM.v`, `RelateLineLine.v`,
   `RelateIntDetBound.v` + oracle vectors). #68's `inCircle` primitive is now
   available. The first two items of the prior order of attack are done/started.

## Recommended order of attack (revised 2026-06-09)

1. **#67** — now the active frontier and largest *unfinished* build: extend the
   landed line-line DE-9IM (S0–S3) to boundary/MOD2 policy, area-line/area-area,
   and the RelateNG pipeline + prepared cache (S4+).
2. **#64** — finish ask #5a Scope B/C (arc-line coordinate identity + forward
   error) and arc-arc; the sign/length foundation is done.
3. **#66** — finish remaining precision/overlay gaps (mostly there).
4. **#65** — curve-aware buffer output once #64 arc coords land.
5. **#68** — Delaunay / Voronoi on top of the now-proven `inCircle_R`.

## How to cite the corpus

When referencing proven results: lead with `[exact]` rows from
`docs/verified-claims.md`, present `[cond]` rows as "conditional headline"
(never as solved), and offer the matching `[oracle]` mode to reproduce a
concrete case. Qed-closure is enforced corpus-wide by
`scripts/check_admitted.sh`; claim citations are checked by
`scripts/validate-claims.sh` on every CI run.
