# Triage — NTS / JTS open issues vs. NetTopologySuite.Proofs corpus

> **Source of record for the curve-awareness proof batch (#64–#69).** This is
> the report every batch issue cites. It maps the open NTS/JTS issues that the
> formal-proof corpus is meant to back onto **what is actually proven today**
> (`theories/`, `theories-flocq/`, `docs/verified-claims.md`), separating
> *proven* from *gap*, and recording priority and ordering decisions.
>
> Generated from the 2026-06-03 issue batch; last reconciled **2026-06-08**
> against corpus HEAD `c7013ae`. The per-issue detail lives in the GitHub
> issues; this file is the cross-cutting overview.

## Scope

The corpus produces **Qed-closed Rocq theories + extractable oracles** that the
Java (JTS) and .NET (NTS) implementations can be *differentially verified*
against. These are **soundness statements**, not a verified re-implementation.
Regimes used below match `docs/verified-claims.md`: `[exact]` exact reals,
`[int-b64]` integer-coordinate binary64, `[full-b64]` all finite binary64,
`[cond]` under named hypotheses, `[oracle]` extracted/differential-testable.

The driving feature work is the **JTS Curve Awareness EPIC** (locationtech/jts#1195,
Option A structural `CurvePolygon`) and the NTS align epic (NTS#828). Umbrella
tracker: **#69**.

## Per-area status

| Issue | Area | Priority | Proof state | Verdict |
|---|---|---|---|---|
| **#64** | Circular-arc primitives (length, sweep, in-arc, in-circle) | `Immediate` | **In flight, foundations landed.** Option A chosen; `theories/Atan2.v` (`atan2` from Stdlib `Ratan`, `cos_atan2`/`sin_atan2`, 4-axiom) and `theories/ArcLength.v` (`arc_length = r·θ`, `chord_le_arc_length`, `chord_subtended_sq`) now exist. `ArcOrient`/`ArcIntersect`/`ArcIntersectIVT`/`ArcHotPixel`/`ArcChordApprox`/`ArcOverlay` Qed. | Active & healthy — keep Immediate |
| **#65** | Buffer / offset curve correctness | `Urgent` | Heaviest existing corpus: 18 `Buffer*.v` files + `ExtractBufferRings.v`, plus 3 documented counterexamples (depth enclosure / horizontal-edge / vertex-graze). Coverage is **linear** buffer; curve-aware `CurvePolygon` output not yet proven (blocked on #64 arc coords). | Trimmed Immediate → Urgent (2026-06-08) |
| **#66** | Precision / snap-rounding / OverlayNG soundness | `Urgent` | **Strongest coverage of the batch.** `SnapRounding_b64`, `HotPixel*`, `Hobby*`, the `PassesThrough_*` family (JTS#752/#1133 segment-reversal asymmetry root + C1 grid-exactness reduction), `Overlay*`, `RingArea979` (JTS#979). Multiple honest machine-checked **negatives** (rounded filter unsound/incomplete/asymmetric). | Keep Urgent — largely delivered, closing gaps |
| **#67** | RelateNG / 9IM matrix & boundary handling | `Immediate` | **Biggest gap vs. label.** No dedicated relate/9IM theory — only segment-level `Intersect.v`. Headline ref JTS#1175 already fixed upstream (jts#1200). | Bumped Urgent → Immediate (2026-06-08) — next real build target |
| **#68** | Delaunay triangulation / Voronoi correctness | `Non-urgent` | `Triangle.v`, `Tin.v`, `GeneralTriangle{Parity,Separation}.v`, `RightTriangle*` exist; no empty-circle Delaunay / Voronoi proofs yet. Natural primitive is `inCircle_R` from #64. | Correctly labeled — downstream of #64 |
| **#69** | Umbrella / epic tracker | `Expectant` | Tracking issue only. | Keep open as the epic tracker |

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

1. **This file now exists.** It was cited by every batch issue but previously
   uncommitted; created 2026-06-08 to be the actual source of record.
2. **Stale upstream refs.** JTS#1175 is fixed (jts#1200) and is now struck
   through with the PR ref in #64, #66, #67. The buffer/overlay "summary of
   failures" refs (JTS#1102, #1000, etc.) should be re-checked against current
   JTS before more proof spend.
3. **Label vs. reality reconciled (2026-06-08).** The two original `Immediate`
   issues (#64, #65) were the *most* progressed; the genuinely under-built area
   was #67 (relate/9IM). #67 bumped `Urgent → Immediate`; #65 trimmed
   `Immediate → Urgent` (linear buffer foundation mature, curve output blocked
   on #64).

## Recommended order of attack

1. **#64** — close remaining gaps: `b64_inCircle` sign-exactness (direct
   analogue of the proven `b64_orient2d_exact_for_small_int` pattern) and
   arc-line intersection *coordinates* (quadratic, mirrors
   `Intersect_b64_exact`). Unblocks #65, #67-arcs, #68.
2. **#67** — start the real 9IM / relate theory (largest value gap).
3. **#66** — finish remaining precision/overlay gaps (mostly there).
4. **#65** — curve-aware buffer output once #64 arc coords land.
5. **#68** — Delaunay / Voronoi on top of #64's `inCircle_R`.

## How to cite the corpus

When referencing proven results: lead with `[exact]` rows from
`docs/verified-claims.md`, present `[cond]` rows as "conditional headline"
(never as solved), and offer the matching `[oracle]` mode to reproduce a
concrete case. Qed-closure is enforced corpus-wide by
`scripts/check_admitted.sh`; claim citations are checked by
`scripts/validate-claims.sh` on every CI run.
