<!-- doc-kind: finding
date: 2026-08-05
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
Thanks for keeping this open — design-history note from the NetTopologySuite.Proofs mesh / Delaunay lane (we treated **#311 → #1094 → #1212** as one product lineage; tip for merge discussion is **#1212**).

### What this PR established (2018)
Stage A Shewchuk in-circle filter (coords translated so `P` is origin) with permanent-scaled `iccerrboundA`, then escalate when uncertain. That filter-then-escalate shape is exactly what #1212 and #1094 still use. Maintainer notes from 2018 (`isInCircleDDFast`, unit tests) aged well.

### Numbers (Stage A only vs extracted `b64_inCircle`)
Write-up: [jts-311-incircle-lane](https://github.com/MerkatorBV/NetTopologySuite.Proofs/blob/main/docs/jts-311-incircle-lane-2026-08.md) (`oracle/jts311_incircle_history.txt`, 22 vectors).

| Check | Result |
|---|---|
| Oracle flip pin | **POS 1.5** |
| Stage A#311 **CERTAIN** vs oracle sign conflicts | **0** |
| Stage A#311 **UNCERTAIN** | **7** (correct declines) |

GEOS955 / JTS#1171 subset still shows why escalation exists: Stage A **ZERO/UNCERTAIN**, oracle **POS**.

### Two archive notes (not merge blockers for a history PR)
1. **Name vs body:** `isInCircleAdapt` here is Stage A + **DDFast**, not Shewchuk’s full `incircleadapt` expansion stages (that fuller port is #1094).
2. **ε:** this PR uses `Math.ulp(1.0)` (= \(2^{-52}\)); Shewchuk / #1212 / #1094 use \(2^{-53}\). Bound is ~2× looser (more DD). Direction is safe; later PRs align with the published constant.
3. **2026 large-coord unit test:** after binary64 rounding of the \(10^{14}\) literals, Stage A det and the Rocq in-circle kernel both say **ZERO** (not strictly inside). If `isInCircleDDFast` still returns `true` on those doubles, that is a useful DD-path check against an independent kernel — happy to dig further if useful.

### Bottom line
Valuable as the **first open sketch** of robust in-circle Stage A in JTS. For production merge we point at **#1212** (Stage A + DDNormalized + `Vertex.isCCW` → `Orientation.index`); corpus gates for the tip are already green.

*(Affiliation: [NetTopologySuite.Proofs](https://github.com/MerkatorBV/NetTopologySuite.Proofs) — formal mesh/predicate companion, not a JTS committer review.)*
