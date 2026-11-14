<!-- doc-kind: finding
date: 2026-08-05
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# Scout — all open [locationtech/jts](https://github.com/locationtech/jts) PRs vs NetTopologySuite.Proofs

**Date**: 2026-08-05.  
**topic:** `docs` (routing); primary epics touched below as `core` / `mesh` / `precision` / `relate` / `buffer` / `metric` / `coverage` / `hull`.  
**Scope**: Inventory of **all 49** open PRs on `locationtech/jts` (fetched 2026-08-05 via GitHub API). Map each against the corpus (`TRIAGE_NTS_JTS_ISSUES.md`, `#64–#69`, `#423`/`#425`/`#410`) and rank by **risk / cost of corpus engagement**.  
**Question**: Which open JTS PRs should this proofs corpus prioritise next, and which can stay park?

**Verdict (headline)**  
Of 49 open PRs, **~12 are corpus-hot**, **~10 are watch**, and **~27 are out of proof scope** (CI, IO, docs, API cosmetics, stale refactors).  
**Top pick stack (do first):** `#1212` + `#1094`/`#311` (mesh in-circle) → `#1093`/`#1197` (orientation filters) → `#1145` (PIP locator) → `#1084` (coverage edges). `#90` ScaledNoder **scoped YELLOW** (policy watch only).

---

## §0 — Scoring rubric

| Axis | Meaning |
|---|---|
| **Relevance** | How hard the PR lands on a corpus epic / oracle surface |
| **Cost** | Effort for *this* repo to engage (pin vectors, claim, differential gate, comment) — not JTS merge cost |
| **Risk** | Downstream soundness risk if JTS merges without a corpus gate |
| **Score** | `priority = f(relevance↑, risk↑, cost↓)` — **P0** engage, **P1** watch, **P2** park |

| Relevance | Cost | Risk |
|---|---|---|
| **H** touches orient / in-circle / DT / snap / overlay / relate / buffer / PIP / Hausdorff / coverage | **L** existing Qed/oracle; pin or comment | **H** production predicate or mesh legality |
| **M** densify, distance, polygonize, simplify structure | **M** new claim or small theory | **M** quality / topology-sensitive |
| **L** API, IO, CI, docs, generics, Z plumbing | **H** greenfield / thesis | **L** no soundness surface |

---

## §1 — Priority picks (engage)

Ordered by **risk÷cost** for the proofs corpus (not JTS merge politics).

| Rank | PR | Title | Epic / topic | Rel | Cost | Risk | Why pick |
|---|---|---|---|---|---|---|---|
| **1** | [#1212](https://github.com/locationtech/jts/pull/1212) | Improve triangulation robustness | **#68** `mesh` | H | L–M | H | `TrianglePredicate.isInCircleRobust` Shewchuk-style filter + `Vertex.isCCW` → `Orientation.index`. Corpus has `b64_inCircle` / `DelaunayLocallyDelaunay` / empty-circle pins — can **diff-test** the new filter against `INCIRCLE_SIGN` / `nts_rocq_in_circle`. Direct NTS port path. |
| **2** | [#1094](https://github.com/locationtech/jts/pull/1094) | Make isInCircleRobust robust | **#68** `mesh` | H | L | H | Older sibling of #1212 on the same class. Same gate; prefer whichever is current tip — treat as **one lane**. |
| **3** | [#311](https://github.com/locationtech/jts/pull/311) | isInCircleAdapt sketch Java port | **#68** `mesh` | H | L | H | Shewchuk adaptive sketch; updated 2026-05. Superseded in spirit by #1094/#1212 but useful as **design history**. Corpus Stage D expansion work is the formal counterpart. |
| **4** | [#1093](https://github.com/locationtech/jts/pull/1093) | Change Shewchuk Orientation filter to Ozaki et al. | **#66/#64** `precision`/`core` | H | M | H | Production `CGAlgorithmsDD` filter. **Lane GREEN 2026-08-05:** 45-vector three-way gate (master `1e-15` / Ozaki / corpus Shewchuk) vs `ORIENT_EXACT` — 0 CERTAIN conflicts; Ozaki tighter than master on 4 same-sign band cases. See [`jts-1093-orient-lane-2026-08.md`](jts-1093-orient-lane-2026-08.md). |
| **5** | [#1197](https://github.com/locationtech/jts/pull/1197) | Characterize DD orientation soundness (#1106) | **#66** `precision` | H | L | M | **Ours.** Test-only + `RocqRefRunner`. **Keep-green 2026-08-05 GREEN:** rebased onto master; corpus integer pins refreshed; local 22/22 + GHA `build-and-test` pass; merge ping posted ([comment](https://github.com/locationtech/jts/pull/1197#issuecomment-5186644725)). Awaiting maintainer review/merge. |
| **6** | [#90](https://github.com/locationtech/jts/pull/90) | Fix ScaledNoder behaviour (draft) | **#66** `precision` · **P1 policy** | H | L | M | **Lane YELLOW 2026-08-05 (not P0 theory):** mukoki scale=1 mixed-precision **masked** by modern `SnapRoundingNoder`; scale=0 `round(x*0)` footgun live; do **not** merge draft as written. No new snap claim. See [`jts-90-scalednoder-lane-2026-08.md`](jts-90-scalednoder-lane-2026-08.md). |
| **7** | [#1145](https://github.com/locationtech/jts/pull/1145) | YStripesPointInAreaLocator | **#67** `relate` (+ JCT) | H | L–M | M | **Lane GREEN 2026-08-05:** gallery 14/14 (vertex-graze/horizontal/Spectre/Hat) — YStripes port ≡ Indexed ≡ Simple ≡ geometric GT. See [`jts-1145-pip-lane-2026-08.md`](jts-1145-pip-lane-2026-08.md). |
| **8** | [#1084](https://github.com/locationtech/jts/pull/1084) | CoverageEdgeExtractor | **#425** `coverage` | M–H | M | M | Unique edges from polygonal coverage. Corpus has `CoverageGapOverlapCleaner.v` / #425. Good **next coverage claim** after cleaner. |
| **9** | [#1216](https://github.com/locationtech/jts/pull/1216) | Explicit stack in DouglasPeucker (#1127) | **#69** S-* | M | L | L–M | **Ours.** Stack overflow fix; behaviour-preserving. Corpus `Simplify.v` is structural only — **no new proof** needed; port to NTS when merged. |
| **10** | [#1140](https://github.com/locationtech/jts/pull/1140) | Hausdorff distance percentile | **#423** `metric` | M | M | L–M | Extends discrete Hausdorff. Corpus `HausdorffDiscrete.v` / Claim423a pins directed max-min — can pin percentile semantics or mark out-of-scope. |
| **11** | [#1217](https://github.com/locationtech/jts/pull/1217) | MinimumAreaRectangle convex-hint (#1149) | **#hull** / #69 | M | L | L | **Ours.** API only. Adjacent to MBT (`MinimumBoundingTriangle.v` / Claim424a) but **no proof obligation**. |
| **12** | [#968](https://github.com/locationtech/jts/pull/968) | Polygonizer infinite loop (#874) | **#66/#69** PLG | M | M | M | Infinite loop fix in polygonizer. Corpus ring-extract / Euler is linear overlay PLG; still a **topology-engine** watch. |

### Recommended immediate work sequence (this repo)

1. **Mesh in-circle lane (P0)** — **LANDED 2026-08-05:**  
   - **Session 1 GREEN (#1212 tip):**  
     `oracle/gen_jts1212_incircle_vectors.py` + `oracle/jts1212_incircle_vectors.txt`  
     + [`docs/jts-1212-incircle-lane-2026-08.md`](jts-1212-incircle-lane-2026-08.md).  
     29 vectors; Stage A CERTAIN never disagrees with oracle; GEOS955 → UNCERTAIN / oracle POS.  
   - **Session 2 GREEN (#1094 FFI scout + corpus review):**  
     `oracle/gen_jts1094_incircle_scout.py` + `oracle/jts1094_incircle_vectors.txt`  
     + scout FFI (`scout_incircle_probe` / `nts_rocq_in_circle`)  
     + [`docs/jts-1094-incircle-lane-2026-08.md`](jts-1094-incircle-lane-2026-08.md).  
     27 vectors; FFI≡oracle_bin bits; CERTAIN vs FFI clean; review: tip stays **#1212**,
     nits on `>=` bound / `Math.fma` / missing `Vertex.isCCW` fix.  
   - **Session 3 GREEN (#311 design history):**  
     `oracle/gen_jts311_incircle_history.py` + `oracle/jts311_incircle_history.txt`  
     + [`docs/jts-311-incircle-lane-2026-08.md`](jts-311-incircle-lane-2026-08.md).  
     Stage A sketch + DDFast lineage; **ε = `ulp(1.0)` = \(2^{-52}\)** (looser than
     Shewchuk \(2^{-53}\)); name is not full `incircleadapt` (#1094). Product tip stays **#1212**.  
2. **Orientation lane (P0)** — **LANDED 2026-08-05 (session GREEN):**  
   - Full `libntsrocq` rebuild path after re-extract (`docs/ffi-rungs-2026-08.md`,
     `scripts/rebuild_oracle_ffi.sh`).  
   - Differential scout: `oracle/gen_jts1093_orient_scout.py` — **three-way**
     mirror (JTS-master `1e-15` vs Ozaki #1093 vs corpus Shewchuk Stage A) vs
     `ORIENT_EXACT`.  
   - Table + write-up: `oracle/jts1093_orient_vectors.txt` (45 vectors) +
     [`docs/jts-1093-orient-lane-2026-08.md`](jts-1093-orient-lane-2026-08.md).  
   - Gate: 0 CERTAIN conflicts; Ozaki CERTAIN while master UNCERTAIN on **4**
     same-sign band vectors; Ozaki ↔ corpus Shewchuk certainty splits **0**.  
   - Note: `ORIENT_EXACT` **FFI** still has a segfault class on extreme coords
     (parity YELLOW); use `oracle_bin` for exact GT.  
   - **#1197 keep-green (same day) GREEN:** rebased
     `feature/orientation-robustness-tests` onto `master`; refreshed
     `orientation_proof_vectors.txt` integer pins; local suite 22/22 + GHA
     `build-and-test` pass; merge-ping comment posted.  
3. **PIP gallery on #1145 (P0/P1)** — **LANDED 2026-08-05 GREEN:**  
   - Faithful C# port: `tests/Discussion839Mre/YStripesPointInAreaLocator.cs`  
   - Harness: `dotnet run … -- --jts1145` (+ `oracle/jts1145_pip_gallery_vectors.txt`)  
   - Write-up: [`docs/jts-1145-pip-lane-2026-08.md`](jts-1145-pip-lane-2026-08.md).  
   - 14/14 geometric GT; critical rows (diamond graze INT, notch horizontal EXT, Spectre/Hat pockets EXT) all pass; Y ≡ Indexed ≡ Simple.  
   - Optional: post gallery pins comment (`tests/Discussion839Mre/jts-1145-comment.md`).  
4. **ScaledNoder #90 (P1)** — **SCOPED 2026-08-05 YELLOW:**  
   - MRE: `tests/Discussion839Mre` `--jts90` + [`jts-90-scalednoder-lane-2026-08.md`](jts-90-scalednoder-lane-2026-08.md).  
   - Does **not** map to a missing `SnapRoundingScale_b64` claim (wrapper policy + scale=0 safety).  
   - Recommend **narrow fix only** (scale=0 skip / throw); do not invert scale=1 under SRN.  
   - Drop from P0 theory budget; keep watch if draft is revived.  
5. **Coverage #1084 (P1)** — Spec sketch only until #425 cleaner is stable.

---

## §2 — Full inventory (all 49)

Columns: **Pri** = P0/P1/P2 · **Rel/Cost/Risk** · **Epic**.

### 2.1 Hot / recent geometric (2024–2026)

| PR | Title | Author | Pri | Rel | Cost | Risk | Epic | Corpus notes |
|---|---|---|---|---|---|---|---|---|
| 1220 | Add Geometry.getCoordinateDimension | mdedetrich | P2 | L | L | L | — | API dimension helper; no soundness |
| 1218 | Update README.md (Kotlin port link) | mipastgt | P2 | L | L | L | — | docs |
| 1217 | MinimumAreaRectangle convex-hint | grootstebozewolf | P1 | M | L | L | hull | Ours; API only |
| 1216 | DouglasPeucker explicit stack | grootstebozewolf | P1 | M | L | L–M | core/S-* | Ours; port when merged |
| 1215 | RelatePointLocator Android ART array | grootstebozewolf | P2 | L | L | L | relate | Runtime/ART; no math |
| 1214 | setRandom on RandomPointsBuilder | woogi-kim | P2 | L | L | L | — | test util |
| **1212** | **Improve triangulation robustness** | micycle1 | **P0** | H | L–M | H | **mesh** | In-circle filter + orient |
| **1197** | **DD orientation characterization (#1106)** | grootstebozewolf | **P0** | H | L | M | **precision** | Ours; Rocq vectors |
| 1196 | Densifier SegmentInterpolator | smithkm | P1 | M | M | L–M | core/DSF | Densify extension; chord/sagitta lane adjacent |
| 1189 | WIP Orientation isCCW GEOS test | strk | P1 | H | L | M | precision | `status-INVALID`; still a useful negative test seed |
| 1170 | Generics on geom.util extractors | micycle1 | P2 | L | L | L | — | API typing |
| 1164 | GeoJsonWriter create() for subclasses | krizleebear | P2 | L | L | L | — | IO |
| **1145** | **YStripesPointInAreaLocator** | micycle1 | **P0** | H | L–M | M | **relate**/JCT | **GREEN** gallery 14/14 ([lane](jts-1145-pip-lane-2026-08.md)) |
| **1140** | **Hausdorff distance percentile** | ikgh9 | **P1** | M | M | L–M | **metric** | Extends HausdorffDiscrete |
| 1137 | Gh pages to docs | jodygarnett | P2 | L | L | L | — | docs |
| 1135 | HilbertEncoder.sort() | micycle1 | P2 | L | L | L | — | spatial index util |
| **1094** | **Make isInCircleRobust robust** | tinko92 | **P0** | H | L | H | **mesh** | Same lane as #1212 |
| **1093** | **Ozaki orientation filter** | tinko92 | **P0** | H | M | H | **precision** | Production orient filter swap |
| **1084** | **CoverageEdgeExtractor** | nstrahl | **P1** | M–H | M | M | **coverage** | #425 adjacent |
| 1014 | Missing @Override annotations | msbarry | P2 | L | L | L | — | app/TestBuilder |
| 994 | NPE in Point | arthurscchan | P2 | L | L | L | — | null guard |
| **968** | **Polygonizer infinite loop** | mukoki | **P1** | M | M | M | PLG | Topology engine bugfix |

### 2.2 Mid-age geometric / plumbing (2021–2023)

| PR | Title | Author | Pri | Rel | Cost | Risk | Epic | Corpus notes |
|---|---|---|---|---|---|---|---|---|
| 942 | HeaderDemo sample_java_header | FObermaier | P2 | L | L | L | — | license sample |
| 941 | WKTReader silent dim addition | chenhh021 | P2 | L | L | L | — | IO/WKT |
| 930 | DistanceOp skip redundant calc | RichMacDonald | P1 | M | L | L–M | metric | Perf; same DistanceOp surface as 926 |
| 926 | LineSegment orthogonal point | RichMacDonald | P1 | M | L–M | L | metric | Segment geometry; `Segment.v` adjacent |
| 836 | CatmullRomSpline | wulfsberg | P2 | L–M | H | L | core? | New curve type; greenfield vs arc/clothoid focus |
| 806 | Polygon.getNumInteriorRing binary compat | i23098 | P2 | L | L | L | — | binary compat |
| 797 | STRtree value generics | halset | P2 | L | L | L | — | index API |
| 715 | Opt-out Z interpolation (OverlayNG) | bjornharrtell | P1 | M | M | M | precision | OverlayNG elevation; Z not in R² corpus |
| 672 | PackedCoordinateSequence arrays | bjornharrtell | P2 | L | L | L | — | storage |
| 658 | Z handling LineSegment/Densifier | mukoki | P2 | L | M | L | — | Z dimension |
| 646 / 638 | CI Java matrix | carldea | P2 | L | L | L | — | CI (likely stale) |
| 499 | RFC ISO compliance tests | jagill | P1 | M | M | L | relate | Spec tests; useful corpus vectors if revived |
| 478 | Gaussian smooth + densifier | jgaffuri | P2 | M | H | L | S-*/DSF | New algorithms; high cost |
| 460 | mvn site javadoc | jodygarnett | P2 | L | L | L | — | build |
| 346 | Zero-length LineString relate | mukoki | P1 | M–H | M | M | **relate** | Dimension/relate edge cases; DE-9IM adjacent |
| 343 | OraReader empty sdo_geometry | nocny-x | P2 | L | L | L | — | Oracle IO |
| 319 | DepthSegment test input | FObermaier | P2 | L | L | L | buffer | test hygiene only |
| **311** | **isInCircleAdapt sketch** | Komzpa | **P0** | H | L | H | **mesh** | Adaptive in-circle (see §1) |
| 283 | TWKB parsing | atallahhezbor | P2 | L | L | L | — | IO |
| **279** | **CommonBits mantissa #253** | taromurao | **P1** | M | M | M | precision | Precision reduction numerics |
| 233 | Release assembly | jodygarnett | P2 | L | L | L | — | release packaging |
| 221 | PM change method | bjornharrtell | P2 | L | L | L | precision | refactor PM |
| 217 | Static ops / null geom | bjornharrtell | P2 | L | M | L | — | JSTS transpilation refactor |
| 200 | Move ops into operation classes | bjornharrtell | P2 | L | H | L | — | large structural; JSTS |
| **90** | **ScaledNoder (draft)** | jnh5y | **P1** | H | L | M | **precision** | **P1 policy watch** (not P0); YELLOW; scale=0 only |
| 83 | RadialDistanceByAngleSimplifier lab | FObermaier | P2 | M | M | L | S-* | lab module |

---

## §3 — Heatmap by corpus epic

| Epic | `topic:` | Open JTS PRs that matter | Corpus readiness |
|---|---|---|---|
| **#68** mesh | `mesh` | **1212, 1094, 311** | Strong: empty-circle, flip, degenerate pins, FFI in-circle |
| **#66** precision | `precision` | **1093, 1197, 90, 279, 715** | Strong: orient exact/filtered, snap, OverlayNG conditional; #90 wrapper-only YELLOW |
| **#67** relate / PIP | `relate` | **1145, 346, 499?, 1215** | Strong PIP gallery + DE-9IM; locator is consumer not new math |
| **#64/#65** core/buffer | `core`/`buffer` | 1196 densify; buffer PRs thin in open set | Densify DSF partial; buffer mostly issues not PRs |
| **#423** metric | `metric` | **1140, 926, 930** | Hausdorff discrete banked; percentile optional |
| **#425** coverage | `coverage` | **1084** | Cleaner landed; edge extractor next |
| **hull** | `hull` | **1217** (API), MBT already local | MBT theory present; MAR API free |
| **PLG** | precision/core | **968** | Euler/ring extract discharged; infinite-loop is engine bug |
| — out of scope | — | ~27 PRs | CI/IO/docs/API/Z/generics/JSTS |

---

## §4 — Explicit non-picks (do not spend proof budget)

- **CI / build / release**: 638, 646, 460, 233  
- **Docs / README / web**: 1218, 1137  
- **IO only**: 1164, 941, 343, 283  
- **API / generics / ART / binary compat**: 1220, 1215, 1170, 797, 806, 994, 1014  
- **Z-dimension / storage**: 658, 672, 715 (watch only for OverlayNG Z)  
- **Large stale structural (JSTS)**: 200, 217, 221  
- **Greenfield curves outside focus**: 836 Catmull-Rom, 478 Gaussian (unless product pull)  
- **Lab simplify**: 83  

---

## §5 — Conflict / supersession map

| Cluster | Members | Action |
|---|---|---|
| **In-circle robustness** | #311 → #1094 → **#1212** | Treat **#1212 as tip**; archive others as predecessors once merged. History: [`jts-311-incircle-lane-2026-08.md`](jts-311-incircle-lane-2026-08.md). FFI scout + review: [`jts-1094-incircle-lane-2026-08.md`](jts-1094-incircle-lane-2026-08.md). Tip differential: [`jts-1212-incircle-lane-2026-08.md`](jts-1212-incircle-lane-2026-08.md) |
| **Orientation filters** | #1093 (Ozaki production), #1197 (DD limits tests), #1189 (isCCW test INVALID) | **#1093 lane GREEN** ([jts-1093-orient-lane-2026-08.md](jts-1093-orient-lane-2026-08.md)); keep #1197; mine #1189 for vectors only |
| **PIP / YStripes** | **#1145** | **GREEN** ([jts-1145-pip-lane-2026-08.md](jts-1145-pip-lane-2026-08.md)): gallery 14/14; free CI for locator merge |
| **ScaledNoder policy** | #90 (draft) | **YELLOW** ([jts-90-scalednoder-lane-2026-08.md](jts-90-scalednoder-lane-2026-08.md)): SRN masks mukoki; scale=0 only; no algebra claim |
| **DistanceOp / LineSegment** | #926, #930 | One review pass if either moves; low proof cost |
| **CI matrix** | #638, #646 | Ignore unless JTS maintainers revive |

---

## §6 — Risk×cost matrix (hot set only)

```
        low cost ──────────────── high cost
high    1197 1216 1217            1093 (Ozaki prove-out)
risk    1212 1094 311
        1145 (gallery)
med     1140 926 930 968 90       1084 1196 346 478
low     1215 1220 …               200 836
```

**P0 (engage this month):** 1212/1094/311 · 1093 · 1197 · 1145  
**P1 (queue):** 90 (policy watch) · 1084 · 1140 · 1216 · 1217 · 968 · 279 · 1196 · 346 · 926/930  
**P2 (park):** the rest (~27)

---

## §7 — What “engage” means for a pick

| Action | When |
|---|---|
| **Differential pin** | Predicate already in corpus (in-circle, orient) — feed PR test coords to `oracle_bin` / FFI |
| **Gallery expansion** | New PIP (#1145) — add WKT cases to `nts-oracle-gallery` if RED vectors appear |
| **Claim registration** | New algorithmic claim with Qed path (percentile Hausdorff, coverage edges) |
| **Comment on JTS PR** | Only with numbers (sign mismatches, pin tables); avoid pure opinion |
| **NTS port watch** | Behaviour-preserving fixes (#1216) after JTS merge |

Do **not** open multi-session theory work for P2 PRs.

---

## §8 — Count check

| Bucket | Count |
|---|---|
| Open PRs inventoried | **49** |
| P0 | **6** (#1212, #1094, #311, #1093, #1197, #1145) — in-circle cluster counted as one product lane; #90 demoted after scope |
| P1 | **~13** (includes #90 policy watch) |
| P2 | **~30** |
| Authored by grootstebozewolf | 4 (#1197, #1215, #1216, #1217) |

(In-circle trio counted as three P0 rows still yields **P0 = 6** distinct PR numbers in §1 after #90 demotion to P1 policy watch.)

---

## §9 — Suggested one-liner picks for Joost / BDFL

1. **Bet the mesh lane on #1212** (with #1094/#311 as history) — highest corpus leverage per hour.  
2. **Orientation filter change (#1093) gated on exact orient** — session GREEN; re-run table if the PR is revised.  
3. **Use the PIP gallery as free CI for #1145** — **done GREEN** (14/14); suggest pinning WKT into JTS tests.  
4. **Ignore ~55% of the open queue** (CI/IO/docs/API) for proof planning.  
5. **Keep our four PRs** green; only #1197 and #1216 need corpus-adjacent attention.

---

## §10 — Sources

- GitHub API: `GET /repos/locationtech/jts/pulls?state=open` (49 results, 2026-08-05)  
- Per-PR file lists via `GET .../pulls/{n}/files`  
- Corpus: `TRIAGE_NTS_JTS_ISSUES.md`, `docs/verified-claims.md`, `#64–#69`, `#423`, `#425`, Delaunay/orient/PIP theories  

**AI assistance**: Grok (grok-4.5), human-directed.  
**License**: project documentation (BSD-3-Clause corpus).
