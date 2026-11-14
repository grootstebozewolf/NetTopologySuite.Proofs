<!-- doc-kind: finding
date: 2026-08-21
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# Scout — open [libgeos/geos](https://github.com/libgeos/geos) issues vs NetTopologySuite.Proofs

**Date**: 2026-08-08.  
**topic:** `docs` (routing); epics touched: `core` / `buffer` / `precision` / `relate` / `coverage` / curve lane `#64`–`#69`.  
**Clone**: `C:\com\github\grootstebozewolf\GEOS` @ **`5b62cd0`** (`main`, shallow).  
**Question**: With GEOS as a candidate co-upstream for SQL/MM curve foundation (NTS#857 / JTS silence), how large is the open-issue surface, and can the Proofs corpus help any of it?

---

## §0 — Gate (user rule)

| Condition | Action |
|---|---|
| Open **issues** ≤ 50 | Treat GEOS as mature enough for a **direct port into NetTopologySuite** (sidestep JTS stall; match maintainer “upstream” wish via GEOS) |
| Open **issues** > 50 | **Random-sample triage** with a **recorded seed**; map sample to corpus IFF/oracle help |

| Metric (2026-08-08) | Count |
|---|---:|
| Open **issues** (`is:issue is:open`) | **106** |
| Open **PRs** | **10** |
| GitHub `open_issues_count` (issues+PRs) | 116 |

**Gate result: 106 > 50 → sample + corpus map (this doc). Direct full-library port is not auto-approved.**

**Nuance (curve foundation only):** open items with label `Curves` or SQL/MM curve title keywords = **1 issue** (+ open PR #1322). Type/IO foundation is landed in GEOS; residual risk is ops quality, not hierarchy design.

---

## §1 — Sampling protocol (reproducible)

| Parameter | Value |
|---|---|
| **Seed** | **`20260808`** (YYYYMMDD of triage day) |
| RNG | Python 3 `random.Random(SEED)` |
| Population | All open **issues** (PRs excluded), N = 106 |
| Sample size | **20** |
| Forced stratum | Label `Curves` **or** title matches SQL/MM curve keywords (`circular`, `compoundcurve`, `curvepolygon`, `multicurve`, `multisurface`, `curved geometr`, `sql/mm`) |

### Reproduce

```python
import json, random
# items = list of {number, title, labels, ...} for 106 open issues
SEED, SAMPLE_SIZE = 20260808, 20
nums = [i["number"] for i in items]
print(sorted(random.Random(SEED).sample(nums, SAMPLE_SIZE)))
```

### Sample numbers

```
660, 695, 872, 947, 968, 1036, 1202, 1235, 1291, 1324,
1339, 1342, 1344, 1367, 1404, 1476, 1481, 1492, 1494, 1497
```

### Forced curve stratum

| # | Title | Labels |
|---:|---|---|
| [1497](https://github.com/libgeos/geos/issues/1497) | CurvePolygon: Missing curved geometry after splitting | Bug, Curves |

(Only open `Curves`-labeled issue at triage time.)

### Deep set

Sample ∪ forced = sample (1497 already drawn). **20 issues** deep-read.

---

## §2 — Full backlog label histogram (all 106 issues)

| Label | Count |
|---|---:|
| Bug | 35 |
| (unlabeled) | 33 |
| Overlay | 16 |
| Enhancement | 13 |
| Buffer | 11 |
| Feedback Requested | 8 |
| Predicates | 7 |
| M | 7 |
| JTS | 6 |
| Triangulation | 6 |
| **Curves** | **1** |
| CMake | 1 |
| Good First Issue | 1 |

**OffsetCurve** bugs (buffer parallel curves) are **not** SQL/MM curve types; do not count them as `Curves` foundation debt.

---

## §3 — Deep triage (sample × Proofs corpus)

**“Corpus help”** = whether NetTopologySuite.Proofs Qed claims / extractable oracles / prior JTS–NTS triage can **pin, differentially gate, or specify** the GEOS issue (same role as `TRIAGE_NTS_JTS_ISSUES.md`).

| Pri | # | Title | Labels | Epic | Corpus help | Action |
|---:|---:|---|---|---|---|---|
| **P0** | [1497](https://github.com/libgeos/geos/issues/1497) | CurvePolygon missing curved part after split | Bug, Curves | **#64 / #69** + splitter | **Yes** — structure-preserving `CURVEPOLYGON`/`COMPOUNDCURVE`; split vs densify identity | **Engage** (curve lane) |
| **P0** | [1344](https://github.com/libgeos/geos/issues/1344) | Union vastly wrong | Bug, Overlay | **#66** | **Yes** — OverlayNG wrong-output gallery | **Engage** |
| **P0** | [1342](https://github.com/libgeos/geos/issues/1342) | Intersection multipolygon → invalid | Bug | **#66** | **Yes** — invalid overlay output / ring guards | **Engage** |
| **P1** | [968](https://github.com/libgeos/geos/issues/968) | Covers Line/Point float robustness | Bug, Predicates | **#67** | **Yes** — DE-9IM covers; on-segment exactness | **Engage** (predicate pins) |
| **P1** | [660](https://github.com/libgeos/geos/issues/660) | Buffer intersects source line | JTS, Buffer | **#65** | **Partial** — buffer enclosure / depth CEs; `BUFFER_REGION` | Watch / pin if buffer port |
| **P1** | [1036](https://github.com/libgeos/geos/issues/1036) | OffsetCurve → MultiLineString contiguous | Bug, Buffer | **#65** / OffsetCurve | **Partial** — join/merge policy; JTS#1147 / NTS#815 wire | Watch |
| **P1** | [1339](https://github.com/libgeos/geos/issues/1339) | Offset extra pts near-closed | Bug | **#65** | **Partial** — near-coincident endpoint class | Watch with #1036 |
| **P1** | [1476](https://github.com/libgeos/geos/issues/1476) | CleanCoverage snap collapses waist | — | **#425** coverage | **Partial** — coverage cleaner; **spec** question | Watch |
| **P2** | [1494](https://github.com/libgeos/geos/issues/1494) | Splitter at endpoint self-intersection | — | noding/split | Weak — combinatorial policy | Watch |
| **P2** | [1481](https://github.com/libgeos/geos/issues/1481) | Method to add vertices to polygon | Enhancement | noding UX | Weak — product API | Park |
| **P2** | [1324](https://github.com/libgeos/geos/issues/1324) | MakeValid preserve M | Enhancement, M | Z/M | No | Park (proofs) |
| **P2** | [1367](https://github.com/libgeos/geos/issues/1367) | Point ∩ LineStringZM drops M | Overlay, M | Z/M | No | Park |
| **P2** | [695](https://github.com/libgeos/geos/issues/695) | Remove old overlay engine? | Feedback, Overlay | policy | No | Park |
| **P2** | [872](https://github.com/libgeos/geos/issues/872) | XY CoordinateSequence algorithms | Feedback | plumbing | No | Park |
| **P2** | [947](https://github.com/libgeos/geos/issues/947) | i386 MinimumAreaRectangle fails | — | platform/hull | Weak | Park |
| **P2** | [1202](https://github.com/libgeos/geos/issues/1202) | SimpleSTRtree remove | — | index | No | Park |
| **P2** | [1235](https://github.com/libgeos/geos/issues/1235) | oriented_envelope /0 | — | hull/FP | No | Park |
| **P2** | [1291](https://github.com/libgeos/geos/issues/1291) | oriented_envelope MultiLineString | — | hull | No | Park |
| **P2** | [1404](https://github.com/libgeos/geos/issues/1404) | C prototypes `(void)` | — | C API | No | Park |
| **P2** | [1492](https://github.com/libgeos/geos/issues/1492) | FE_INVALID on macOS | — | platform FP | Weak (#515 class) | Park |

### Open curve-adjacent PRs (not in issue sample)

| PR | Title | Corpus |
|---:|---|---|
| [1322](https://github.com/libgeos/geos/pull/1322) | CurvePolygon PIP → contains / disjoint | **#67 / V-CP / R-CONT** — `POINT_IN_CURVE_RING`, `CURVE_RELATE_MATRIX` |
| [1460](https://github.com/libgeos/geos/pull/1460) | GeometryNoder collection identity | **#66** noding (weak arc-specific) |
| [1500](https://github.com/libgeos/geos/pull/1500) | GeometrySplitter: Avoid dropped component | Likely **#1497** fix path — track |

### Corpus help ranked

1. **#1497 + #1322 (+ #1500)** — curve structure / PIP / splitter (JTS epic #1195 + Proofs #64/#67/#69).  
2. **#1342 / #1344** — OverlayNG invalid/wrong output gallery (#66).  
3. **#968** — covers L/P float robustness (#67).  
4. **#660 / #1036 / #1339** — buffer/offset quality (#65; already wired to JTS OffsetCurve issues).  
5. **#1476** — coverage snap semantics (#425 soft).

---

## §4 — GEOS curve landing (how foundation shipped)

Design lived on PRs, **not** GitHub Discussions. Label: **`Curves`**.

| Phase | What | Key PRs | Release |
|---|---|---|---|
| Foundation | In-core hierarchy + WKT; envelope; **fail-closed** other C-API ops | [#1046](https://github.com/libgeos/geos/pull/1046) (merged 2024-04-30) | **3.13** |
| I/O + C create | WKB R/W; create empty/non-empty curved types | #1104, #1106, #1108 | 3.13 |
| Validation | CompoundCurve continuity, empty members, closed rings | #1164, #1282, #1393 | 3.13–3.14 |
| Metrics attempt | length / area / arc PIP | [#1111](https://github.com/libgeos/geos/pull/1111) **closed unmerged** 2024-08-16 | — |
| Primitives | `CircularArcIntersector`, arc noding | #1171, #1347, #1418 | → 3.15 |
| Ops wave | boundary, normalize, distance, polygonizer, OverlayNG, linearize/curve, splitter, … | #1382, #1394, #1420, #1427, #1428, … | **3.15β** |

**#1046 hierarchy (siblings, not OGR’s CurvePolygon→Polygon):**

```text
Curve → SimpleCurve → { LineString, CircularString }
     → CompoundCurve
Surface → { Polygon, CurvePolygon }
GeometryCollection → { MultiCurve, MultiSurface }
```

**#1046 review social proof:** `@pramsey` early approve; QGIS (`@m-kuhn`, `@lbartoletti`) OK with OGR divergence; `@dr-jts` only asked to mark Draft — **no “wait for JTS” veto**.

**Minimum merge bar (dbaston, 2024-04-16):** types + WKT + envelope + error out unsupported ops — same shape as NTS#857 Phase 1.

Sponsors credited on 3.13: German QGIS users group / Canton of Basel-Landschaft / Canton of Zug.

---

## §5 — Implications for NTS#857 / maintainer “upstream”

| Scope | Under this gate | Recommendation |
|---|---|---|
| Port **all** of GEOS into NTS | 106 open issues; hard overlay/buffer/FP debt | **No** — not a clean freeze |
| Port **curve foundation only** (types + WKT, GEOS contracts, fail-closed ops) | 1 open `Curves` issue; foundation landed 3.13+ | **Yes, as co-upstream** — does not require JTS merge |
| Wait until GEOS open issues ≤ 50 | Global backlog gate | **Blocks indefinitely** without measuring curve readiness |
| Wait for JTS #1194/#1198 | Closed unmerged; maintainer silence | **Open-ended** |

**NTS maintainer mapping:**

- “Upstream” = *merged locationtech/jts* → still blocked.  
- “Upstream” = *maintained JTS-family implementation of SQL/MM types+IO* → **GEOS 3.13+ is that**.  
- Global ≤50 gate failed → do **not** sell full-library parity; **do** sell scoped foundation port with GEOS as the behavioral pin (plus Proofs oracles for arc metrics later).

---

## §6 — Recommended next work (this repo / NTS)

1. **Curve lane** — Pin #1497 WKT pair + expected collection shapes in proofs/oracle or NTS test gallery; watch #1500 / #1322.  
2. **Overlay gallery** — Harvest #1342/#1344 WKT when filing NTS/JTS differential cases (#66).  
3. **Predicate pin** — #968 Line/Point covers float case → #67 / RelateNG bank.  
4. **NTS#857 comment** — cite seed `20260808`, 106 vs 1 Curves split, GEOS #1046 minimum bar, offer GEOS-contract foundation (not full GEOS port).  
5. **Do not** open a “port entire GEOS” epic from this triage.

---

## §7 — Artifacts

| Path / ref | Role |
|---|---|
| `C:\com\github\grootstebozewolf\GEOS` @ `5b62cd0` | Local clone |
| Seed **`20260808`**, sample size 20 | Reproducible selection |
| This file | Durable triage |
| `TRIAGE_NTS_JTS_ISSUES.md` | Parent NTS/JTS ↔ corpus map |
| Prior session notes | GEOS curve PR inventory (#1046…#1480) |

### Draft comment for NetTopologySuite#857 (paste-ready)

```markdown
### GEOS open-issue triage (2026-08-08) — co-upstream for foundation?

I cloned `libgeos/geos` and applied a maturity gate on **open issues**:

| Gate | Result |
|---|---|
| Open issues ≤ 50 → treat GEOS as quiet enough for a direct full port into NTS | **Not met** (106 open issues, 10 open PRs) |
| Open issues > 50 → random sample + map to formal/oracle work | **Applied** |

**Recorded sample seed:** `20260808` (Python `random.Random`, n=20 of 106).  
Deep set included the only open `Curves`-labeled issue: [libgeos/geos#1497](https://github.com/libgeos/geos/issues/1497) (CurvePolygon split drops arc component). Open curve-adjacent PR: [#1322](https://github.com/libgeos/geos/pull/1322) (PIP/predicates).

**Split that matters for this PR:**

- **Global GEOS backlog** is large (overlay, buffer, platform FP, Z/M, …) → not a signal to “port all of GEOS.”
- **SQL/MM curve foundation surface** is small: types + WKT/WKB already shipped in GEOS **3.13** via [#1046](https://github.com/libgeos/geos/pull/1046) (hierarchy + WKT + envelope + fail-closed ops), then #1104/#1106/#1108 (WKB + C create). That is the same Phase-1 bar as this PR. Remaining curve work is ops polish (splitter/PIP), not “should we have types?”

GEOS did **not** wait for JTS: design review was on #1046 (`@pramsey` buy-in; QGIS OK with sibling `Polygon`/`CurvePolygon` hierarchy; no JTS-merge gate). Metrics/ops came later in many small PRs (and #1111 length/area/PIP was even closed unmerged before the ops wave).

So if “upstream support” means *a maintained JTS-family implementation of structure + WKT*, GEOS already is that co-upstream. If it means *merged locationtech/jts*, we remain blocked on silence there.

Happy to keep **this PR scoped** as GEOS-aligned foundation (types + WKT + linearize escape; no arc overlay), and treat GEOS contracts + open curve bugs (#1497) as the pin surface — without claiming full GEOS algorithmic parity.

Write-up: NetTopologySuite.Proofs `docs/geos-open-issues-triage-2026-08.md`.
```

---

## §8 — Verdict (headline)

| Question | Answer |
|---|---|
| Direct **full** GEOS→NTS port under ≤50 gate? | **No** (106 open issues) |
| Seed recorded? | **Yes — `20260808`** |
| Corpus helps sample? | **Yes on a minority** — curve #1497, overlay #1342/#1344, covers #968, buffer/offset cluster |
| Curve **foundation** ready enough to cite as co-upstream for NTS#857? | **Yes** — 1 open Curves issue; #1046-style land already done in GEOS |
| Next product move | **GEOS-first** (not JTS). Scoped GEOS-contract foundation; engage open curve PRs/issues |

---

## §9 — Engagement log (GEOS-first pivot)

| When | Action |
|---|---|
| 2026-08-08 | NTS#857 comment: GEOS as co-upstream ([comment](https://github.com/NetTopologySuite/NetTopologySuite/pull/857#issuecomment-5225495128)) |
| 2026-08-08 | **Approved** [libgeos/geos#1500](https://github.com/libgeos/geos/pull/1500) (splitter/noding fix for #1497) |
| 2026-08-08 | **Commented** [libgeos/geos#1322](https://github.com/libgeos/geos/pull/1322) (curve A/P PIP; empty multipoint note) |
| 2026-08-08 | **#1502** local build green; fix Contains boundary/empty DE-9IM; CI awaits maintainer approval |
| 2026-08-08 | **PR** [libgeos/geos#1502](https://github.com/libgeos/geos/pull/1502) — rebase of #1322 + empty MultiPoint guards |
| 2026-08-08 | Fork [grootstebozewolf/geos](https://github.com/grootstebozewolf/geos); local remotes: `origin`=fork, `upstream`=`libgeos/geos` |
| 2026-08-09 | **#1500 merged** — #1497 CurvePolygon splitter drop fixed |
| 2026-08-10 | Rebased/force-pushed #1502 onto post-#1500 `main` |
| 2026-08-10 | Oracle hunt harness `tests/GeosOracleBugHunt` — curve metrics/PIP/#1497 green |
| 2026-08-10 | **PR** [libgeos/geos#1505](https://github.com/libgeos/geos/pull/1505) — #968 covers L/P (`isOnSegment` Ozaki-filter policy) |
| 2026-08-10 | Write-up `docs/geos-oracle-rung-2026-08.md` |

**Pause JTS curve lobby** unless a maintainer reopens #1194-class work. Energy goes to GEOS curve ops quality + pins.