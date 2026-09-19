# GEOS rock-solid rung — oracle differential (2026-08-10)

**Trigger:** [libgeos/geos#1500](https://github.com/libgeos/geos/pull/1500) merged (`14fd2d7`) — GeometrySplitter/GeometryNoder fix for CurvePolygon drop (#1497).  
**Policy:** GEOS-first co-upstream (see `docs/geos-open-issues-triage-2026-08.md` §9).  
**Oracle:** `.ci-artifacts/oracle-bin-linux/oracle_bin`  
**Harness:** `tests/GeosOracleBugHunt/hunt.py` (`geosop` + oracle modes)

---

## Ladder (after #1500)

| Rung | Item | Status |
|---:|---|---|
| 0 | #1497 / #1500 splitter drop | **Merged** — hunt pin green |
| 1 | #1502 curve A/P PIP (rebase of #1322) | **Open PR** — rebased onto post-#1500 main; awaits maintainer CI |
| 2 | #968 covers L/P float | **PR #1505** — `isOnSegment` Ozaki-filter policy |
| 3 | Overlay #1342 / #1344 | Next (gallery + OverlayNG) |
| 4 | Splitter area leak #1495 / #1242 | Watch (linear splitter) |

---

## Oracle hunt summary (GEOS 3.15.0β3 + local fixes)

```
SUMMARY  ok=35  warn=6  bug=0  fail=0   (#968 fix applied)
```

Earlier (pre-#968): `ok=34 warn=6 bug=1` — only failure was `COVERS968/orig`.

| Surface | Oracle mode | Result |
|---|---|---|
| `CircularString` length | `ARC_LENGTH` | **OK** (bit-close on 7 arcs) |
| Point×CS distance | `ARC_DISTANCE` | **OK** (10 queries) |
| Envelope arc extrema | analytical pin | **OK** (MaxX=1 on −30°…50°) |
| CurvePolygon area | `ARC_AREA` / π | **OK** half-disk + unit disk |
| PIP half-disk | `POINT_IN_CURVE_RING` | **OK** hard; soft boundary notes (DE-9IM) |
| #1497 split | structure | **OK** curved component preserved |
| MultiSurface×MultiPoint | DE-9IM A/P | **OK** (#1502 branch) |
| #968 covers | — | **OK** after #1505 |

Soft PIP grid notes (not bugs) — two distinct conventions, per
[ADR-0003](adr/ADR-0003-two-tier-interior-spec-parity-computation.md)
(interior is two-tier: OGC open interior specifies, half-open ray
parity computes):

- **Chord `y=0`.** GEOS `contains=false` reports the **specification**
  tier (the OGC open interior excludes this boundary chord); the
  oracle's `IN` reports the **computation** tier (half-open ray parity
  includes it by construction, per `Overlay.edge_crosses_ray`). Both
  are correct about their own tier — this is ADR-0003's reclassification
  of the case from undecided to expected, not a divergence to chase.
- **Apex `(0,1)`.** GEOS `intersects=true` vs. oracle `OUT` is a
  *different* convention: the parity computation's `ray_avoids_vertices`
  genericity guard (tangent/vertex-grazing rays), which the two-tier
  model does not remove — ADR-0003 keeps it as a permanent, load-bearing
  guard, not a deferral.

---

## #968 fix design

**Bug:** `LINESTRING (1 0, 0 2)` / `POINT (0.9 0.2)` — covers false; distance ~2e-17.  
**Root:** `Orientation::index` = Ozaki filter (uncertain) → DD non-collinear.  
**Policy (isOnSegment only):**

| Filter | Result |
|---|---|
| certain LEFT/RIGHT | off |
| STRAIGHT or FAILURE | **on** |

`Orientation::index` unchanged for callers needing DD separation.  
**PR:** https://github.com/libgeos/geos/pull/1505  
**Local tests:** `test_geos_unit` ok:3934.

---

## Reproduce

```bash
# WSL — geosop from Release build; oracle from CI artifact
export GEOSOP=/home/user/geos-build/bin/geosop
export ORACLE=/mnt/c/com/github/grootstebozewolf/NetTopologySuite.Proofs/.ci-artifacts/oracle-bin-linux/oracle_bin
python3 tests/GeosOracleBugHunt/hunt.py
```

---

## Engagement log (addendum)

| When | Action |
|---|---|
| 2026-08-09 | #1500 merged (splitter) |
| 2026-08-10 | Rebased + force-pushed #1502 onto post-#1500 main |
| 2026-08-10 | Built GEOS in WSL; oracle hunt harness landed |
| 2026-08-10 | **PR** [libgeos/geos#1505](https://github.com/libgeos/geos/pull/1505) — #968 covers |
| 2026-08-10 | Next: Overlay #1342/#1344 differential gallery |

Assisted-by: xAI Grok
