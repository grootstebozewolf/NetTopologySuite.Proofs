<!-- doc-kind: finding
date: 2026-08-21
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# Oracle bug hunt — NTS#857 curves vs Rocq `oracle_bin`

**Date**: 2026-08-08  
**NTS branch**: `feat/curves-structure-wkt-foundation` (`NetTopologySuite` @ curves foundation + GEOS WKB dovetail)  
**Oracle**: CI artifact `oracle-bin-linux` from  
[actions/runs/31253549636](https://github.com/MerkatorBV/NetTopologySuite.Proofs/actions/runs/31253549636)  
(artifact id `9020854736`) → `.ci-artifacts/oracle-bin-linux/oracle_bin`  
**Harness**: `tests/CurveOracleBugHunt` (WSL-invoked oracle, ProjectReference to NTS)

```
SUMMARY  ok=12  warn=0  bug_or_fail=14
```

---

## Verdict

| Surface | Status vs oracle / soundness |
|---|---|
| **WKT / WKB structure** | **OK** — round-trip EqualsExact for CS / CC / CP / MultiCurve / MultiSurface |
| **chord ≤ arc length** | **OK** — oracle theorem holds on samples (end-chord vs `ARC_LENGTH`) |
| **Length** | **BUG (metric)** — `CircularString.Length` = control-polyline, not arc length |
| **Envelope** | **BUG (metric)** — control-point bbox can miss axis extrema of the true arc |
| **Distance** | **BUG (severe)** — `DistanceOp` returns **`double.MaxValue`** for Point×CircularString |

---

## Findings (oracle-backed)

### B1 — `CircularString.Length` is chord polyline (oracle `ARC_LENGTH`)

Implementation: `Algorithm.Length.OfLine(_points)` — sums control chords, not \(r\cdot\theta\).

| Case | NTS Length | Oracle arc | Short by |
|---|---:|---:|---:|
| unit quarter | 1.5307… | π/2 ≈ 1.5708 | **2.55%** |
| unit semicircle | 2.8284… | π ≈ 3.1416 | **9.97%** |
| R=5 semicircle | 14.14… | 15.708… | **9.97%** |
| off-centre 90° | 3.414… | 4.712… | **27.55%** |
| near-flat | ~10.00002 | ~10.000027 | tiny |

Oracle mode: `ARC_LENGTH` (interface-boundary float over exact rational invariants; allowlisted).  
Proof companion: `theories/ArcLength.v` / `chord_le_arc_length`.

**Severity**: High for any consumer that trusts `Geometry.Length` on curves.  
**Fix direction**: Analytical arc length (port GEOS / oracle formula); keep chord as explicit `ILinearizable` path only.

---

### B2 — Envelope under-approximates true arc (control bbox)

Comment in code already admits “conservative: enclose all control points” but that is **not** conservative for extents — it can **exclude** points on the arc.

**Witness**: unit circle arc controls at −30°, 10°, 50°:

| | MaxX |
|---|---:|
| Control-point envelope (NTS) | ≈ 0.9848 (cos 10°) |
| True arc (angle 0° on unit circle) | **1.0** |

GEOS implements analytical envelope for circular arcs.

**Severity**: High for filters, indexes, short-circuit predicates.  
**Fix direction**: Expand envelope by arc extrema (cardinal angles on circle within sweep); GEOS `CircularString` envelope path.

---

### B3 — `DistanceOp` returns `double.MaxValue` on curves (**P0**)

For every Point×CircularString sample, NTS returned `1.797…E+308` (`double.MaxValue`), while oracle `ARC_DISTANCE` returned finite values (e.g. centre of unit semicircle → **1**, endpoint → **0**).

Root cause: `DistanceOp` initializes `_minDistance = double.MaxValue` and **never visits** curve control segments / arcs for non-`LineString` lineals, so the un-updated sentinel is returned.

**Severity**: **Critical** — silent wrong distance (not even “chord approx”); looks like “infinitely far”.  
**Fix direction** (minimal foundation bar):

1. **Fail closed**: throw `NotSupportedException` for non-linearized curves in `DistanceOp`, **or**
2. **Chord fallback**: extract control polylines / `ILinearizable.Linearize()` before distance, **or**
3. **Arc-aware** (oracle `ARC_DISTANCE` / GEOS distance ops).

Until fixed, any spatial join / nearest-neighbour over curves is unsafe.

---

### Structural (green)

WKB/WKT GEOS dovetail round-trips:

- CircularString, CompoundCurve, CurvePolygon, MultiCurve, MultiSurface — **OK**

---

## How to reproduce

```powershell
# artifact already at .ci-artifacts/oracle-bin-linux/oracle_bin
cd C:\com\github\grootstebozewolf\NetTopologySuite.Proofs\tests\CurveOracleBugHunt
# NTS must be on feat/curves-structure-wkt-foundation
dotnet run -c Release
```

Oracle is invoked via `wsl -e …/oracle_bin` with modes `ARC_LENGTH` / `ARC_DISTANCE`.

---

## Recommended NTS#857 follow-ups (priority)

| Pri | Item |
|---:|---|
| **P0** | Distance: never return `MaxValue` for supported/unsupported curves (throw or linearize) |
| **P1** | Envelope: analytical (or densify-with-sagitta) for CircularString / CompoundCurve |
| **P1** | Length: analytical arc length (or document + rename API; do not claim `Geometry.Length` = measure) |
| P2 | Area / centroid / PIP vs `ARC_AREA` / `POINT_IN_CURVE_RING` (next hunt pass) |

---

## Artifact provenance

| Item | Value |
|---|---|
| Run | https://github.com/MerkatorBV/NetTopologySuite.Proofs/actions/runs/31253549636 |
| Artifact | `oracle-bin-linux` (id 9020854736) |
| Local path | `.ci-artifacts/oracle-bin-linux/oracle_bin` |
| Also present | `.ci-artifacts/libntsrocq-linux-x64/libntsrocq.so` (unused this pass) |
