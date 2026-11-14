<!-- doc-kind: finding
date: 2026-08-05
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
Thanks for the clear MRE and screenshots — there are really **two separate questions** mixed in here:

1. Whether an edge is "non-Delaunay" under `ConformingDelaunayTriangulationBuilder`
2. How to filter the hull triangulation down to the **interior of a concave polygon**

### 1) "Non-Delaunay" edges under CDTB

`ConformingDelaunayTriangulationBuilder` is **not** unconstrained Delaunay of the vertex set. Constrained polygon edges are forced into the mesh (with Steiner insertion in the *conforming* sense). An edge that looks "bad" on a screenshot is not, by itself, a defect if it is a **constraint** (or a refined constraint segment).

Local Delaunay legality is the **empty-circle** test (Shewchuk / Guibas–Stolfi): for a CCW triangle `ABC` and opposite vertex `D` of the shared-edge quad, the edge is strictly illegal iff the oriented in-circle determinant is **positive**.

We re-ran your sites on **NTS 2.6.0** with your scale (`1e5` + round), `Tolerance = 0.1`, sites = constraints = the polygon, and checked **every internal edge** against that criterion (via the extracted `b64_inCircle` kernel from [NetTopologySuite.Proofs](https://github.com/MerkatorBV/NetTopologySuite.Proofs) — same arithmetic as the Phase 5 `nts_rocq_in_circle` FFI):

| Metric | Result (NTS 2.6.0) |
|---|---|
| Total triangles | 34 |
| Internal edges checked | 45 |
| Strict empty-circle violations (`inCircle > 0`) | **0** |

So on current NTS, this input produces a mesh with **no** strict local-Delaunay violations on internal edges (including free edges). Steiner points do appear (non-integer vertices after integer scale), which is expected for conforming refinement.

You are on **NetTopologySuite.Core 1.15.3**, which is quite old relative to the 2.x line. If a green-marked edge still looks wrong after upgrading, please post the **four coordinates of the quad** (two triangles sharing the edge, including any Steiner points). Visual inspection alone is not enough to call it illegal.

Related upstream quality class for CDTB + already-Delaunay / degenerate constraints: [locationtech/jts#1190](https://github.com/locationtech/jts/issues/1190).

### 2) Exterior triangles after centroid filtering

`GetTriangles` triangulates the **sites' convex hull** with constraints. It does **not** return "triangles of the polygonal face." Interior selection is always a **post-process** — that is expected API behaviour, not the builder testing against the convex hull instead of your polygon.

For a concave polygon, many hull triangles sit in **reflex pockets** (inside the convex hull, outside the polygon). Those must be dropped by a correct point-in-polygon test on a representative point of the triangle (centroid is the usual choice when the mesh does not straddle the boundary).

Same re-run on NTS 2.6.0 with your filter:

```csharp
locator.Locate(t.Centroid.Coordinate) == Location.Interior
```

| Metric | Result |
|---|---|
| Centroid Interior / Exterior / Boundary | **22 / 12 / 0** |
| Interior-centroid triangles not fully `polygon.Covers(t)` | **0** (no straddlers) |
| `polygon.IsValid` | `true` |
| Shell CCW | `false` (CW shell; area still positive; locator still worked) |

So on modern NTS the centroid + `IndexedPointInAreaLocator` path **does** drop the 12 exterior pocket triangles and keeps 22 fully covered interior triangles. The "blue exterior triangles kept" behaviour did **not** reproduce on 2.6.0 for this MRE (also with unscaled coords and `Tolerance = 0`).

If 1.15.3 still keeps exterior faces after the same filter, that is best treated as a **version-specific** issue: please try current NTS 2.x first.

### Practical suggestions

1. **Upgrade** off 1.15.3 to current NTS 2.x and re-run the MRE.
2. Confirm `polygon.IsValid` after scale/round/`Distinct()`; self-intersections after snapping break both CDTB and PIP.
3. Prefer certifying "non-Delaunay" with an explicit in-circle test on the shared-edge quad (four points, full vertex set including Steiner), not the screenshot.
4. If centroids ever sit on the skeleton, try `Locate != Exterior` (boundary-tolerant) for skinny near-edge triangles.
5. A dual walk across **constraint** edges (seed an interior face, flood until you cross a constraint) is often more stable than centroid filtering when Steiner density is high — but for this simple valid ring, centroid filtering is already sound on 2.6.0.

Happy to dig further if you can confirm whether the green edge is a **constraint** segment and/or whether the exterior-filter bug still appears after upgrading.

*(Repro notes / empty-circle criterion write-up: [nts-discussion-839-scout](https://github.com/MerkatorBV/NetTopologySuite.Proofs/blob/main/docs/nts-discussion-839-scout.md) in NetTopologySuite.Proofs.)*
