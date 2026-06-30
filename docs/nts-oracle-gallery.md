# NTS Oracle Gallery — machine-verified point-in-polygon edge cases

A copy-paste gallery of **point-in-polygon / ray-crossing edge cases whose answer is
mechanically proven** in this Rocq/Coq corpus. Each case gives the polygon as WKT, a
query point, the **geometrically correct** answer, the **robustness gotcha** it
exercises, and the exact `Qed`-closed theorem that certifies the underlying fact — so
NetTopologySuite maintainers can drop them into `NetTopologySuite.Test` as regression
cases **without touching Coq**.

These target the most robustness-sensitive primitive in the stack: locating a point
against a ring (`RobustRayCrossingCounter` / `PointLocation` / `IPreparedGeometry.Contains`).
No new axioms, no new proofs were written for this gallery — it only transcribes results
that already end in `Qed`. Trust footprint of the corpus backing it: **3 classical-reals
axioms, exactly 1 (unrelated) registered `Admitted`** (`scripts/check_admitted.sh`).

> **The convention being tested.** The corpus predicate `point_in_ring` is the *pure*
> rightward-ray odd-crossing-parity test with a **strict y-straddle** rule (an edge counts
> iff `min(yA,yB) < y_query < max(yA,yB)`, i.e. the half-open vertex rule). That pure test
> is correct on points in *generic position*, but — by design — it can disagree with the
> true geometric answer exactly at **vertex grazes** and **horizontal edges at the query
> height**. The cases below pin both the correct answer and the naive miscount, which is
> precisely what a robust implementation must get right. The corpus also ships a `Z`-valued
> **winding number** whose parity is proven equal to the crossing parity
> (`WindingNumber.winding_decides_membership`), so either algorithm can be checked against
> these vectors.

---

## Tier 1 — robustness edge cases (exact rational coordinates)

### 1. Vertex graze — a *false negative* of naive ray casting

```
POLYGON ((0 1, 1 0, 0 -1, -1 0, 0 1))
```

| Query point | Correct answer | Naive rightward-ray crossing count | Note |
|---|---|---|---|
| `(0, 0.5)` | **Interior** | 1 (odd) | generic position — naive test is correct |
| `(0, 0)` | **Interior** (it is the centre) | **0 (even)** ⇒ naive says *Exterior* | the rightward ray passes exactly through vertex `(1, 0)`; under the strict y-straddle rule neither incident edge counts |

A robust counter (NTS `RobustRayCrossingCounter`, which special-cases rays through
vertices) must return **Interior** for `(0, 0)`. **Verified:** `diamond_point_in_ring_A`
and `diamond_not_point_in_ring_B` (`theories/JCT_VertexGrazingCounterexample.v`) prove the
crossing counts are exactly 1 and 0; `diamond_refutes_parity_seam` shows `(0,0)` and
`(0,0.5)` lie in the **same** complement component (so both are interior), which is why the
generic-position guard `ray_avoids_vertices` is necessary.

### 2. Horizontal edge at the query height — a *false positive* of naive ray casting

```
POLYGON ((0 0, 4 0, 4 2, 2 2, 2 1, 0 1, 0 0))
```
(an L-shaped / orthogonal polygon: the `[0,4]×[0,2]` box with the top-left `[0,2]×[1,2]`
quarter removed)

| Query point | Correct answer | Naive rightward-ray crossing count | Note |
|---|---|---|---|
| `(-1, 1)` | **Exterior** (it is left of the whole polygon) | **1 (odd)** ⇒ naive says *Interior* | the query height `y = 1` coincides with the horizontal edge `(2,1)–(0,1)` and the vertices at `y = 1` |

A robust counter must return **Exterior**. **Verified:** `notch_point_in_ring_pext`
(naive count is 1) together with `notch_pext_not_interior` (the point escapes leftward to
infinity — it is genuinely outside), and the headline
`notch_refutes_parity_without_guard` (`theories/JCT_HorizontalEdgeCounterexample.v`). This
is why the `no_horizontal_edge_at` guard is required for the bare parity test.

### 3. Half-open boundary convention of a rectangle

```
POLYGON ((0 0, 4 0, 4 3, 0 3, 0 0))
```

The pure ray-parity test classifies the rectangle's boundary **half-open**: the *left* and
*bottom-open* edges read as inside, the *right* and *top* edges as outside. **Verified:**
`point_in_ring_rect_iff` (`theories/RectangleJCT.v`): for `x0<x1`, `y0<y1`,
`point_in_ring p (rect_ring x0 y0 x1 y1) ↔ (y0 < y < y1 ∧ x0 ≤ x < x1)`.

| Query point | Pure ray-parity result | OGC `Contains` (boundary excluded) |
|---|---|---|
| `(2, 1.5)` | inside | Interior — `Contains = true` |
| `(0, 1.5)` (left edge) | **inside** (`x0 ≤ x`) | Boundary — `Contains = false` |
| `(4, 1.5)` (right edge) | outside (`x < x1`) | Boundary — `Contains = false` |
| `(2, 0)` (bottom edge) | outside (`y0 < y`) | Boundary — `Contains = false` |
| `(2, 3)` (top edge) | outside (`y < y1`) | Boundary — `Contains = false` |

Use this to pin the exact boundary-inclusion rule of a ray-crossing counter (NTS's
`RayCrossingCounter` reports `Location.Boundary` for the on-edge points; the half-open
columns are the *parity* convention the corpus and the winding number agree on).

### 4. Half-open hot-pixel box (snap-rounding)

```
POLYGON ((-0.5 -0.5, 0.5 -0.5, 0.5 0.5, -0.5 0.5, -0.5 -0.5))
```
(the unit hot pixel centred at the origin: `[-1/2, 1/2) × (-1/2, 1/2)`)

| Query point | Pure ray-parity result | Note |
|---|---|---|
| `(0, 0)` (centre) | **inside** | `unit_pixel_centre_in_ring` |
| `(0, -0.5)` (bottom edge) | **outside** | on the *included* bottom edge as a half-open *pixel* (`in_hot_pixel`), yet `point_in_ring` is false — the ray grazes the bottom-edge vertices |

**Verified:** `pixel_point_in_ring_iff_box` and `pixel_grazing_bottom_edge`
(`theories/HotPixelConvexRing.v`). The half-open pixel rule is what keeps a snap-rounding
noder from double-counting a segment that lands on a shared pixel edge.

---

## Tier 2 — concave / non-convex showcases (inside-the-hull exterior points)

These are the cases convex-only PIP shortcuts get wrong: a point inside the **convex hull**
but outside the **polygon**, in a reflex notch. Both are classified correctly by the
convexity-independent ray-parity test.

### 5. Spectre monotile (exact rational embedding)

```
POLYGON ((0 0, 2 0, 3.5 1, 4 0, 6 0, 7.5 1, 7 2, 5 2, 4.5 3, 3 2, 1 2, 0.5 1, -0.5 1, 0 0))
```

| Query point | Correct answer | Crossing count | Note |
|---|---|---|---|
| `(5, 0.5)` | **Interior** | 1 (odd) | between the two "feet" |
| `(3.5, 0.5)` | **Exterior** | 2 (even) | bottom reflex pocket — inside the hull, outside the tile |

**Verified:** `spectre_parity_classification` (`theories/SpectreConcaveFamily.v`):
`point_in_ring (5, 1/2) ∧ ¬ point_in_ring (7/2, 1/2)`. The ring is `ring_simple` and a
`valid_polygon` (rational coordinates throughout — no `sqrt 3`).

### 6. Hat monotile (irrational — coordinates are `APPROX`)

> ⚠️ The hat embeds with `y·√3/2`, so the WKT below is rounded. The corpus proves the
> result at the **exact** `√3` coordinates; treat the decimals as `APPROX` and prefer an
> exact-arithmetic check if your harness supports it.

```
POLYGON ((0 0, 2 0, 3.5 0.8660254, 4 0, 6 0, 7.5 0.8660254, 7 1.7320508, 5 1.7320508,
          4.5 2.5980762, 3 1.7320508, 1 1.7320508, 0.5 0.8660254, -0.5 0.8660254, 0 0))
```

| Query point (exact) | Correct answer | Crossing count | Note |
|---|---|---|---|
| `(17/4, 5√3/4)` ≈ `(4.25, 2.1650635)` | **Interior** | 1 (odd) | top bump |
| `(7/2, √3/4)` ≈ `(3.5, 0.4330127)` | **Exterior** | 2 (even) | bottom reflex notch |

**Verified:** `hat_parity_classification` (`theories/HatMonotileExterior.v`); the ring is
`hat_ring_simple` and proven genuinely non-convex (`hat_non_convex`).

---

## Cross-check with the winding number

The corpus also defines an `atan2`-free, `Z`-valued winding number (the signed
ray-crossing count) and proves its parity decides membership:

- `WindingNumber.winding_number : Point → Ring → Z` — `+1` per upward crossing, `−1` per
  downward.
- `WindingNumber.winding_decides_membership` — under `no_horizontal_edge_at`,
  `Z.odd (winding_number p r) = true ↔ point_in_ring p r`.
- `WindingNumber.winding_parity_eq_crossing_parity` —
  `Z.odd (winding_number p r) = Nat.odd (count_crossings_ray p r)`.

So every Tier-1/Tier-2 vector above is *simultaneously* a winding-parity test: the winding
number is odd exactly on the **Interior** rows and even on the **Exterior** rows (subject
to the same vertex-graze / horizontal-edge caveats, which is exactly why those rows are
called out).

---

## Mapping to NTS operations and the TRIAGE tracker

| Case | NTS surface | `TRIAGE_NTS_JTS_ISSUES.md` |
|---|---|---|
| 1 vertex graze | `RobustRayCrossingCounter`, `PointLocation.Locate`, `Geometry.Contains` | #67 (RelateNG / boundary), V-CP |
| 2 horizontal edge | `RobustRayCrossingCounter` (horizontal-edge handling) | #67, JTS#1175 lineage |
| 3 rectangle half-open | `RayCrossingCounter.LocatePointInRing` boundary rule | #67, V-CP |
| 4 hot-pixel half-open | `SnapRoundingNoder` / `HotPixel` | #66 (snap-rounding) |
| 5 Spectre / 6 Hat | `PointLocation`, `Geometry.Contains` on concave rings | #67, V-CP; `POINT_IN_CURVE_RING` oracle |

## Provenance

Every "Correct answer" / crossing count above is a `Qed`-closed theorem in the file named
beside it (`theories/JCT_VertexGrazingCounterexample.v`,
`theories/JCT_HorizontalEdgeCounterexample.v`, `theories/RectangleJCT.v`,
`theories/HotPixelConvexRing.v`, `theories/SpectreConcaveFamily.v`,
`theories/HatMonotileExterior.v`, `theories/HatMonotileInterior.v`,
`theories/WindingNumber.v`). The ray-crossing semantics are `Overlay.point_in_ring`
(odd-parity over `ring_edges`) with the bool mirror `PointInRingCorrect.segment_crosses_ray`
and its correctness theorem `segment_crosses_ray_correct`.

## A ready-to-paste NTS regression sketch

```csharp
// NetTopologySuite.Test — verified PIP edge cases (see docs/nts-oracle-gallery.md)
using NetTopologySuite.Algorithm.Locate;
using NetTopologySuite.Geometries;
using NetTopologySuite.IO;

var rdr = new WKTReader();

// Case 1 — vertex graze: the diamond centre (0,0) is INTERIOR despite the
// rightward ray passing through vertex (1,0). Robust PIP must not miss it.
var diamond = (Polygon)rdr.Read("POLYGON ((0 1, 1 0, 0 -1, -1 0, 0 1))");
var loc = new IndexedPointInAreaLocator(diamond);
Assert.That(loc.Locate(new Coordinate(0, 0)),   Is.EqualTo(Location.Interior));
Assert.That(loc.Locate(new Coordinate(0, 0.5)), Is.EqualTo(Location.Interior));

// Case 2 — horizontal edge at query height: (-1,1) is EXTERIOR.
var notch = (Polygon)rdr.Read("POLYGON ((0 0, 4 0, 4 2, 2 2, 2 1, 0 1, 0 0))");
Assert.That(new IndexedPointInAreaLocator(notch).Locate(new Coordinate(-1, 1)),
            Is.EqualTo(Location.Exterior));

// Case 5 — concave Spectre: hull-interior pocket point is EXTERIOR.
var spectre = (Polygon)rdr.Read(
  "POLYGON ((0 0, 2 0, 3.5 1, 4 0, 6 0, 7.5 1, 7 2, 5 2, 4.5 3, 3 2, 1 2, 0.5 1, -0.5 1, 0 0))");
var sloc = new IndexedPointInAreaLocator(spectre);
Assert.That(sloc.Locate(new Coordinate(5,   0.5)), Is.EqualTo(Location.Interior));
Assert.That(sloc.Locate(new Coordinate(3.5, 0.5)), Is.EqualTo(Location.Exterior));
```

*(Boundary-row cases from Tier 1.3/1.4 assert `Location.Boundary`; the half-open columns
describe the internal ray-parity convention, not OGC `Contains`.)*

---

*Generated as part of the NetTopologySuite.Proofs corpus. AI-drafted, human-reviewed.
Assisted-by: Claude. BSD-3-Clause.*
