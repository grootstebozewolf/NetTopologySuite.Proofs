<!-- doc-kind: finding
date: 2026-08-05
Provenance: pre-ratchet
Theorems: none — pre-ratchet record; anchors in the body are not re-checked
-->
# Scout — NTS discussion #839 (ConformingDelaunay + concave polygon)

**topic:** `mesh` (Delaunay / CDTB legality; PIP post-filter is secondary substrate).  
**Date**: 2026-08-05.  
**Upstream**: [NetTopologySuite/NetTopologySuite#discussion-839](https://github.com/NetTopologySuite/NetTopologySuite/discussions/839)
  — *ConformingDelaunayTriangulationBuilder Concave polygon* (CodeTwentyNineLtd, 2026-03-15; unanswered at scout time).  
**Corpus home**: epic [#68](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/issues/68) (`topic: mesh`), with
  PIP / ray-parity substrate from Phase 3 JCT (`point_in_ring`, counterexample gallery).  
**Related upstream**: [locationtech/jts#1190](https://github.com/locationtech/jts/issues/1190)
  (ConformingDelaunay quality / already-Delaunay constraints) — already wired to #68 in `TRIAGE_NTS_JTS_ISSUES.md`.  
**Scope**: 1–2 hour corpus inventory + claim triage (no new proofs this session).  
**Question**: What can this corpus *already* say, with `Qed`, about the two complaints in #839 —
  (A) an apparently non-Delaunay triangle in the CDT output, and
  (B) exterior triangles surviving centroid + `IndexedPointInAreaLocator` filtering?

**Verdict (summary)**

| Claim | Corpus reading | Grade |
|---|---|---|
| (A) “Green-dot edge is non-Delaunay” | Local Delaunay **is** empty-circle; violation is a **single** `inCircle_R` test. Under *constraints / conforming*, non-empty-circle edges are **not** automatically a builder bug. Degenerate pins for CDTB exist (JTS#1190 single-triangle). | **AMBER** — check, don’t assume bug |
| (B) “Blue-dot exterior triangles keep Interior centroids” | Ray-parity PIP is proven on convex families and on concrete **concave** rings (hat / Spectre pockets). Centroid is the vertex average and lies in the triangle bbox. Filtering CDTB output by centroid is a **post-process**, not a builder guarantee; failures usually mean invalid/self-touching ring after scale/round, wrong orientation, or visual mis-id of hull pockets. | **AMBER** — method is standard; diagnose inputs |
| Global / covering DT, Steiner-conforming correctness, Voronoi dual | Explicitly out of scope of landed #68 rungs. | **RED** — not yet in corpus |

Overall: the discussion is answerable from the corpus as **spec + diagnostic**, not as “we re-ran your MRE under Rocq.” No new theorems required to draft a reply.

---

## §0 — What the reporter is doing

MRE (NTS.Core **1.15.3**):

1. Scale sites by `1e5`, round to integer coords, `Distinct()`.
2. Close as a `Polygon`, feed **both** `SetSites(polygon)` and `Constraints = polygon` into
   `ConformingDelaunayTriangulationBuilder` (`Tolerance = 0.1`).
3. `GetTriangles` → full triangulation of the **site set** (convex hull of vertices, with
   constrained edges forced / refined).
4. Keep triangles whose **centroid** has `IndexedPointInAreaLocator.Locate == Location.Interior`.

Two visual claims:

- **(A)** One interior edge looks non-Delaunay (green mark).
- **(B)** After the centroid filter, some triangles that look exterior to the concave polygon
  remain (blue marks). Other exterior-removal strategies (edge midpoints, hull-of-polygons)
  allegedly agree.

---

## §1 — Corpus surface for claim (A): what “Delaunay” means here

### 1.1 Empty-circle = local Delaunay (Qed)

| Theorem | File | Meaning |
|---|---|---|
| `triangle_locally_delaunay A B C P ≜ inCircle_R A B C P ≤ 0` | `DelaunayLocallyDelaunay.v` | Shewchuk open-disk legality for CCW △ABC vs opposite vertex P |
| `both_locally_delaunay_iff_single_test` | same | Both sides of the AB-quad reduce to **one** determinant (`inCircle_R_double_swap`) |
| `flip_witness_both_not_locally_delaunay` | same | CCW + opposite sides + `0 < inCircle_R` ⇒ **neither** candidate triangle is locally Delaunay |
| `loc_flip_not_both_locally_delaunay` | same | Rational pin: A=(0,0), B=(2,0), C=(1,1), D=(1,−1/2), `inCircle_R = 3/2 > 0` |
| `delaunay_edge_iff_empty_circumcircle` | `DelaunayEdgeEmptyCircle.v` | Weak-skeleton: edge of a DT ⇔ empty circumcircle certificate (68-a) |
| `in_circle_test_iff_b64_inCircle_exact_pos` | `theories-flocq/DelaunayEmptyCircle.v` | R-side sign ↔ exact `b64_inCircle_exact` for finite binary64 |

**Operational consequence for the green mark.**  To certify “this edge is non-Delaunay,” form the
shared-edge quad (two triangles) and evaluate `inCircle_R` (or the extracted / FFI exact
in-circle). Visual inspection is not the criterion the corpus (or Shewchuk) uses.

### 1.2 Conforming ≠ unconstrained Delaunay

`ConformingDelaunayTriangulationBuilder` is **not** pure unconstrained DT of the vertex set:

- **Constraints** force polygon edges into the mesh (possibly after Steiner insertion in the
  *conforming* sense).
- A constrained edge may be forced even when the opposite vertex lies inside a circumcircle
  of a candidate triangle that would flip it away — that is the difference between
  *constrained / conforming* DT and *unconstrained* DT.
- The corpus proves the **legality predicate** and the **flip criterion**. It does **not**
  prove that JTS/NTS CDTB’s Steiner insertion always restores pure local Delaunay on
  every edge of a general constrained input (global insert / covering DT remain open —
  `TRIAGE_NTS_JTS_ISSUES.md` #68 residue).

So (A) alone is **not** enough to open a “builder is broken” ticket unless the edge is
*unconstrained* (or post-conforming) and still fails the empty-circle test against the
**actual** vertex set (including Steiner points).

### 1.3 Known CDTB degeneracy pin already in-corpus (JTS#1190)

`DelaunayDegeneratePins.v` (claim **68-c**):

- `single_triangle_delaunay`: over its own vertices, a lone triangle has
  `inCircle_R A B C P = 0` for `P ∈ {A,B,C}` — **no** strict empty-circle violation.
- Concrete pin `single_triangle_pin_1190` (right triangle 0–4–4).
- Companion cocircular square pin for JTS#1039 (`cocircular_square_tie_1039`, flip guard
  correctly excludes the 0-tie).

These are the field degeneracies the builder historically mishandles (zero-area extras on
already-Delaunay constraints — see jts#1190). #839’s polygon is **not** that single-triangle
input, but the same builder family and the same legality vocabulary apply.

### 1.4 Claim (A) triage

| Observation | Reading |
|---|---|
| Edge is a **constraint** (original polygon edge or Steiner-refined constraint) | Non-empty-circle may be **expected** until / unless conforming finishes; not pure-DT |
| Edge is **unconstrained**, Steiner set included, and `inCircle_R > 0` with CCW | True local-Delaunay violation → quality bug (aligns with jts#1190 class) |
| Four sites nearly cocircular | Knife-edge tie: exact 0 is legal either way (`cocircular_tie_no_flip_witness`); float noise can flip arbitrarily |

**Grade for (A): AMBER.**  The corpus gives a machine check (`inCircle_R` / `b64_inCircle_exact`),
not a free “yes that green edge is illegal.”

---

## §2 — Corpus surface for claim (B): centroid filter vs concave PIP

### 2.1 What the locator is computing

The corpus model of NTS-style area location is ray-crossing parity:

- `Overlay.point_in_ring` — strict y-straddle half-open vertex rule.
- `JCTParityTransport.point_in_ring_dec` — decidable, total, never both odd and even.
- Gallery: `docs/nts-oracle-gallery.md` (vertex graze, horizontal edge, half-open rectangle).

Guards that pure parity needs for geometric fidelity (proven necessary by RED counterexamples):

| Guard / phenomenon | File / theorem |
|---|---|
| Vertex graze false-negative | `JCT_VertexGrazingCounterexample.v` (`diamond_refutes_parity_seam`) |
| Horizontal edge at query height false-positive | `JCT_HorizontalEdgeCounterexample.v` (`notch_refutes_parity_without_guard`) |
| On-edge half-open skeleton | `JCT_OnEdgeCounterexample.v` (`parity_seam_strict_refuted_on_edge`) |

NTS `IndexedPointInAreaLocator` / `RobustRayCrossingCounter` are the **robust** counterparts;
the gallery exists so implementers can pin those edge cases. A generic-position centroid of a
non-degenerate triangle is almost always off-skeleton, so these degeneracies are secondary for
(B) unless coordinates are pathological after scale/round.

### 2.2 Concave polygons: hull-interior can be *exterior* to the ring

This is the key geometric fact for CDTB + concave filter:

| Theorem | File | Meaning |
|---|---|---|
| `hat_pocket_not_in_ring` | `HatMonotileExterior.v` | Point in reflex notch of the hat monotile: inside **convex hull**, `point_in_ring` **false** (even parity) |
| `spectre_pocket_not_in_ring` | `SpectreConcaveFamily.v` | Same pattern for the Spectre tile |
| `hat_point_in_ring` | `HatMonotileInterior.v` | Interior witness on the same non-convex ring |

So: triangles that live in a **convex-hull pocket** of a concave polygon *must* filter out
if the locator agrees with geometric exterior. If the reporter’s blue-marked triangles are
true hull-pocket triangles and the centroid still reports `Interior`, either the ring after
`Distinct`/scale is not the intended simple polygon, orientation/validity is wrong, or the
triangle is not actually confined to the pocket (see §2.4).

### 2.3 Convex ladder (closed) vs general simple ring (residual)

| Closed | Residual |
|---|---|
| Rectangle / right triangle / general CCW triangle / diamond / hexagon / strict-convex y-unimodal (`ConvexJCT.convex_unimodal_point_in_ring_iff_interior`) | Full unconditional `point_in_ring ↔ geometric_interior_cont` for *arbitrary* simple rings is still the H1 seam residual (`point_in_ring_correct_jct_cont` is **conditional** on `parity_characterises_interior_cont`) |

For **practice** (NTS locator on a simple valid polygon), robust ray-crossing is the industrial
answer; the corpus pins its edge cases and proves the convex families. It does **not** claim a
full formal JCT for every concave production polygon.

### 2.4 Centroid facts (what the filter actually samples)

From `Centroid.v`:

- `centroid3 A B C = ((xA+xB+xC)/3, (yA+yB+yC)/3)`
- `triangle_centroid`
- Axis-aligned bounds: `centroid3_{x,y}_{lb,ub}` — centroid lies in the triangle’s bbox
- Translation / scale equivariance

The centroid of a **non-degenerate** triangle lies in the relative interior of that triangle
(standard affine fact; the corpus pins the average and bbox, not a full barycentric-interior
theorem in `Centroid.v` alone). Therefore:

> Centroid-in-polygon ⇔ triangle-in-polygon  
> **only if** the triangle cannot straddle the polygon boundary.

For a **correct constrained triangulation of a simple polygon**, constrained edges are barriers:
each face is wholly inside or wholly outside. That is an **algorithmic** expectation of CDT,
not a corpus theorem about NTS CDTB. If constraints fail (crossing, collapsed, Steiner mess),
centroid filtering can disagree with “looks exterior.”

### 2.5 API semantics the reporter may be missing

`GetTriangles` on `ConformingDelaunayTriangulationBuilder` returns the triangulation of the
**sites** (hull of vertices), **not** “triangles of the polygonal region.” Interior selection
is always a **post-process**. The builder is doing what it advertises; the concave cut is the
caller’s job (centroid, dual walk across constrained edges, or a constrained triangulator API
that returns faces already labelled).

### 2.6 Claim (B) triage — likely causes (ordered)

1. **Visual “exterior” is still polygon-interior**  
   Long constrained diagonals in a deep bay look “outside” the silhouette but stay inside the
   ring. Centroid correctly stays. (Not a locator bug.)

2. **Hull-pocket triangle whose centroid is truly exterior but reported Interior**  
   Check `polygon.IsValid`, orientation (`IsCCW`), and that `Distinct()` + integer snap did not
   introduce self-intersections / collapsed edges. Corpus: concave pockets *should* be even
   parity (`hat_pocket_not_in_ring` pattern).

3. **Tolerance / Steiner / scale mismatch**  
   `SCALE = 1e5` + `Tolerance = 0.1` + `PrecisionModel.MaximumPreciseValue` is a mixed regime;
   sites can merge near tolerance while constraints still reference snapped rings.

4. **Old stack**  
   NTS.Core **1.15.3** is far behind current 2.x ports of JTS triangulation fixes. jts#1190
   remains open as `type-question` but the class of CDTB surprises is documented.

5. **Filter predicate too strict / too loose**  
   `== Location.Interior` drops boundary centroids; for skinny triangles near edges prefer
   `!= Location.Exterior` or a slightly shrunk probe. On-edge RED (`parity_seam_strict_refuted_on_edge`)
   shows half-open conventions disagree on the skeleton.

**Grade for (B): AMBER.**  Method is standard; corpus explains *why* hull pockets exist and
what parity must say about them. It does not re-execute the MRE.

---

## §3 — Answer draft (for posting on discussion #839)

> **Short version.**  Two separate issues are mixed in this thread: (1) what “Delaunay” means
> under a *conforming / constrained* builder, and (2) filtering the hull triangulation down to
> a *concave* polygon.
>
> **(1) Non-Delaunay-looking edges.**  
> Local Delaunay legality is the empty-circle test: for a CCW triangle ABC and opposite vertex
> P, the edge is illegal iff the oriented in-circle determinant is strictly positive
> (Shewchuk / Guibas–Stolfi). That criterion is formalised and Qed-closed in the
> NetTopologySuite.Proofs corpus (`triangle_locally_delaunay`, `flip_witness_both_not_locally_delaunay`,
> `delaunay_edge_iff_empty_circumcircle`; exact binary64 bridge via `b64_inCircle_exact`).  
> **Important:** `ConformingDelaunayTriangulationBuilder` is not unconstrained DT. Constrained
> polygon edges are forced into the mesh; they can look “non-Delaunay” relative to a pure flip
> criterion until (and unless) Steiner conforming finishes. A green mark on a **constraint**
> edge is not by itself evidence of a bug. To file a defect, show an **unconstrained** edge
> (or post-conforming mesh) with a strict empty-circle violation against the **full** vertex
> set including Steiner points. Degenerate CDTB behaviour on already-Delaunay constraints is
> tracked upstream as [jts#1190](https://github.com/locationtech/jts/issues/1190); the corpus
> pins the single-triangle “must stay Delaunay / zero violation” algebra as
> `single_triangle_delaunay`.
>
> **(2) Exterior triangles after centroid filtering.**  
> `GetTriangles` triangulates the **sites’ convex hull** with constraints; it does not return
> “triangles of the polygonal face.” Filtering by
> `IndexedPointInAreaLocator.Locate(centroid) == Interior` is the usual post-process.  
> For a **concave** polygon, many hull triangles sit in reflex **pockets**: inside the convex
> hull, outside the polygon. Machine-checked concave examples in the proofs corpus
> (`hat_pocket_not_in_ring`, `spectre_pocket_not_in_ring`) show exactly that pattern —
> ray-parity / PIP must report exterior there. If a true pocket triangle’s centroid still
> reports Interior, first check `IsValid` / orientation after `Scale+Round+Distinct`, and
> whether the triangle actually straddles a broken constraint. Also try
> `Locate != Exterior` (boundary-tolerant) and a current NTS 2.x build — 1.15.3 is old.  
> Ray-crossing edge cases the robust locator must get right (vertex graze, horizontal edge at
> query height, half-open boundary) are documented with WKT vectors in
> https://github.com/MerkatorBV/NetTopologySuite.Proofs/blob/main/docs/nts-oracle-gallery.md
>
> **Practical suggestions.**  
> - Verify legality with an explicit in-circle test on the quad (don’t rely on the screenshot).  
> - Prefer constrained dual walk: triangles separated from the seed interior face by a
>   *constraint* edge are exterior (more stable than centroid when Steiner points are dense).  
> - Ensure the ring is simple and CCW after integer snap.  
> - Upgrade off 1.15.3 if possible; re-check against current JTS/NTS CDTB.

---

## §4 — What this scout does *not* claim

- No Rocq re-execution of the 23-vertex MRE (coordinates stay C# / NTS-side).
- No proof that NTS CDTB is globally correct or that Steiner insertion terminates with a pure DT.
- No discharge of the general polygonal JCT residual for arbitrary concave rings.
- No endorsement that `Tolerance = 0.1` at scale `1e5` is a sound merge policy.

---

## §5 — Follow-ups (if Joost / #68 track wants more)

| Priority | Work item | Size |
|---|---|---|
| Low | Add discussion #839 to `TRIAGE_NTS_JTS_ISSUES.md` wire map under #68 / `mesh` | 5 min edit |
| Medium | Extract / pin an `INCIRCLE_SIGN` oracle vector from the reporter’s green-dot quad once coordinates of the four vertices are recovered | 1 session |
| Medium | Document “CDTB + concave filter” recipe next to `nts-oracle-gallery.md` (centroid vs dual-walk) | 1 short doc |
| Large | Global covering DT + conforming insert correctness (named #68 residue) | multi-session / thesis-scale |

---

## §6 — Files grepped / read

- `theories/DelaunayLocallyDelaunay.v`, `DelaunayEdgeEmptyCircle.v`, `DelaunayDegeneratePins.v`,
  `DelaunayFlipWitness.v`, `DelaunayFlipGeometric.v`
- `theories-flocq/DelaunayEmptyCircle.v`
- `theories/Centroid.v`, `PointInRingCorrect.v`, `JCT.v` (headers / headlines)
- `theories/HatMonotileExterior.v` / interior + Spectre concave family (via `verified-claims.md`)
- `docs/nts-oracle-gallery.md`, `docs/verified-claims.md` (68-a/b/c + PIP rows),
  `TRIAGE_NTS_JTS_ISSUES.md` (#68, jts#1190)
- Upstream: NTS discussion #839 body; jts#1190 title/labels

**Scout time**: ~1.5 h inventory + analysis.
**AI assistance**: Grok (grok-4.5), human-directed.
**License note**: this note is project documentation (BSD-3-Clause corpus).

---

## §7 — Empirical re-run (2026-08-05) via NTS 2.6.0 + Rocq `INCIRCLE_SIGN`

Harness: `tests/Discussion839Mre/` (replays the discussion MRE, then checks every
internal edge with the proofs-repo oracle kernel).

| Ingredient | Value |
|---|---|
| NTS package | **2.6.0** (assembly reports `2.0.0.0`) |
| Rocq kernel | `oracle_bin` `INCIRCLE_SIGN` → extracted `b64_inCircle` (**same code** as Phase 5 FFI `nts_rocq_in_circle`; in-process `libntsrocq` not loaded on this host — WSL protocol path) |
| Oracle pin | A=(0,0),B=(2,0),C=(1,1),D=(1,−½) → **POS 1.5** (matches `loc_in_circle_test_D`) |
| Sites | discussion #839 ring, `SCALE=1e5` + round, `Tolerance=0.1` (also re-run `--no-scale` and `--tol0`: **same counts**) |

### Results

| Metric | Value |
|---|---|
| `Polygon.IsValid` | **True** |
| Shell CCW | **False** (CW shell; area still positive) |
| Total triangles | **34** |
| Centroid `Interior` / `Exterior` / `Boundary` | **22 / 12 / 0** |
| `polygon.Contains` / `Covers` centroid | 22 / 22 |
| Interior-centroid triangles **not** `Covers(t)` | **0** (no straddlers) |
| Internal edges checked | **45** |
| Strict empty-circle violations (`inCircle > 0`) | **0** (unconstrained: 0) |

### Empirical verdict (modern NTS)

- **(A) Non-Delaunay claim does not reproduce** on NTS 2.6.0 for this input: every
  internal edge is locally Delaunay under the corpus empty-circle criterion
  (oracle-checked). Steiner points appear (non-integer vertices after scale).
- **(B) Exterior filter works**: 12 hull-pocket triangles correctly get
  `Location.Exterior` and are dropped; the 22 kept triangles are fully covered by
  the polygon. The reporter’s “blue exterior triangles kept” behaviour is **not**
  seen on 2.6.0 with this MRE.

### Implications for the discussion reply

1. Ask the reporter to re-run on **current NTS 2.x** (they used **1.15.3**).
2. Offer the empty-circle check protocol (`INCIRCLE_SIGN` / `nts_rocq_in_circle`)
   so any remaining green-dot edge can be certified, not eyeballed.
3. If 1.15.3 still mis-filters, treat as a **version-specific** CDTB / locator
   regression relative to 2.6.0, not as a general geometric impossibility
   (the corpus + this re-run show the method is sound on the modern stack).

Run:

```text
dotnet run --project tests/Discussion839Mre -c Release
# optional: -- --no-scale | --tol0 | --verbose
# oracle: WSL_ORACLE_BIN=/path/to/oracle_bin  or  ORACLE_BIN=C:\...\oracle_bin.exe
```
