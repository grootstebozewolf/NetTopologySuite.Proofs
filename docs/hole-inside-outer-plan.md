# Closing `hole_inside_outer` — honest, grounded, multi-beachhead plan

> **Status: PLAN.** No proof attempted in this document. Every primitive,
> theorem, and file named below was **verified to exist** (and its `Qed`/
> conditional status checked) against `main` before writing — no invented
> lemmas. This plan supersedes earlier route sketches that referenced
> non-existent machinery (`RayParity` module, `tangent_test`,
> `no_tangent_crossing`, `leftmost_vertex`, `ray_parity_odd ... = true`).

## 0. The obligation, grounded

```coq
(* Overlay.v *)
hole_inside_outer outer hole := exists p, In p hole /\ point_in_ring p outer.
point_in_ring p r            := ray_parity_odd p (ring_edges r).   (* inductive Prop *)
```

The combinatorial assembler (R5 slices 1–3f, on `main`) already discharges every
`valid_polygon` condition **except** `hole_inside_outer`
(`FacePolygonHoles.face_polygon_holes_valid` takes it as its sole hypothesis).
So the entire remaining gap for `extract_rings_valid` is: **establish
`point_in_ring p outer` for a hole vertex `p`.**

This is a *ray-crossing parity* fact. Tying it to actual containment is the
Jordan-curve content. The corpus is **not** empty here — it has several JCT
beachheads, each built on the shared IVT separation engine
(`SeparationField.separation_via_field`).

## 1. The beachheads that exist (verified)

| beachhead | file | key result | status |
|---|---|---|---|
| **Rectangle** | `RectangleJCT.v` + `RectangleSeparation.v` | `rect_parity_characterises_interior_open` (parity ⟺ interior, modulo `rect_confines`) **and** `rect_confines_of_interior` (discharges it via IVT) | **unconditional, Qed** |
| **Convex (half-planes)** | `Convex.v`, `ConvexField.v` | `convex_separation` (`in_bounded_component_cont` from a convex `conv_min` field + radius bound) | separation **Qed**; JCT assembly TODO |
| **Triangle** | `RightTriangleSeparation.v`, `GeneralTriangleSeparation.v` | triangle separation via IVT (`separation_via_field`) | separation **Qed**; JCT assembly TODO |
| **Continuous-JCT seam** | `JCT.v`, `JordanCurveSeam.v` | `point_in_ring_correct_jct_cont` (parity ⟺ `geometric_interior_cont`, modulo named JCT hypothesis); topological lemmas `no_path_from_interior_to_exterior`, `interior_component_bounded`, `far_point_not_interior` | conditional **Qed** + scaffolding |
| **Conditional bridge** | `PointInRingTangents.v` | `point_in_ring_correct_jct` (parity ⟺ `geometric_interior_stdlib`, modulo named hypotheses) | conditional **Qed** |

The rectangle chain closes outright:
`x0<px p<x1 ∧ y0<py p<y1` → `rect_confines_of_interior` → `rect_confines` →
`rect_open_box_geometric_interior_of_confines` → `geometric_interior_cont` →
`rect_parity_characterises_interior_open` (←) → **`point_in_ring p (rect_ring …)`**,
unconditionally.

## 1b. Beachhead status at a glance

| stage | scope | effort | status |
|---|---|---|---|
| A — conditional headline | full `extract_rings_valid`, modulo named JCT hyp | ~1 slice | **LANDED** (`ExtractFacePolygonJCT.face_polygon_valid_via_jct`) |
| B — rectangle (unconditional) | `hole_inside_outer`, rectangular outer | ~1 slice | **LANDED** (`HoleInsideOuterRect.hole_inside_outer_rect`) — unconditional for all axis-aligned rectangles |
| C — convex (unconditional) | `hole_inside_outer`, convex outer | medium | **opened** — concrete diamond instance landed (`HoleInsideOuterConvexExample`); separation **Qed**; GENERAL parity characterisation (convex-chain monotonicity) still TODO |
| D — triangle (unconditional) | `hole_inside_outer`, triangular outer | medium | separation **Qed** (`Right/GeneralTriangleSeparation`); assembly TODO |
| E — general simple-polygon JCT | unconditional, any simple ring | research | **open residual** — registered H1/JCT gap; topological scaffolding only |
| F — shape recognition + `extract` rewire | apply B/C/D per face; redefine `extract` | structural | not started |

## 2. Staged plan (cheapest/most-certain first)

### Stage A — Conditional headline (plumbing) — *high confidence, ~1 slice*

Wire `FacePolygonHoles.face_polygon_holes_valid` to `JCT.point_in_ring_correct_jct_cont`,
producing a conditional `extract_rings_valid`-shaped theorem for face polygons that
takes the JCT characterization (`parity_characterises_interior_cont_strict`) +
side conditions (`no_horizontal_edge_at`, `ray_avoids_vertices`) as **named
hypotheses**. This matches the corpus's accepted `overlay_ng_correct_conditional`
/ `point_in_ring_correct_jct` pattern and lands the headline honestly in
conditional form. Pure composition; no new geometry.

### Stage B — Rectangle `hole_inside_outer`, UNCONDITIONAL — *high confidence, ~1 slice*

Generalise the concrete witness (`HoleInsideOuterExample.v`, the fixed 4×4 square)
to **all** rectangles:

```coq
Lemma point_in_ring_rect_strict :        (* chain of §1, all pieces Qed *)
  x0 < x1 -> y0 < y1 -> x0 < px p < x1 -> y0 < py p < y1 ->
  point_in_ring p (rect_ring x0 y0 x1 y1).
Theorem hole_inside_outer_rect :         (* a hole vertex strictly inside a rect outer *)
  ... -> hole_inside_outer (rect_ring x0 y0 x1 y1) hole.
```

This is a *genuinely unconditional* closure of the analytic seam for the
rectangular-outer case — the first real (non-toy) discharge of `hole_inside_outer`.

### Stage C — Convex `hole_inside_outer` — *medium, few slices*

Assemble the convex JCT on top of `ConvexField.convex_separation`, mirroring the
rectangle assembly: (i) the edge skeleton of a CCW convex ring is the boundary of
its half-plane intersection (so a complement point has `conv_min ≠ 0`); (ii)
strict interior ⇒ `0 < conv_min` ⇒ `in_bounded_component_cont` (separation) ⇒
`geometric_interior_cont`; (iii) parity ⟺ interior for convex rings ⇒
`point_in_ring`. Yields `hole_inside_outer` for convex outer faces. Reuses
`Convex.half_plane`, `conv_min`, and the IVT engine.

### Stage D — Triangle (parallel stepping stone) — *medium*

`RightTriangleSeparation` / `GeneralTriangleSeparation` already give the
separation; assemble the triangle JCT exactly as in the rectangle case. Subsumed
by Stage C once convex is general, but a smaller concrete rung if C is deferred.

### Stage E — General simple-polygon JCT — *research-grade, stays the residual*

`parity_characterises_interior_cont_strict` *unconditionally* for an arbitrary
simple ring is the registered H1/JCT gap. `JCT.v` has the topological scaffolding
(`no_path_from_interior_to_exterior`, `interior_component_bounded`,
`far_point_not_interior`); the general parity characterisation is the open work.
**This stays deferred / conditional** — it is not closeable by a quick slice, and
no plan here pretends otherwise.

### Stage F — Shape recognition + `extract` rewire (structural)

To *apply* B/C/D to a DCEL-extracted face, the abstract face ring
(`ring_of_chain (face_chain …)`) must be matched to a `rect_ring` / convex shape
(a normalization/recognition step), and `extract` must be redefined to emit these
face polygons. For general (non-convex) faces this routes through Stage E's named
hypothesis. Structural; depends on the real pipeline types.

## 3. Honest coverage summary

- **Unconditional, now reachable:** `hole_inside_outer` for **rectangular** outer
  faces (Stage B), and **convex** with moderate work (Stage C). These cover a
  real class of inputs (boxes, convex overlays/buffers) outright.
- **Conditional, now reachable:** the full `extract_rings_valid` headline modulo a
  *named* JCT hypothesis (Stage A) — the corpus-standard honest form.
- **Genuinely open:** the unconditional general-simple-polygon JCT (Stage E) — the
  long-standing H1 residual. Everything else is built; this is the one hard rung.

## 4. Recommended order

**A then B** — both ~1 slice, high confidence, and together they (i) land the
headline conditionally and (ii) close the analytic seam unconditionally for the
rectangle class. Then **C** (convex) widens the unconditional class. **E** is the
research residual and should get its own deliberate effort, not a rushed slice.

---

## Stage B wired into valid_polygon assembly (2026-06-13, `theories/JCTNesting.v`)

`valid_polygon_rect_outer`: a polygon with a rectangular outer ring and holes
(each a well-formed ring with at least one vertex inside the box) is
`valid_polygon` unconditionally, reusing the Stage-B witness
`HoleInsideOuterRect.hole_inside_outer_rect` through
`FacePolygonHoles.polygon_valid_of_rings`. This makes the `hole_inside_outer`
nesting obligation carried by the conditional `extract_rings_valid` /
`extract_rings_valid_holes` (theories-flocq/OverlayBridge.v) dischargeable for
box outers with no JCT seam. Also proves the previously-missing
`rect_ring_simple` (an axis-aligned rectangle is a simple ring).

The general arbitrary-simple-ring parity theorem (Stage E,
`parity_characterises_interior_cont` for `ring_simple`) remains the thesis-scale
gap. See #188 and `EdgeConnectivity.v` §5 for the remaining named fact.

---

## Stage C — second convex instance: hexagon (2026-06-13, `theories/HexagonNesting.v`)

A concrete convex HEXAGON now joins the diamond as a Stage-C witness:
`hex_point_in_ring` (`point_in_ring (2,1)` of a convex integer-coordinate
6-gon, by ray-parity edge enumeration — one slanted edge crossed, odd),
`hex_ring_simple`, `hole_inside_outer_hexagon`, and the capstone
`valid_polygon_hexagon_with_hole` (via `FacePolygonHoles.polygon_valid_of_rings`).
Unconditional, no named hypothesis. The general convex-n-gon parity still
awaits the convex-chain monotonicity lemma (a rightward ray from an interior
point crosses exactly one of n arbitrary slanted edges); the conditional
general-convex assembly (`ConvexOffringSeam.convex_parity_seam_offring_of`)
remains the route once that lemma lands.

---

## General convex, guarded (2026-06-13, `theories/ConvexNesting.v`)

`hole_inside_outer_convex_guarded` packages the general convex case: a hole
with a vertex strictly inside a convex outer (`0 < conv_min hps`, general
position) nests inside, conditional on the single named residual
`convex_interior_parity` — the convex-chain monotonicity (a rightward ray from
a strictly-interior point crosses an odd number of edges), which is exactly the
interior-parity obligation `ConvexOffringSeam.convex_parity_seam_offring_of`
leaves open. Concrete convex families (rectangle, triangle; and the explicit
diamond/hexagon point witnesses) discharge it directly; the general n-gon
monotonicity remains the one open lemma.
