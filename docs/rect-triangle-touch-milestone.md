# Milestone: Rect + Triangle Touch / Pointset / Relate (S15l)

**Status:** Skeleton + helpers + EE cell + prepared wrappers + honest DEFERRED registry entries (2026-06-21). Full capstone cells + regime decision remain work in progress (registered).

## What landed
- Full triangle representation + dispatch skeleton in RelateNG (triangle_geometry_*, point_in_triangle, tris_relate, relate_on_triangles_dispatches).
- TrianglePairRegime + fill (TPR_* + reuse of aa_* matrices) in RelateMatrixTriangle.v.
- Touch helpers (triangles_touch_on_shared_edge via shares + opposite_sides/cross, touch_triangle_bb_point + between).
- Strict II no-common (`touch_triangle_pair_strict_ii_no_common` using gtri_pos_iff + shared edge sign flip).
- Cell lemmas:
  - `touch_triangle_pair_ii_cell` (None for SInt/SInt via point_set disjoint under named H_ii; 0<gtri form unconditional; lift deferred)
  - `touch_triangle_pair_bb_cell` (Some 1 for SBnd/SBnd via shared bnd point)
  - `touch_triangle_pair_ee_cell` (Some 2 for SExt/SExt via two_geometries_exterior_meet)
- Capstone: `touch_triangles_satisfy_pointset` (and `_and_general`) assembling the provable cells.
- Honest notes everywhere on:
  - Strict interior for II (boundary points assigned to BB cell — half-open philosophy mirroring rect).
  - Trimmed F cells and full 9-cell geom_de9im_pointset DEFERRED (bnd inclusion in point_set).
  - DEFERRED: arbitrary polygon composition (target #68).
- Prepared extension: `pg_tri_cache`, `prepare` populates it, `prepared_triangle_*` agrees + cached touch example.
- Concrete examples (`ex_triangles_touch_on_shared_edge`, `touch_triangles_satisfy_pointset_ex`, relate under touch).
- Claims + triage refresh (new rows, "triangle touch capstone landed", #68 pointer).

### Concrete example (shared-edge touch)
```coq
(* Two triangles sharing the interior of edge (1,0)--(0,1).
   Third points (0,0) and (1,1) lie on opposite sides of the shared line
   (cross-product sign flip). Their strict interiors are disjoint (0 < gtri
   cannot hold for both), the shared edge interior point is in both boundaries
   (BB), and exteriors meet (EE). *)
Example tri_touch_shared_edge :
  triangles_touch_on_shared_edge
    (mkPoint 0 0) (mkPoint 1 0) (mkPoint 0 1)
    (mkPoint 1 0) (mkPoint 1 1) (mkPoint 0 1).
(* Satisfies the trimmed pointset: ~exists p, 0<gtriA p /\ 0<gtriB p  (strict II)
   + BB cell + EE cell. *)
```

A simple ASCII sketch:
```
      C=(0,1)               B'=(1,1)
       / \                   / \
      /   \                 /   \
A=(0,0)--B=(1,0)     B=(1,0)--C'=(0,1)
      \   /                 \   /
       \ /                   \ /
      A'=(0,0) wait no: left tri A(0,0) B(1,0) C(0,1); right B(1,0) B'(1,1) C(0,1)
Shared edge B--C ; opposite thirds A and B'.
```

## Reuse & style
- Heavy reuse of gtri/gtri_pos_iff, point_set/point_on_boundary, cell_ok, two_geometries_exterior_meet, between, cross, ring_edges.
- 3-axiom, Qed on primary paths and all using sites + examples.
- Transparent DEFERRED notes + trim to provable cells only.

## Forward
This + the rect touch work gives a solid rect+triangle building block.

Opens the door to:
- Vertex-touch variant
- Overlap/Contains regimes for tris
- Pairwise composition lemmas (see deferred entries in admitted-deferred-proofs.txt linked to #68)
- Delaunay (#68) — empty circumcircle <=> local relate matrices on adjacent triangles.

See:
- theories/RelateNG.v (touch section)
- theories/RelatePrepared.v (tri cache)
- docs/issue-67-relateng-triage.md + verified-claims.md
- docs/rect-triangle-touch-milestone.md (this file)

Next options on the table: consumption XUnit sketch, #64 arc momentum, #66 overlay gaps, or composition lemmas.

**Author note:** Beautiful clean slice. Strict II + BB hand-off is the right model.
