# `depth_region`: completing the guard set — the vertex-graze case

**Coq artifact:** [`theories/BufferDepthVertexGrazeCounterexample.v`](../theories/BufferDepthVertexGrazeCounterexample.v)
(Qed-closed; no `Admitted` / `Axiom` / `Parameter`; axiom footprint =
the standard classical-reals pair on the allowlist).

**Seam touched:** `depth_region` in [`theories/BufferDepth.v`](../theories/BufferDepth.v).

---

## TL;DR

The third and final guard for `depth_region`. #91 (open-spur) showed it needs a
**closed** kept boundary; #93 (horizontal-edge) showed closure is not
sufficient, it also needs `no_horizontal_edge_at`. This file adds
`ray_avoids_vertices`, mirroring the JCT parity seam (#85): a closed,
horizontal-edge-free kept boundary is *still* misclassified when the rightward
ray grazes a vertex.

## The witness

Reuse the merged #85 convex **diamond** (vertices `(0,1),(1,0),(0,-1),(-1,0)`)
as the kept boundary of `G_diamond`. Since the labels are kept and listed in the
diamond's vertex order, `edges_of (kept_edges G_diamond) = ring_edges diamond`
(`Gdiamond_kept_is_diamond`) — a closed boundary with **no horizontal edge** —
so `depth_region G_diamond p ↔ point_in_ring p diamond`, and the #85 verdicts
transfer.

## RED — closed + horizontal-edge-free still misclassifies

```coq
Theorem depth_region_vertex_not_invariant :
  ~ (forall a b, connected_in_complement_cont diamond a b ->
       (depth_region G_diamond a <-> depth_region G_diamond b)).
```

`A = (0, 1/2)` gets `depth_region` **true** (ray crosses one edge); `B = (0,0)`
gets **false** (ray grazes vertex `(1,0)`; the strict y-straddle counts neither
incident edge). `A` and `B` are joined by the off-boundary segment `x = 0`
(`diamond_segment_off_ring`, #85), so `depth_region G_diamond` is not constant on
a complement component — not a sound enclosure predicate. Neither #91 (it's
closed) nor #93 (no horizontal edge) excludes this; the defect is the vertex
graze.

## GREEN — a ray-avoids-vertices guard excludes it

```coq
Definition depth_region_vertex_guarded (G : TopologyGraph) (r : Ring) (p : Point) : Prop :=
  edges_of (kept_edges G) = ring_edges r ->
  ray_avoids_vertices p r ->
  depth_region G p.

Theorem Gdiamond_excluded_by_ray_avoids_guard :
  depth_region_vertex_guarded G_diamond diamond B.   (* vacuous: B's ray grazes (1,0) *)
```

### RGR status

| phase | content | status |
|---|---|---|
| **RED**   | a closed, horizontal-edge-free kept boundary misclassifies at a vertex graze (`depth_region_vertex_not_invariant`) | Qed |
| **GREEN** | a `ray_avoids_vertices` guard on the kept boundary excludes the witness (`Gdiamond_excluded_by_ray_avoids_guard`) | Qed |
| **REFACTOR** | thread the full guard set through `depth_region_is_buffer` / `buffer_H_bridge_factor` | follow-up |

## The complete `depth_region` guard set (#91 + #93 + this)

| guard | role | shown by |
|---|---|---|
| closed kept boundary (even kept-degree) | necessary | #91 (open spur) |
| `no_horizontal_edge_at` on the kept boundary | necessary on top of closure | #93 (horizontal edge) |
| `ray_avoids_vertices` on the kept boundary | necessary on top of the above | this file (vertex graze) |

This is exactly `point_in_ring`'s guard set — `depth_region` is the same
ray-parity primitive and needs the same preconditions to be a sound enclosure
test.

## Registry note

No `admitted-counterexamples.txt` entry: the file has no `Admitted`; this is a
Qed-closed scope finding about the definition `depth_region`.
