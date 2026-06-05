# BufferDepth REFACTOR: the guarded depth-region predicate

**Coq artifact:** [`theories/BufferDepthGuarded.v`](../theories/BufferDepthGuarded.v)
(Qed-closed; no `Admitted` / `Axiom` / `Parameter`; axiom footprint =
the standard classical-reals trio on the allowlist).

**Seam touched:** `depth_region` / `depth_region_is_buffer` / the H_bridge
factorisation in [`theories/BufferDepth.v`](../theories/BufferDepth.v).

---

## What this does

The BufferDepth enclosure counterexamples pinned the guards `depth_region`
needs (each Qed-closed RED/GREEN):

| guard | counterexample |
|---|---|
| closed kept boundary | #91 (open spur) |
| `no_horizontal_edge_at` | #93 (horizontal edge) |
| `ray_avoids_vertices` | #95 (vertex graze) |

This REFACTOR folds them into one predicate and re-points the depth seams onto
it — **additively** (the existing `BufferDepth` theorems are untouched).

```coq
Definition kept_boundary_wellformed (G : TopologyGraph) (r : Ring) (p : Point) : Prop :=
  edges_of (kept_edges G) = ring_edges r /\
  ring_simple r /\ ring_closed r /\ ring_has_minimum_points r /\
  no_horizontal_edge_at p r /\ ray_avoids_vertices p r.
```

## The headline: depth = geometric interior, modulo the JCT seam

`depth_region` is the same ray-parity primitive as `point_in_ring`, so for a
well-formed kept boundary it reduces to it (`depth_region_eq_point_in_ring`), and
then to the continuous geometric interior **under the named JCT seam**:

```coq
Theorem depth_region_is_geometric_interior_guarded :
  forall G r p,
    kept_boundary_wellformed G r p ->
    parity_characterises_interior_cont_strict p r ->   (* the JCT seam, JCT.v *)
    (depth_region G p <-> geometric_interior_cont p r).
```

This is the depth-labelling analogue of `JCT.point_in_ring_correct_jct_cont`: it
shows buffer depth labelling reduces to the **same single remaining seam** as the
point-in-ring correctness, not a new one.

## Re-pointed H_bridge

```coq
Definition depth_region_is_buffer_guarded (G : TopologyGraph) (g : Geometry) (d : R) (r : Ring) : Prop :=
  forall p, kept_boundary_wellformed G r p -> (depth_region G p <-> buffer_spec g d p).

Theorem buffer_H_bridge_factor_guarded : ...   (* composes extract_realizes_depth with the guarded seam *)
Theorem buffer_correct_via_depth_guarded : ... (* end-to-end capstone over the guarded seam *)
```

The unguarded `depth_region_is_buffer` is refuted by the #91/#93/#95 witnesses;
the guarded form is its dischargeable scope, so correctness uses should carry the
guard.

## Scope note — what is *not* proved

The proposed `depth_region_guarded_component_invariant` ("ray-parity is constant
on a complement component for a closed ring") is **not** provable here: it *is*
the winding-number / JCT theorem — the same thesis-scale gap
`parity_characterises_interior_cont_strict` names. This file routes the bridge
**through** that named seam rather than re-proving it; nothing here discharges
the JCT.

### RGR status (BufferDepth loop)

| phase | content | status |
|---|---|---|
| RED/GREEN | `depth_region` guard set (closed + no-horizontal + ray-avoids) | #91 / #93 / #95, merged |
| **REFACTOR** | `kept_boundary_wellformed`, the depth/interior bridge, the guarded H_bridge | this file, Qed |

## Registry note

No `admitted-counterexamples.txt` entry: the file has no `Admitted`. The
remaining content is the named `Prop` seam `parity_characterises_interior_cont_strict`
(JCT.v), carried as a hypothesis, exactly as elsewhere in the JCT work.
