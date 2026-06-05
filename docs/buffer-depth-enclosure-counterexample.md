# The open-spur counterexample: `depth_region` needs a closed-boundary guard

**Coq artifact:** [`theories/BufferDepthEnclosureCounterexample.v`](../theories/BufferDepthEnclosureCounterexample.v)
(Qed-closed; no `Admitted` / `Axiom` / `Parameter`; axiom footprint =
the standard classical-reals pair on the allowlist).

**Seam touched:** `depth_region` in [`theories/BufferDepth.v`](../theories/BufferDepth.v).

---

## TL;DR

`BufferDepth.v` defines the buffer interior as the crossing-number interior of
the kept boundary edges:

```coq
depth_region G p := ray_parity_odd p (edges_of (kept_edges G)).
```

`kept_edges G` is `filter (xor in_left in_right) (tg_edges G)` — an arbitrary
sublist of the graph's edges. **Nothing constrains those edges to form a closed
boundary.** But ray-crossing parity is only a meaningful enclosure test for a
closed boundary; for an open edge set it is not even constant on a connected
component of the complement, so it cannot equal any region.

This is the same family of gap as the JCT parity-seam findings (#84–#87) — and
the same shared primitive, `ray_parity_odd`.

## The witness

The smallest open boundary: a single kept edge ("spur") from `(0,0)` to `(0,2)`.

```coq
Definition spur : TopologyGraph :=
  {| tg_vertices := [mkPoint 0 0; mkPoint 0 2];
     tg_edges    := [ (mkPoint 0 0, mkPoint 0 2,
                       {| in_left := true; in_right := false |}) ] |}.
```

Its kept-edge list is exactly `ring_edges` of the degenerate two-vertex "ring"
`spur_ring = [(0,0); (0,2)]` (`spur_kept_is_open_ring`) — an open segment, not a
closed loop.

## The disagreement (RED)

The complement of a single segment is path-connected, yet the rightward-ray
parity differs across it:

| point | ray vs the segment | `depth_region` |
|---|---|---|
| `p1 = (-1, 1)` | crosses (`y=1 ∈ (0,2)`) | **true** ("inside") |
| `p2 = (-1, 3)` | misses (`y=3 ∉ (0,2)`) | **false** ("outside") |

and `p1`, `p2` are joined by the off-boundary vertical path `x = -1`
(`spur_p1_p2_connected`). A sound enclosure predicate is constant on each
complement component (as `geometric_interior_cont` is, `JCT.v`); `depth_region
spur` is not:

```coq
Theorem spur_depth_not_component_invariant :
  ~ (forall a b, connected_in_complement_cont spur_ring a b ->
       (depth_region spur a <-> depth_region spur b)).
```

So `depth_region` is not a sound enclosure predicate without a closure guard.

## The fix (GREEN)

The kept boundary of the spur is the ring `spur_ring`, which is **not**
`ring_closed` (`spur_ring_not_closed`) and has fewer than four vertices. A
`depth_region` guarded by closure of its kept boundary excludes the witness
vacuously:

```coq
Definition depth_region_closed_guarded (G : TopologyGraph) (r : Ring) (p : Point) : Prop :=
  edges_of (kept_edges G) = ring_edges r ->
  ring_closed r -> ring_has_minimum_points r ->
  depth_region G p.

Theorem spur_excluded_by_closure_guard :
  forall p, depth_region_closed_guarded spur spur_ring p.   (* vacuous: spur_ring not closed *)
```

The proper *general* guard is "every vertex is incident to an even number of
kept edges" — the boundary decomposes into closed cycles. For the single-edge
witness this collapses to "the kept boundary is a closed ring", which is what is
formalised here.

### RGR status

| phase | content | status |
|---|---|---|
| **RED**   | `depth_region spur` is not a complement-component invariant (`spur_depth_not_component_invariant`) | Qed |
| **GREEN** | a closure-guarded depth predicate excludes the spur (`spur_excluded_by_closure_guard`) | Qed |
| **REFACTOR** | thread a `kept_boundary_closed` (even kept-degree) premise through `depth_region_is_buffer` / the H_bridge factorisation | follow-up |

## Registry note

No `admitted-counterexamples.txt` entry: the file has no `Admitted`; this is a
Qed-closed scope finding about the definition `depth_region`.
