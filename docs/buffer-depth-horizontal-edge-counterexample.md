# `depth_region`: closure is necessary but not sufficient — the horizontal-edge case

**Coq artifact:** [`theories/BufferDepthHorizontalEdgeCounterexample.v`](../theories/BufferDepthHorizontalEdgeCounterexample.v)
(Qed-closed; no `Admitted` / `Axiom` / `Parameter`; axiom footprint =
the standard classical-reals pair on the allowlist).

**Seam touched:** `depth_region` in [`theories/BufferDepth.v`](../theories/BufferDepth.v).

---

## TL;DR

The open-spur counterexample
([`docs/buffer-depth-enclosure-counterexample.md`](buffer-depth-enclosure-counterexample.md),
#91) showed `depth_region` needs its kept edges to form a **closed** boundary.
This file shows closure alone is **not sufficient**: a *closed* kept boundary
with a horizontal edge at the ray height is still misclassified. `depth_region`
needs the **same generic-position guards as `point_in_ring`** — exactly the JCT
parity-seam story (#86), transferred into the depth-labelling pipeline.

## The witness

Reuse the merged #86 **notch** (a valid simple polygon with a horizontal edge
at `y = 1`) as the kept boundary of a graph:

```coq
Definition G_notch : TopologyGraph :=
  {| tg_vertices := [(0,0);(4,0);(4,2);(2,2);(2,1);(0,1)];
     tg_edges    := [ each consecutive notch edge, label {in_left:=true; in_right:=false} ] |}.
```

Because the labels are all kept (`xor true false = true`) and listed in the
notch's vertex order, `edges_of (kept_edges G_notch) = ring_edges notch`
(`Gnotch_kept_is_notch`) — a **closed** boundary, so this is not the open-spur
gap of #91. Hence `depth_region G_notch p ↔ point_in_ring p notch`
(`Gnotch_depth_is_point_in_ring`), and the #86 verdicts transfer verbatim.

## RED — a closed boundary still misclassifies

```coq
Theorem depth_region_horizontal_refutes :
  depth_region G_notch pext /\ ~ geometric_interior_cont pext notch.
```

For the exterior point `pext = (-1,1)`, the rightward ray runs *along* the
horizontal kept edge `(2,1)→(0,1)`; the strict y-straddle misses the genuine
left crossing and counts only the far vertical edge, so `depth_region G_notch
pext` is **true** ("inside"). But `pext` is in the unbounded component
(`notch_pext_not_interior`, #86) — not enclosed. So `depth_region` disagrees
with the geometric interior for a closed kept boundary, purely because of the
horizontal edge.

## GREEN — a no-horizontal-edge guard excludes it

```coq
Definition depth_region_generic_guarded (G : TopologyGraph) (r : Ring) (p : Point) : Prop :=
  edges_of (kept_edges G) = ring_edges r ->
  no_horizontal_edge_at p r ->
  depth_region G p.

Theorem Gnotch_excluded_by_no_horizontal_guard :
  depth_region_generic_guarded G_notch notch pext.   (* vacuous: notch has a horizontal edge *)
```

### RGR status

| phase | content | status |
|---|---|---|
| **RED**   | a *closed* kept boundary with a horizontal edge misclassifies (`depth_region_horizontal_refutes`) | Qed |
| **GREEN** | a `no_horizontal_edge_at` guard on the kept boundary excludes the witness (`Gnotch_excluded_by_no_horizontal_guard`) | Qed |
| **REFACTOR** | thread closed-boundary (#91) + generic-position guards through `depth_region_is_buffer` / `buffer_H_bridge_factor` | follow-up |

## The `depth_region` guard picture (with #91)

| guard | role | shown by |
|---|---|---|
| closed kept boundary (even kept-degree) | necessary | #91 (open spur) |
| `no_horizontal_edge_at` on the kept boundary | necessary on top of closure | this file |
| `ray_avoids_vertices` on the kept boundary | necessary by the same argument as #85 | (analogous; not separately formalised) |

## Registry note

No `admitted-counterexamples.txt` entry: the file has no `Admitted`; this is a
Qed-closed scope finding about the definition `depth_region`.
