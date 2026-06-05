# The horizontal-edge counterexample: why `no_horizontal_edge_at` is necessary

**Coq artifact:** [`theories/JCT_HorizontalEdgeCounterexample.v`](../theories/JCT_HorizontalEdgeCounterexample.v)
(Qed-closed; no `Admitted` / `Axiom` / `Parameter`; axiom footprint =
the standard classical-reals pair on the allowlist).

**Seam touched:** the named JCT seam `parity_characterises_interior_cont`
in [`theories/JCT.v`](../theories/JCT.v).

---

## TL;DR

This is the **necessity companion** to the vertex-grazing finding
([`docs/jct-vertex-grazing-counterexample.md`](jct-vertex-grazing-counterexample.md)).
That file showed the seam's `no_horizontal_edge_at` guard is *insufficient*
(a vertex graze slips past it). This file shows the guard is *necessary*: drop
it and ray-parity genuinely disagrees with the geometric interior.

## The witness

A valid simple **notch** hexagon — the rectangle `[0,4]×[0,2]` with the
top-left block `[0,2]×(1,2)` removed — and the **exterior** point `pext = (-1,1)`:

```
             (2,2)---------(4,2)
               |              |
               |   (notch)    |
   pext o------+----[====]----+        y = 1: the ray runs ALONG the
   (-1,1)    (2,1)        |    |               horizontal edge (2,1)->(0,1)
               .          |    |
             (0,1)--------'    |
               |  (bottom bar) |
             (0,0)----------(4,0)
```

```coq
Definition notch : Ring :=
  mkPoint 0 0 :: mkPoint 4 0 :: mkPoint 4 2 :: mkPoint 2 2
    :: mkPoint 2 1 :: mkPoint 0 1 :: mkPoint 0 0 :: nil.
Definition pext : Point := mkPoint (-1) 1.
```

The notch is `ring_simple`, `ring_closed`, and has ≥ 4 vertices
(`notch_ring_simple`, `notch_ring_closed`, `notch_min_points`) — a genuinely
valid simple polygon, so the failure is not an artefact of invalidity.

## The disagreement (RED)

`pext` is plainly **outside** (it sits at `x = -1`, left of the whole polygon),
and it escapes to infinity leftward without meeting the ring, so it is in the
**unbounded** component:

```coq
Lemma notch_pext_not_interior : ~ geometric_interior_cont pext notch.
  (* via JCT.v's not_in_bounded_component_cont_intro: a leftward straight path
     reaches arbitrarily far while staying off the ring *)
```

Yet ray-parity calls it **inside**. The rightward ray at `y = 1` should cross
the boundary twice (enter on the left, exit on the right), but the left-hand
crossing happens degenerately *along* the horizontal edge `(2,1)→(0,1)` and its
endpoint vertices — all skipped by the strict y-straddle. Only the right edge
`(4,0)→(4,2)` at `x = 4` is counted: parity **1 = odd**.

```coq
Lemma    notch_point_in_ring_pext : point_in_ring pext notch.
Theorem  notch_refutes_parity_without_guard :
  point_in_ring pext notch /\ ~ geometric_interior_cont pext notch.
```

So `point_in_ring` and `geometric_interior_cont` disagree at `pext` — a raw
refutation of "ray-parity characterises the interior" with no horizontal-edge
guard present.

## The guard does real work (GREEN)

The notch has a horizontal edge `(2,1)→(0,1)` exactly at the ray height
`y = 1`, so `no_horizontal_edge_at pext notch` is **false**. The *existing* seam
therefore already excludes this witness vacuously:

```coq
Lemma    notch_violates_no_horizontal     : ~ no_horizontal_edge_at pext notch.
Theorem  notch_excluded_by_existing_seam  : parity_characterises_interior_cont pext notch.
```

`no_horizontal_edge_at` is necessary, not redundant — it is precisely what stops
the ray from running along a horizontal edge.

### RGR status

| phase | content | status |
|---|---|---|
| **RED**   | exterior `pext` is classified "inside" by ray-parity (`notch_refutes_parity_without_guard`) | Qed |
| **GREEN** | the existing `no_horizontal_edge_at` guard already excludes `pext` (`notch_excluded_by_existing_seam`) | Qed |
| **REFACTOR** | none needed — this *justifies* an existing guard | n/a |

## The complete guard picture

Together with the vertex-graze finding, the seam's correct guard **set** is now
pinned:

| guard | role | shown by |
|---|---|---|
| `no_horizontal_edge_at` | **necessary** (ray must not run along an edge) | this file |
| `ray_avoids_vertices`   | **additionally required** (ray must not graze a vertex) | `JCT_VertexGrazingCounterexample.v` |

## Registry note

No `admitted-counterexamples.txt` entry: the file has no `Admitted`, and
`parity_characterises_interior_cont` is a `Prop` seam hypothesis — this is a
scope finding about it, fully Qed-closed.
