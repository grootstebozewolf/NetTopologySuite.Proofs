# The vertex-grazing counterexample: `no_horizontal_edge_at` is not enough

**Coq artifact:** [`theories/JCT_VertexGrazingCounterexample.v`](../theories/JCT_VertexGrazingCounterexample.v)
(Qed-closed; no `Admitted` / `Axiom` / `Parameter`; axiom footprint =
the standard classical-reals pair on the allowlist).

**Seam touched:** the named remaining JCT seam
`parity_characterises_interior_cont` in [`theories/JCT.v`](../theories/JCT.v).

---

## TL;DR

`JCT.v` reduces the polygonal Jordan Curve Theorem to a single named seam:

```coq
Definition parity_characterises_interior_cont (p : Point) (r : Ring) : Prop :=
  ring_simple r -> ring_closed r -> ring_has_minimum_points r ->
  no_horizontal_edge_at p r ->
  (geometric_interior_cont p r <-> point_in_ring p r).
```

It is meant to hold for every off-ring point of a valid simple polygon. This
file shows the **four guards are insufficient**: a genuinely simple convex
polygon (a diamond) has an off-ring point where the rightward ray **grazes a
vertex**, making ray-parity disagree with the true interior — while every guard
still holds.

This is the **continuous, vertex-grazing analogue** of the bowtie scope finding
([`docs/jct-bowtie-counterexample.md`](jct-bowtie-counterexample.md)): there the
missing premise was vertex *distinctness*; here it is the generic-position guard
that the rightward ray miss every vertex.

## The witness

A convex diamond and its centre:

```
            (0,1)
             /\
            /  \
   (-1,0)  *  A *  (1,0)       A = (0, 1/2)   ray crosses 1 edge  -> parity ODD
            \ B|/             B = (0, 0)      ray GRAZES (1,0)    -> parity EVEN
             \/
            (0,-1)
```

```coq
Definition diamond : Ring :=
  mkPoint 0 1 :: mkPoint 1 0 :: mkPoint 0 (-1) :: mkPoint (-1) 0 :: mkPoint 0 1 :: nil.
Definition A : Point := mkPoint 0 (1/2).
Definition B : Point := mkPoint 0 0.
```

The diamond is `ring_simple`, `ring_closed`, has ≥ 4 vertices, and — crucially —
has **no horizontal edge**, so `no_horizontal_edge_at p diamond` holds for
*every* `p`, including the pathological centre `B`.

## The graze

`edge_crosses_ray` (Overlay.v) uses a **strict** y-straddle: an edge counts only
if its endpoints satisfy `py a < py p < py b` or `py b < py p < py a`. At `B`
(`py = 0`) the two edges meeting at vertex `(1,0)` — `(0,1)→(1,0)` and
`(1,0)→(0,-1)` — each have an *endpoint* at `y = 0`, so neither strictly
straddles. No other edge straddles `y = 0` either. The crossing count is **0**
(even → "outside"), even though `B` is the centre of the diamond.

At `A` (`py = 1/2`) exactly one edge (`(0,1)→(1,0)`, intercept `x = 1/2 > 0`)
straddles: count **1** (odd → "inside"), which is correct.

## The refutation (RED)

`A` and `B` lie in the **same** connected component of the complement — joined
by the vertical segment `x = 0`, `y ∈ [0, 1/2]`, which meets the ring only at
the apexes `(0,±1)`, both outside the segment:

```coq
Lemma diamond_segment_off_ring : connected_in_complement_cont diamond B A.
```

`geometric_interior_cont` is a **component invariant** (assembled from `JCT.v`'s
`in_bounded_component_cont_iff` + the off-ring endpoint lemmas), whereas
`point_in_ring` is **not** (it differs on `A` and `B`). So the seam cannot hold
at both:

```coq
Theorem diamond_refutes_parity_seam :
  ~ (parity_characterises_interior_cont A diamond /\
     parity_characterises_interior_cont B diamond).
```

Both `A` and `B` satisfy all four guards, so `parity_characterises_interior_cont`
is **not universally true** for a valid simple polygon as stated — at least one
of these well-formed instances is false. (The false one is `B`; proving that
directly needs `geometric_interior_cont B`, the thesis-scale bounded-interior
fact, so the proof routes through the invariant + the foil `A` instead.)

## The fix (GREEN)

The defect is exactly the graze: a ring vertex sitting on `B`'s rightward ray.
The missing premise is the standard generic-position guard:

```coq
Definition ray_avoids_vertices (p : Point) (r : Ring) : Prop :=
  forall v : Point, In v r -> ~ (py v = py p /\ px p <= px v).

Lemma  diamond_B_ray_hits_vertex      : ~ ray_avoids_vertices B diamond.  (* (1,0) on the ray *)
Lemma  diamond_A_ray_avoids_vertices  :   ray_avoids_vertices A diamond.

Definition parity_characterises_interior_cont_strict (p : Point) (r : Ring) : Prop :=
  ring_simple r -> ring_closed r -> ring_has_minimum_points r ->
  no_horizontal_edge_at p r ->
  ray_avoids_vertices p r ->
  (geometric_interior_cont p r <-> point_in_ring p r).

Theorem diamond_excluded_by_strict_parity_seam :
  parity_characterises_interior_cont_strict B diamond.   (* vacuous: B fails the new guard *)
```

`diamond_guard_insufficient` makes the point sharp: `no_horizontal_edge_at B
diamond` holds *and* `~ ray_avoids_vertices B diamond` — the existing guard
passes the bad point; only the new one rejects it.

### RGR status

| phase | content | status |
|---|---|---|
| **RED**   | diamond centre B passes all four guards yet ray-parity mis-classifies it (`diamond_refutes_parity_seam`) | Qed |
| **GREEN** | adding `ray_avoids_vertices` excludes B (`diamond_excluded_by_strict_parity_seam`) | Qed |
| **REFACTOR** | re-point `JCT.v`'s `parity_characterises_interior_cont` / `point_in_ring_correct_jct_cont` at the generic-position-strengthened guard | follow-up |

## Registry note

No `admitted-counterexamples.txt` entry: the file has no `Admitted`, and
`parity_characterises_interior_cont` is a `Prop` seam hypothesis, not an
`Admitted` theorem — this is a scope finding about it, fully Qed-closed.
