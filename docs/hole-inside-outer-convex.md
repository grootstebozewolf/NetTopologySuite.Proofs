# Convex `hole_inside_outer` — Stage C opened (concrete instance)

**Coq artifact:** [`theories/HoleInsideOuterConvexExample.v`](../theories/HoleInsideOuterConvexExample.v)
(Qed-closed; standard three-axiom classical-reals base).

**Thread:** Stage C of [`docs/hole-inside-outer-plan.md`](hole-inside-outer-plan.md).

---

## Honest scope

Stage B closed `hole_inside_outer` **unconditionally for all rectangles**, because
`RectangleJCT` already supplies the parity characterisation `point_in_ring_rect_iff`.
`ConvexField` supplies the *separation engine* (`conv_min`, `convex_separation`)
but **no parity characterisation** for convex rings — the general convex
`point_in_ring p (convex_ring …)` is a ray-crossing count over an arbitrary CCW
convex polygon (convex-chain monotonicity), genuinely substantial geometric work,
and is **not attempted here**.

## What this lands

The first convex instance **beyond axis-aligned rectangles**: a **diamond**
(rotated square) whose four edges are **slanted**, so the crossing test exercises
real x-intercept arithmetic (not the rectangle's degenerate vertical/horizontal
edges).

```coq
Definition diamond : Ring := [ (2,0); (4,2); (2,4); (0,2); (2,0) ].
Lemma diamond_interior_point_in_ring : point_in_ring (mkPoint 2 1) diamond.
Theorem hole_inside_outer_diamond     : hole_inside_outer diamond hole_diamond.
```

The interior point `(2,1)` is chosen off all vertex heights (`y ∈ {0,2,4}`), so
the rightward ray grazes no vertex. It crosses exactly the south-east slanted
edge `(2,0)-(4,2)` (x-intercept `3 > 2`) and no other → odd parity →
`point_in_ring`, all via the `ray_parity_odd` constructors with each
`edge_crosses_ray` decided by `lra` (numeral denominators, so the slanted
intercepts close directly).

## Status

This is a **regression anchor** for the convex beachhead and a demonstration that
the parity route extends to non-axis-aligned shapes — **not** the general convex
theorem. The general convex `point_in_ring` characterisation (and thence
unconditional convex `hole_inside_outer`) remains the substantial Stage-C work;
the rectangle case (Stage B) is the only *general* unconditional discharge so far.
