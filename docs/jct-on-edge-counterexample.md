# The H1 seam is false as stated: on-edge points pass both guards

**Date:** 2026-06-10.
**File:** `theories/JCT_OnEdgeCounterexample.v` (Qed-closed, three-axiom).
**Refutes:** `JCT.parity_characterises_interior_cont_strict` (and a fortiori
the un-strengthened `parity_characterises_interior_cont`) as universal
targets.
**Corrects to:** `parity_characterises_interior_cont_offring` (adds a
`ring_complement r p` premise).

## TL;DR

The corpus's formal statement of the H1 polygonal-JCT seam — the named Prop
`parity_characterises_interior_cont_strict p r` in `theories/JCT.v` — asserts
under five premises (`ring_simple`, `ring_closed`, `ring_has_minimum_points`,
`no_horizontal_edge_at`, `ray_avoids_vertices`):

```coq
geometric_interior_cont p r  <->  point_in_ring p r
```

This is **false** for points ON the ring skeleton: the two generic-position
guards constrain horizontal edges and vertices on the rightward ray, but they
do **not** exclude `p` itself lying on an edge — and there the ray-parity test
is **half-open** (the same phenomenon `GeneralTriangleParityRED.v` exhibited
for the triangle parity spec, one level up in the seam hierarchy).

## The witness

The CCW triangle `A=(0,0), B=(4,1), C=(1,3)` — chosen with **no horizontal
edge** (edge height pairs `(0,1)`, `(1,3)`, `(3,0)`) — and the point
`p = (1/2, 3/2)`, the midpoint of edge `C–A`. Then:

- **`point_in_ring p` is TRUE.** The rightward ray at height `3/2` crosses
  edge `B–C` exactly once (at `x = 13/4 > 1/2`); edge `A–B` lies below the ray
  (heights `0..1`); and the edge `C–A` that `p` lies on does **not** count —
  `p` is not strictly to its left (the edge's signed area at `p` is exactly
  `0`). Crossing number 1, parity odd.
- **`geometric_interior_cont p` is FALSE.** `p` is in the ring image
  (parameter `t = 1/2` on `C–A`), so `ring_complement r p` fails — and the
  continuous interior predicate is defined as
  `ring_complement ∧ in_bounded_component_cont`.
- **All five premises hold**, each Qed: `ring_simple` (six `nra` cases — no
  pair of the three adjacent edges crosses properly), `ring_closed`,
  `ring_has_minimum_points`, `no_horizontal_edge_at` (no edge is horizontal at
  all), and `ray_avoids_vertices` (`p`'s height `3/2` differs from all vertex
  heights `{0, 1, 3}`).

So the biconditional fails in the `point_in_ring → geometric_interior_cont`
direction: `parity_seam_strict_refuted_on_edge` and
`parity_seam_refuted_on_edge` are Qed.

## Consequence: the corrected H1 target

Any eventual discharge of H1 must carry an **off-ring premise**. The repaired
seam (in the same file) is

```coq
Definition parity_characterises_interior_cont_offring (p : Point) (r : Ring) : Prop :=
  ring_simple r -> ring_closed r -> ring_has_minimum_points r ->
  ring_complement r p ->
  no_horizontal_edge_at p r ->
  ray_avoids_vertices p r ->
  (geometric_interior_cont p r <-> point_in_ring p r).
```

and `point_in_ring_correct_jct_cont_offring` re-wires the conditional headline
of `JCT.v` against it (trivial composition, mirroring
`point_in_ring_correct_jct_cont`).

The guard set is now: the two ray-genericity guards (each previously shown
necessary: `JCT_HorizontalEdgeCounterexample.v`,
`JCT_VertexGrazingCounterexample.v`) **plus** the off-skeleton premise (shown
necessary here). Whether this set is *sufficient* is exactly the open H1
content — unchanged in difficulty, still thesis-scale.

## What is NOT affected

The three fully-closed families — rectangle
(`rect_parity_characterises_interior`), right triangle
(`right_triangle_parity_characterises_interior`), arbitrary triangle
(`general_triangle_parity_characterises_interior`) — all scope their
headlines to **strict-interior** points (`0 < field p`), which are off-ring
by construction (`gtri_interior_complement` and friends discharge
`ring_complement` from positivity). Their statements and proofs need no
change. Likewise the conditional headline `point_in_ring_correct_jct_cont`
remains *true* as a conditional — but its hypothesis is now known to be
unsatisfiable at on-edge points, which is why the `_offring` re-wiring is the
honest target going forward.

## Follow-up (same date): the corrected seam is satisfiable — rectangle discharged totally

`theories/RectangleOffringSeam.v` proves
`rect_parity_seam_offring : parity_characterises_interior_cont_offring p
(rect_ring x0 y0 x1 y1)` for **every** rectangle and **every** point — the
first family for which the (corrected) seam Prop itself is a theorem rather
than only its strict-interior projection. The new ingredient is the
exterior half: the generic straight-ray escape lemmas
`escape_beyond_{x,y}_{low,high}` (a point strictly beyond a one-sided bound
on the skeleton is in no bounded complement component), instantiated through
`rect_image_bounds`. Assembly is the `box_min` trichotomy: positive — the
existing strict-interior biconditional; zero — excluded by the off-ring
premise; negative — both sides of the biconditional are false
(`rect_exterior_not_in_ring` and the escape engine).

So the repair this counterexample forced is not merely consistent — it is
**achievable**: the off-ring seam now has a non-trivial, fully-Qed instance,
and the escape engine is the reusable piece the triangle and convex families
need for their own exterior halves.

## Follow-up 2 (same date): the triangle's exterior half + the half-plane escape engine

`theories/GeneralTriangleExterior.v` extends the programme to the first
sloped-edge family. The axis-aligned escapes do not suffice there (a
triangle's exterior point can sit strictly inside the vertex bounding box —
e.g. `(3,3)` for the triangle `(0,0),(4,0),(0,4)`), so the engine is
generalised to **half-planes**: `escape_beyond_halfplane` shows a point
strictly beyond a half-plane containing the skeleton is in no bounded
complement component, with the radius defeat done square-root-free via the
Cauchy–Schwarz polynomial identity. Since `gtri p < 0` names a violated edge
half-plane and the skeleton lies inside all three
(`gtri_image_slacks_nonneg`), exteriors escape (`gtri_exterior_escapes`),
giving the **total geometric ⇒ parity direction**
(`gtri_geometric_imp_in_ring`) and the triangle's total off-ring seam
**conditional on exactly one residual**
(`gtri_parity_seam_offring_of_exterior_parity`): exterior points have even
ray parity (`gtri p < 0 → ¬ point_in_ring p`). That residual — a guarded
case analysis over the per-edge crossing bands with mixed slack signs — is
the named target of the next rung; closing it makes the triangle the second
total family after the rectangle.

## Follow-up 3 (same date): the residual closed — triangle is the second total family

`theories/GeneralTriangleOffringSeam.v` closes the exterior-parity residual:
`gtri_exterior_even_parity` proves exterior points of a CCW triangle have
even ray parity under the `ray_avoids_vertices` guard (necessary — for the
triangle `(0,0),(2,2),(0,4)` the exterior point `(-1,2)` crosses edge `C–A`
once and then grazes vertex `B`, so the unguarded count is odd). The proof
inverts odd parity into the four odd crossing-subsets (`rpo3_cases`); the
triple dies on the pairwise-incompatible directed straddles, and each
singleton dies by a trichotomy on the opposite vertex's height: at that
height the guard puts the grazed vertex strictly west, factoring both
adjacent slacks; elsewhere the skipped edges pin one slack's sign, the
slack-sum identity pins another, and the barycentric height identity is
violated strictly. Composing with the conditional assembly of Follow-up 2:

`gtri_parity_seam_offring` — the corrected off-ring H1 seam holds for
**every CCW triangle and every point**. The total-family ladder now reads
**rectangle ✓, triangle ✓**; the convex n-gon is next (the half-plane escape
engine and the band machinery are both already shape-generic).

## Follow-up 4 (same date): the generic convex layer + the right triangle for free

`theories/ConvexOffringSeam.v` lifts the per-family scaffolding to the generic
half-plane presentation of `ConvexField.v`. Proved once, for any ring:
vertices inside a half-plane put the whole skeleton inside it
(`image_slack_nonneg` — the n-gon induction; note the hypothesis is the
**global** `vertices_in_halfplane` form, since the pentagram refutes the
local all-CCW-turns form), a negative `conv_min` names a violated half-plane,
and such a point escapes (`convex_exterior_escapes`). The assembly
`convex_parity_seam_offring_of` then reduces the total off-ring seam for ANY
half-plane-presented ring to four named family obligations: zero-set on the
skeleton, bounded positive region, and the two guarded parity facts
(interior odd / exterior even). All remaining topology is discharged in the
layer. Separately, `rtri_parity_seam_offring` lands the **third total
family** for free: the right-triangle ring is definitionally a `gtri_ring`
instance.

Remaining for the convex n-gon rung proper: the two parity obligations for a
vertex-list n-gon (the y-monotone-chain band argument) and its zero-set/bound
facts — the named targets of the next rung. The ladder: rectangle ✓,
triangle ✓, right triangle ✓, convex n-gon (parity obligations open),
general simple polygon (H1 proper, open).
