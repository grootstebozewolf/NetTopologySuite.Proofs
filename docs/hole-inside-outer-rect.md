# Rectangle `hole_inside_outer` (unconditional) — R5 analytic seam, Stage B

**Coq artifact:** [`theories/HoleInsideOuterRect.v`](../theories/HoleInsideOuterRect.v)
(Qed-closed; no `Admitted`/`Axiom`/`Parameter`; standard three-axiom classical-reals base).

**Thread:** Stage B of [`docs/hole-inside-outer-plan.md`](hole-inside-outer-plan.md).

---

## The first non-toy discharge of the analytic seam

`hole_inside_outer outer hole := ∃ p, In p hole ∧ point_in_ring p outer`, and for
a rectangle `RectangleJCT.point_in_ring_rect_iff` (Qed) already says

```coq
point_in_ring p (rect_ring x0 y0 x1 y1) <-> (y0 < py p < y1 /\ x0 <= px p < x1).
```

Since `hole_inside_outer` is *defined* via `point_in_ring` (a ray-crossing parity
predicate), no JCT / IVT separation is needed for it — only box-membership of a
hole vertex. Hence:

```coq
Theorem hole_inside_outer_rect : forall x0 y0 x1 y1 hole p,
  x0 < x1 -> y0 < y1 -> In p hole ->
  y0 < py p < y1 -> x0 <= px p < x1 ->
  hole_inside_outer (rect_ring x0 y0 x1 y1) hole.
```

This is **unconditional** and holds for **every** axis-aligned rectangle —
generalising the fixed-4×4 witness (`HoleInsideOuterExample.v`) to the whole
rectangle class. `hole_inside_outer_rect_strict` is the open-interior form;
`hole_inside_outer_4x4_via_rect` re-derives the original concrete witness as an
instance.

## Coverage

The analytic seam is now closed **unconditionally for rectangular outer faces**.
What remains (per the plan): convex outers (Stage C, on
`ConvexField.convex_separation`), triangular outers (Stage D), and the general
simple-polygon JCT (Stage E, the registered residual).
