# Conditional `valid_polygon` headline via the JCT bridge — R5 seam, Stage A

**Coq artifact:** [`theories/ExtractFacePolygonJCT.v`](../theories/ExtractFacePolygonJCT.v)
(Qed-closed; no `Admitted`/`Axiom`/`Parameter`; standard three-axiom classical-reals base).

**Thread:** Stage A of [`docs/hole-inside-outer-plan.md`](hole-inside-outer-plan.md).

---

## What this lands

Slice 3f reduced the residual to `hole_inside_outer` (a ray-parity predicate).
This slice expresses that residual in its natural **geometric** form and bundles
it with the corpus's named JCT predicate
`JCT.parity_characterises_interior_cont_strict` (which packages the
`geometric_interior_cont ⟺ point_in_ring` bridge and its side conditions). The
result is a **conditional `valid_polygon` headline** matching the established
`overlay_ng_correct_conditional` / `point_in_ring_correct_jct` pattern — the JCT
appears **only** as a named hypothesis.

```coq
Definition hole_jct_witness (outer h : Ring) : Prop :=
  exists p, In p h /\ no_horizontal_edge_at p outer /\ ray_avoids_vertices p outer
            /\ parity_characterises_interior_cont_strict p outer   (* the named JCT *)
            /\ geometric_interior_cont p outer.

Theorem face_polygon_valid_via_jct :
  forall D, arrangement_ok D -> pairwise_no_proper_cross D ->
    forall d, In d D -> forall n, (3 <= n)%nat -> iter (fstep D) n d = d ->
    forall holes : list Ring,
      (forall h, In h holes -> ring_closed h /\ ring_simple h /\ ring_has_minimum_points h) ->
      (forall h, In h holes -> hole_jct_witness (ring_of_chain (face_chain D d n)) h) ->
      valid_polygon (mkPolygon (ring_of_chain (face_chain D d n)) holes).
```

`hole_inside_outer_of_witness` discharges the parity predicate from the witness
via the JCT bridge; the outer ring's three combinatorial conditions are automatic
(slice 3b). So for a face polygon, `extract_rings_valid` holds outright **except**
for the named JCT predicate inside the witness.

## Relation to Stage B

The witness's JCT predicate (`parity_characterises_interior_cont_strict`) is
discharged **unconditionally for rectangles** by Stage B
(`HoleInsideOuterRect`) — there `point_in_ring` is box-membership directly, so no
named JCT assumption is needed at all. Stages C/D extend that to convex/triangle;
the general simple-polygon JCT (Stage E) is the registered residual.
