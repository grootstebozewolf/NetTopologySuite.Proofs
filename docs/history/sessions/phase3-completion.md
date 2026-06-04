# Phase 3 completion: OverlayNG topology graph + boolean overlay

Phase 3 delivers OverlayNG: build a topology graph from noded input,
label its edges, and extract the boolean-op result with point-set
semantics matching the set operation. The headline
`overlay_ng_correct_conditional` is Qed-closed under three named
hypotheses; milestones 1–5 landed on main in May 2026.

## Shipped (Qed-closed)

**Geometry + boolean-op semantics** —
[`theories/Overlay.v`](../theories/Overlay.v):

- `Ring` / `Polygon` / `Geometry` types; `valid_geometry` (OGC §6:
  closed, simple, minimum points, holes inside outer).
- `point_set`, `point_in_ring`/`point_in_polygon` (ray crossing).
- `BooleanOp` + `boolean_op` — set-theoretic union/intersection/
  difference/symdiff, with commutativity lemmas.

**Topology graph + labelling** —
[`theories/OverlayGraph.v`](../theories/OverlayGraph.v):

- `TopologyGraph` + `valid_topology_graph` + `build_graph`.
- `EdgeLabel`, `merge_labels`, the label algebra.
- `edge_in_result op` + `extract op g`.

**Noding bridge** —
[`theories-flocq/OverlayBridge.v`](../theories-flocq/OverlayBridge.v):

- `noded_segments` / `noded_labeled_graph` (from Phase 2's snap-rounded
  noding).
- `correct_labels_all_ops` — labelling correct for every boolean op.

**Headline** —
[`theories-flocq/OverlayCorrectness.v`](../theories-flocq/OverlayCorrectness.v):

```coq
Theorem overlay_ng_correct_conditional :
  forall (A B : Geometry) (op : BooleanOp) (p : Point),
    valid_geometry A ->
    valid_geometry B ->
    fully_intersected (noded_segments A B) ->
    (* H1 (JCT): ray-crossing parity = topological interior *)
    (forall (q : Point) (r : Ring),
       ring_closed r -> ring_simple r ->
       point_in_ring q r <-> geometric_interior_stdlib q r) ->
    (* H2 (DCEL): extract assembles valid geometry *)
    (forall (op' : BooleanOp) (g : TopologyGraph),
       valid_topology_graph g -> valid_geometry (extract op' g)) ->
    (* H_bridge: point-set of extract agrees with boolean_op *)
    (forall (g : TopologyGraph),
       valid_topology_graph g ->
       correct_labels op g A B ->
       valid_geometry (extract op g) ->
       (forall (q : Point) (r : Ring),
          ring_closed r -> ring_simple r ->
          point_in_ring q r <-> geometric_interior_stdlib q r) ->
       (point_set (extract op g) p <-> boolean_op op A B p)) ->
    point_set (extract op (noded_labeled_graph A B)) p <-> boolean_op op A B p.
```

Plus forward/backward corollaries. The opaque `geometric_interior`
Section Variable was eliminated and instantiated with
`geometric_interior_stdlib`, so the JCT gap is visible in H1's content,
not hidden in a definition.

**JCT seam** —
[`theories/PointInRingCorrect.v`](../theories/PointInRingCorrect.v),
[`theories/PointInRingTangents.v`](../theories/PointInRingTangents.v):
nine Qed-closed seam lemmas (`segment_crosses_ray` sound/complete,
`ray_parity_fold_bridge`, `segment_crosses_ray_iff_cross_R_pt`) up to
the principled stopping point `point_in_ring_correct_jct`. No `Admitted`.

**Oracle** — RocqRefRunner mode `EDGE_IN_RESULT` extracted.

## Open

Both gaps are the headline's explicit hypotheses, not silent assumptions.

**`extract_rings_valid` (H2).** Current `extract` is the naive version —
filter edges by `edge_in_result op`, concatenate survivors — which isn't
`valid_polygon` in general. A real proof needs a DCEL (twin/next
pointers, face-traversal ring extraction) plus per-condition proofs.
Registered as a deferred proof
([`audit-phase3-milestone5.md`](audit-phase3-milestone5.md) §4.3, §7);
~5–7 sessions, pure structural reasoning.

**`point_in_ring_correct` (H1).** The polygonal Jordan Curve Theorem.
The JCT scout ([`jct-scout-2026-05-29.md`](jct-scout-2026-05-29.md))
found nothing reusable in the installed ecosystem (fourcolor's `Jordan`
is purely combinatorial; mathcomp-analysis has no ℝ² polygon JCT), so
this is thesis-scale with **no Coq stub** — the toolkit is absent, there's
nothing to register. Re-open when a published polygonal JCT formalisation
exists. Minimal hypothesis set in
[`point-in-ring-jct-path.md`](point-in-ring-jct-path.md).

## What "complete" means here

The overlay ships at the conditional level: structural skeleton,
labelling, and the noding bridge are Qed-closed, and the headline holds
under three named gaps — one registered deferred (DCEL), one thesis-scale
(JCT). Phase 4 reuses this skeleton (its TRANSFER list,
[`audit-phase4-chord-overfitting.md`](audit-phase4-chord-overfitting.md)
§3) and doesn't need either gap closed first.

## Next

1. `extract_rings_valid` via DCEL — the next structural slice.
2. `point_in_ring_correct` — gated on a published polygonal JCT.
3. C# port of the topology graph + labelling, once DCEL extract lands.

## Audit

- One `Admitted` (`extract_rings_valid`), registered as a deferred proof.
  The JCT gap is a named hypothesis with no stub (toolkit absent).
- `Overlay.v` / `OverlayGraph.v` / `PointInRing*.v` are classic-free.
  `OverlayBridge.v` / `OverlayCorrectness.v` inherit the Category C
  footprint via `fully_intersected (noded_segments …)`, tracked in
  [`audit-exceptions.txt`](audit-exceptions.txt).
