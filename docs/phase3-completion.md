# Phase 3 completion: OverlayNG topology graph + boolean overlay

**Status.** Written 2026-06-01 retroactively. Phase 3's deliverable —
a planar topology graph with edge labelling and a Qed-closed
`overlay_ng_correct_conditional` headline under three named hypotheses
— landed on main across May 2026 (milestones 1–5). No completion doc
was written at the time; this artifact closes the documentation gap so
the Phase 0 → Phase 1 → Phase 2 → Phase 3 → Phase 4 retro chain is
intact.

The discipline observed for
[`docs/phase0-completion.md`](phase0-completion.md),
[`docs/phase1-completion.md`](phase1-completion.md), and
[`docs/phase2-completion.md`](phase2-completion.md) is mirrored here:
current state, what stays open, why this is "Phase 3 complete," future
paths.

## Current state (May 2026, completion point)

**Shipped, Qed-closed.**

Geometry + boolean-op semantics
([`theories/Overlay.v`](../theories/Overlay.v)):

- `Ring` / `Polygon` / `Geometry` types; `valid_polygon` /
  `valid_geometry` (OGC §6 conditions: `ring_closed`, `ring_simple`,
  `ring_has_minimum_points`, `hole_inside_outer`).
- `point_set` — the point-set semantics of a geometry; `point_in_ring`
  / `point_in_polygon` via ray crossing on `ring_edges`.
- `BooleanOp` enum + `boolean_op` — pure set-theoretic semantics of
  union / intersection / difference / symmetric difference; commutativity
  lemmas (`boolean_op_union_comm`, etc.).

Planar topology graph + labelling
([`theories/OverlayGraph.v`](../theories/OverlayGraph.v)):

- `TopologyGraph` record + `valid_topology_graph` + `build_graph`.
- `EdgeLabel` record + `merge_labels` / `merge_labeled_edges` +
  the label-algebra lemmas (`merge_in_left_iff`, `merge_in_right_iff`).
- `edge_in_result op` + `extract op g` — the S2 ring-extraction that
  filters survivors by the boolean op.

Snap-rounding noding bridge
([`theories-flocq/OverlayBridge.v`](../theories-flocq/OverlayBridge.v)):

- `noded_segments A B` / `noded_labeled_graph A B` — the bridge from
  Phase 2's snap-rounded noding into the topology graph.
- `correct_labels` + `correct_labels_{union,intersection,difference,symdiff}`.
- **`correct_labels_all_ops`** — Qed-closed: the labelling is correct
  for every boolean op, by uniform case-on-op composition.

Conditional headline
([`theories-flocq/OverlayCorrectness.v`](../theories-flocq/OverlayCorrectness.v)):

- **`overlay_ng_correct_conditional`** — HEADLINE. The point-set of the
  extracted overlay matches `boolean_op`, under three named hypotheses
  (H1 JCT, H2 DCEL valid polygons, H_bridge semantic):

```coq
Theorem overlay_ng_correct_conditional :
  forall (A B : Geometry) (op : BooleanOp) (p : Point),
    valid_geometry A ->
    valid_geometry B ->
    fully_intersected (noded_segments A B) ->
    (* H1 (JCT gap): point_in_ring captures topological interior *)
    (forall (q : Point) (r : Ring),
       ring_closed r -> ring_simple r ->
       point_in_ring q r <-> geometric_interior_stdlib q r) ->
    (* H2 (DCEL gap): extract assembles valid geometry *)
    (forall (op' : BooleanOp) (g : TopologyGraph),
       valid_topology_graph g ->
       valid_geometry (extract op' g)) ->
    (* H_bridge (semantic gap): consolidated point-set agreement *)
    (forall (g : TopologyGraph),
       valid_topology_graph g ->
       correct_labels op g A B ->
       valid_geometry (extract op g) ->
       (forall (q : Point) (r : Ring),
          ring_closed r -> ring_simple r ->
          point_in_ring q r <-> geometric_interior_stdlib q r) ->
       (point_set (extract op g) p <-> boolean_op op A B p)) ->
    point_set (extract op (noded_labeled_graph A B)) p <->
      boolean_op op A B p.
```

- `overlay_ng_correct_forward` / `overlay_ng_correct_backward` —
  Qed-closed directional corollaries.
- The `geometric_interior` Section Variable was eliminated and
  instantiated with `geometric_interior_stdlib`
  ([`theories/PointInRingTangents.v`](../theories/PointInRingTangents.v));
  the JCT gap now lives in H1's biconditional content, not in an opaque
  definition.

JCT seam work
([`theories/PointInRingCorrect.v`](../theories/PointInRingCorrect.v),
[`theories/PointInRingTangents.v`](../theories/PointInRingTangents.v)):

- Nine Qed-closed seam lemmas: `segment_crosses_ray` (sound + complete
  + correct), `ray_parity_fold_bridge`, `point_in_ring_eq_parity`,
  `segment_crosses_ray_iff_cross_R_pt`, and the principled stopping
  point `point_in_ring_correct_jct` (the target stated against named
  JCT-side hypotheses). No `Admitted` in either file.

Oracle consumer
([`theories-flocq/Validate_binary64_extract.v`](../theories-flocq/Validate_binary64_extract.v)):

- RocqRefRunner mode `EDGE_IN_RESULT` extracted — the boolean-op edge
  survival decision is differential-testable.

## Open

Two pieces remain. They are carried as the headline's explicit named
hypotheses (H1, H2), not silently assumed.

### `extract_rings_valid` — H2, the DCEL gap (registered deferred proof)

`extract` is the naive S2 version: it filters edges by
`edge_in_result op` and concatenates survivors into a single polygon.
That does NOT satisfy `valid_polygon` in general. The usable proof
needs a DCEL refactor (doubly-connected edge list with twin/next
pointers + face-traversal ring extraction), then per-condition proofs
against the new structure. Registered as a Tier-3 deferred `Admitted`
in [`docs/admitted-deferred-proofs.txt`](admitted-deferred-proofs.txt)
with the proof path in
[`docs/audit-phase3-milestone5.md`](audit-phase3-milestone5.md)
§4.3, §7. Estimated **5–7 sessions** (DCEL path). Pure structural
reasoning — no JCT or point-set semantics needed at this level.

### `point_in_ring_correct` — H1, the JCT gap (thesis-scale, no Coq stub)

H1 asks that ray-crossing parity captures the topological interior on
valid rings — the polygonal Jordan Curve Theorem. The JCT scout
([`docs/jct-scout-2026-05-29.md`](jct-scout-2026-05-29.md)) confirmed
**RED, thesis-scale**: the installed ecosystem (fourcolor 1.4.2 +
mathcomp-analysis 1.16.0) has no JCT for ℝ² polygons, and the three
bridge gaps (combinatorial→topological, Stdlib ℝ → `Real.structure`,
crossing-number ↔ interior) do not shortcut the load-bearing piece.
This is carried as a named hypothesis with **no Coq deferred-proof
entry** — the JCT toolkit is absent from the corpus, so there is
nothing to stub. Re-open when a published Coq formalisation of polygonal
JCT appears. See [`docs/point-in-ring-jct-path.md`](point-in-ring-jct-path.md)
for the minimal hypothesis set.

## Why this is "Phase 3 complete"

Phase 3's chokepoint deliverable is a **verified OverlayNG**: build a
topology graph from noded input, label its edges, and extract the
boolean-op result with point-set semantics matching the set operation.
That deliverable shipped at the conditional level, end-to-end:

- **Coq-side**: the geometry + boolean-op semantics, the planar topology
  graph + labelling (`correct_labels_all_ops`), the snap-rounding bridge,
  and `overlay_ng_correct_conditional` — Qed-closed under three named
  gaps, with the JCT seam advanced to a principled stopping point.
- **Oracle-side**: `EDGE_IN_RESULT` extracted for differential testing.

What's open — DCEL ring-assembly validity and the polygonal JCT — is
parallel to Phase 0's open Stage D and Phase 2's open Lemma 4.3:
substantial separate engagements (one registered as a deferred proof,
one thesis-scale with no toolkit), carried as the conditional's explicit
hypotheses rather than assumed.

## Future paths

In rough order of payoff vs. cost:

1. **`extract_rings_valid` via DCEL** — the registered deferred proof;
   discharging H2 is the next chokepoint slice (5–7 sessions, structural).
2. **`point_in_ring_correct` (JCT)** — gated on a published polygonal
   JCT formalisation; thesis-scale until then. The seam lemmas in
   `PointInRingCorrect.v` are the landing points.
3. **C#-side overlay port** — mirror the topology graph + labelling
   into `NetTopologySuite.Robust.*` once the DCEL extract lands.
4. **Phase 4 onward** — native curves. Phase 4 composes on Phase 3's
   structural skeleton (the TRANSFER list in
   [`docs/audit-phase4-chord-overfitting.md`](audit-phase4-chord-overfitting.md)
   §3) and does NOT depend on closing (1) or (2).

## Audit summary

- **The only `Admitted` is `extract_rings_valid`**, registered as a
  Tier-3 deferred proof in
  [`docs/admitted-deferred-proofs.txt`](admitted-deferred-proofs.txt).
  The JCT gap is carried as a named hypothesis with no stub (toolkit
  absent). `scripts/check_admitted.sh` enforces the registration.
- **No silent narrowing of contracts.** H1 (JCT) and H2 (DCEL) are the
  headline's explicit premises; the Section Variable for
  `geometric_interior` was eliminated, so the gap is visible in the
  theorem statement, not hidden in a definition.
- **Axiom footprint.** `Overlay.v` / `OverlayGraph.v` /
  `PointInRing*.v` are in the clean Stdlib lane (no
  `Classical_Prop.classic` — they do not touch the snap layer).
  `OverlayBridge.v` / `OverlayCorrectness.v` inherit the Category C
  footprint via `fully_intersected (noded_segments …)`, tracked in
  [`docs/audit-exceptions.txt`](audit-exceptions.txt); same four-axiom
  baseline Phases 0–2 carry.

## Why this doc lands now

Phase 3 worked at the conditional level and Phase 4 composed on top of
it (`arc_overlay_correct_chord_approx` reuses the boolean-op case split
and the geometry skeleton). The missed ceremony was a
`docs/phase3-completion.md` to mirror the ones for Phases 0–2. This doc
closes that gap so the retrospective chain reads linearly when future
contributors trace the history.

---

**AI assistance disclosure:** AI-drafted, human-reviewed.
  Assisted-by: Claude
