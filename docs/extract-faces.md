# The extract rewire — `extract_rings_valid` R5, slice 3g

**Coq artifact:** [`theories/ExtractFaces.v`](../theories/ExtractFaces.v)
(Qed-closed; no `Admitted` / `Axiom` / `Parameter`; axioms = the allowlisted
classical-reals pair).

**Thread:** `extract_rings_valid` R5 — see
[`docs/extract-rings-proof-structure.md`](extract-rings-proof-structure.md)
§5 step 4 ("`extract` re-defined") and §11's "R1-open" item, downstream of
[`docs/face-polygon.md`](face-polygon.md) (3c) and
[`docs/face-chain.md`](face-chain.md) (3a).

---

## Why this slice

The DCEL programme (slices 1–3c) built everything needed to assemble valid
rings from an unordered noded edge set — darts, the angular `next`, the face
step `fstep`, orbit finiteness, face chains, and `face_polygon_valid` — but it
was never **wired to the pipeline**: `OverlayGraph.extract` still filters
`tg_edges g` by `edge_in_result op` and then *flattens* the survivors into one
pseudo-ring, which `ExtractFlattenCounterexample.extract_unordered_not_valid`
refutes as a `valid_polygon` source. The registered deferred proof
`extract_rings_valid` quantifies over *the polygons the extractor emits* —
so until an extractor actually emits face polygons, the face machinery
discharges nothing of that obligation's shape.

This slice performs the rewire.

## The extractor

```coq
Definition result_edges op g :=          (* extract's filter, minus the flatten *)
  map fst (filter (fun e => edge_in_result op (snd e)) (tg_edges g)).
Definition result_darts op g := darts_of (result_edges op g).

Definition face_polygon_at D d := face_polygon D d (face_period D d).
Definition extract_faces op g :=
  map (face_polygon_at (result_darts op g)) (result_darts op g).
```

One hole-free face polygon per surviving dart. Each face is emitted once per
boundary dart and the outer face's traversal is included — deduplication and
the bounded/CCW face selection (slice 3e orientation classification) are
*result-semantics* refinements, orthogonal to the validity obligation
(`forall poly, In poly (extract ...) -> valid_polygon poly`), which
quantifies over every emitted polygon anyway.

## The period: a bounded first-return search

`face_polygon` needs the orbit's return time `n` as an explicit argument.
`DartFace.face_orbit_finite` proves a return *exists*, but emitting polygons
needs the period as a **function** of the dart. `face_period D d` searches
`1 .. length D` for the first `k` with `iter (fstep D) k d = d`:

```coq
Definition face_period D d := first_return D d (seq 1 (length D)).
```

The search bound is justified by **`orbit_returns_bounded`**: an injective
self-map of a finite list returns within `length L` steps. The pigeonhole
inside `OrbitCycle.orbit_returns` proves exactly this bound (`i < j <
|S|+1`, return time `j − i ≤ |S|`) but exports only the existence; this
slice restates the bounded form from the same exported ingredients
(`seq_map_dup`, `iter_in`, `iter_inj_on`, `iter_comp`). `face_period_spec`
then pins the function down: on an `arrangement_ok` dart set, `face_period`
is a genuine positive return time.

## What's proved

| lemma | content |
|---|---|
| `in_result_edges_iff` | an edge survives iff some kept label carries it |
| `in_result_darts_iff` | a result dart is an orientation of a surviving edge |
| `result_darts_arrangement_ok` | twin-closure is free (`darts_of`); only per-vertex `fan_ok` is needed |
| `orbit_returns_bounded` | injective self-map of a finite list returns within `length L` steps |
| `face_period_spec` | `face_period` is a positive return time of `fstep` |
| **`extract_faces_valid`** | every polygon `extract_faces` emits is `valid_polygon` |
| `extract_faces_edges_subset` | every emitted ring edge is a surviving dart |
| `extract_faces_label_fidelity` | every emitted ring edge is (an orientation of) an op-kept labelled edge |

## The headline and its hypotheses

```coq
Theorem extract_faces_valid :
  forall op g,
    (forall v, fan_ok (outgoing v (result_darts op g))) ->
    pairwise_no_proper_cross (result_darts op g) ->
    no_short_faces (result_darts op g) ->
    forall poly, In poly (extract_faces op g) -> valid_polygon poly.
```

This is the **obligation shape of the registered deferred
`extract_rings_valid`** (`theories-flocq/OverlayBridge.v`), discharged for
the face extractor in the hole-free regime with **no Jordan-curve residual**.
The three hypotheses are the structural guarantees of the noded pipeline,
not analytic seams:

- `fan_ok` per vertex — general position of the noded arrangement's fans
  (the same hypothesis the whole slice 2a–2f order machinery carries);
- `pairwise_no_proper_cross` — the noder's `fully_intersected` output
  (the `RingSimple.ring_simple_of_subset` route);
- `no_short_faces` — every face has ≥ 3 darts: the no-spur/no-bigon
  property of a fully-noded arrangement.

`extract_faces_label_fidelity` adds the semantic half: the assembled rings
trace **only** edges that `edge_in_result op` kept — the extractor invents
no geometry, connecting the face walks back to the labelling layer
(`OverlayGraph.correct_labels_all_ops`).

## What remains

- **With-holes emission**: ✅ landed as slice 3h
  (`theories/ExtractFacesHoles.v`, `extract_faces_holes_valid`): the
  extractor emits with-holes polygons with the nesting supplied as a
  spec'd oracle; validity is conditional only on the per-hole
  `hole_inside_outer` clause — the same single JCT seam as
  `overlay_ng_correct_conditional` H1, now carried by an emitting
  extractor.  Computing the assignment (3e orientation classifier +
  nesting tree) and discharging the seam remain the analytic follow-ups.
- **Discharging the three hypotheses from `fully_intersected`** for the
  concrete noded output of `OverlayBridge` (connecting `noded_segments` to
  `fan_ok`/`no_short_faces`), which would re-point the deferred
  `extract_rings_valid` itself onto `extract_faces`.
- **R4 Euler relation** `V − E + F = 1 + C` (the oracle bridge to
  `buffer_hole_count.py`'s bounded-component count).
