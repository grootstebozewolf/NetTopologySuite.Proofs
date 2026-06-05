# Face orientation classification — `extract_rings_valid` R5, slice 3e

**Coq artifact:** [`theories/FaceOrientation.v`](../theories/FaceOrientation.v)
(Qed-closed; no `Admitted` / `Axiom` / `Parameter`; standard three-axiom
classical-reals base via `R` arithmetic, introduces none of its own).

**Thread:** `extract_rings_valid` R5 — see
[`docs/extract-rings-proof-structure.md`](extract-rings-proof-structure.md)
§5 step 3 (hole nesting), lifting slice 3d
([`docs/ring-orientation.md`](ring-orientation.md)) to rings and faces.

---

## Why this slice

Slice 3d gave the signed-area primitive and its orientation-flip law. This slice
lifts it to **rings** and **faces**, building the combinatorial scaffolding for
distinguishing the outer ring from holes — *without* the analytic claim that the
sign means "encloses".

## What's here

```coq
Definition ring_signed_area2 (r : Ring) : R := signed_area2 (ring_edges r).
Definition ring_ccw r := ring_signed_area2 r > 0.
Definition ring_cw  r := ring_signed_area2 r < 0.
```

| lemma | content |
|---|---|
| `ring_ccw_not_cw`, `ring_orientation_trichotomy` | the classifier is exclusive and exhaustive (CCW / CW / degenerate) |
| `ring_signed_area2_of_chain` | a face ring's signed area equals its defining chain's (via slice-3a `ring_edges_of_closed_chain`) |
| `seg_of_twin_swap` | `seg_of (twin d) = swap_seg (seg_of d)` |
| `map_swap_face_chain` | swapping every face segment = taking the segments of the **twin** darts |
| **`twin_face_chain_signed_area`** | the twin face (twin darts, walked in reverse) has the **negated** signed area |
| `twin_face_cw_of_ccw` | so a CCW face's twin face is CW |

## The headline: adjacent faces are oppositely oriented

```coq
Definition twin_face_chain D d n := rev (map seg_of (map twin (dart_walk D d n))).

Theorem twin_face_chain_signed_area :
  signed_area2 (twin_face_chain D d n) = - signed_area2 (face_chain D d n).
```

The face across each edge is reached by `twin` (which swaps each segment,
`seg_of_twin_swap`) and walked in reverse — and slice 3d's
`signed_area2_reverse_traversal` says that negates the signed area. So **the two
faces sharing an edge carry opposite orientation sign** — the combinatorial
heart of "outer boundary one way, holes the other". Combined with
`ring_signed_area2_of_chain`, this is stated for the actual face rings produced
by the slice-3a machinery.

## Deliberately deferred (the analytic frontier)

- the **geometric meaning** of the sign: positive area ⟺ the face is bounded /
  encloses its interior — this is the JCT-adjacent step;
- the **analytic** `hole_inside_outer` point-set containment (§4), shared with
  R3's H1 gap;
- a **globally consistent** orientation assignment across an arrangement's faces
  (so the signs partition into one outer + holes), and assembling a
  `valid_polygon` *with* holes.

### Registry note

No `admitted-counterexamples.txt` entry: no `Admitted`. Additive — asserts and
weakens nothing about the existing pipeline.
