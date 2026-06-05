# Face ring is simple — `extract_rings_valid` R5, slice 3b

**Coq artifact:** [`theories/FaceRingSimple.v`](../theories/FaceRingSimple.v)
(Qed-closed; no `Admitted` / `Axiom` / `Parameter`; axioms = the allowlisted
classical-reals pair).

**Thread:** `extract_rings_valid` R5 — see
[`docs/extract-rings-proof-structure.md`](extract-rings-proof-structure.md) §4,
joining slice 3a ([`docs/face-chain.md`](face-chain.md)) to
`RingSimple.ring_simple_of_subset`.

---

## Why this slice

Slice 3a gave a face ring that is `ring_closed`, `ring_has_minimum_points`, with
edges exactly the face segments. `RingSimple.ring_simple_of_subset` says a ring
whose edges all lie in a `pairwise_no_proper_cross` (noded) arrangement is
`ring_simple`. This slice connects them, completing **three of the four**
`valid_polygon` conditions for a face ring.

## The key observation

A face segment of a dart `d` is `seg_of d = (dbase d, dtip d) = (fst d, snd d)`.
Since `Dart = Edge = Point*Point`, by `surjective_pairing` this is **`d`
itself**. So a face ring's edges are exactly arrangement darts.

| lemma | content |
|---|---|
| `dart_walk_subset` | every dart on the walk is in `D` (closure) |
| `face_chain_subset` | every face segment is a dart of `D` (`seg_of d = d`) |
| **`face_ring_simple`** | if `D` is `pairwise_no_proper_cross`, the face ring is `ring_simple` |
| **`face_ring_combinatorial_valid`** | a `≥ 3`-dart face of a noded, well-formed arrangement ⇒ `ring_closed ∧ ring_has_minimum_points ∧ ring_simple` |

`face_ring_simple` rewrites the ring's edges to the face segments
(`ring_edges_of_closed_chain`), shows each is in `D` (`face_chain_subset`), and
applies `ring_simple_of_subset` with the noding hypothesis
`pairwise_no_proper_cross D` — exactly the snap-rounding noder's
`fully_intersected` guarantee.

## `valid_polygon` scorecard for a face ring

| condition | status |
|---|---|
| `ring_closed` | ✅ slice 3a (`face_walk_closed`) |
| `ring_has_minimum_points` | ✅ slice 3a (`face_walk_min_points`, ≥3 darts) |
| `ring_simple` | ✅ **this slice** (noded arrangement) |
| `hole_inside_outer` | ⏳ analytic / JCT-adjacent residual (§4) |

Three of four conditions now hold **by construction** of the face walk, for a
general noded overlay arrangement.

## Deliberately deferred (the remaining R5 shell)

- **hole nesting** — distinguishing the outer ring from hole rings (the
  face-incidence tree, §5 step 3): the combinatorial half of `hole_inside_outer`;
- the **analytic** `hole_inside_outer` point-set containment (§4) — the only
  genuinely JCT-adjacent piece, shared with R3's H1 gap;
- re-defining `extract` to emit `{ outer_ring ; hole_rings }` and closing
  `extract_rings_valid`.

### Registry note

No `admitted-counterexamples.txt` entry: no `Admitted`. Additive — asserts and
weakens nothing about the existing pipeline.
