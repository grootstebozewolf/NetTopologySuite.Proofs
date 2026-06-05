# Face orbit → closed chain → ring — `extract_rings_valid` R5, slice 3a

**Coq artifact:** [`theories/FaceChain.v`](../theories/FaceChain.v)
(Qed-closed; no `Admitted` / `Axiom` / `Parameter`; axioms = the allowlisted
classical-reals pair).

**Thread:** `extract_rings_valid` R5 — see
[`docs/extract-rings-proof-structure.md`](extract-rings-proof-structure.md)
§5 step 2, joining slice 2f ([`docs/dart-face.md`](dart-face.md)) to the
existing `RingExtract` assembler.

---

## Why this slice

Two halves were already in place:

- slice 2f's **`face_orbit_finite`** — iterating the face step `fstep` from a
  dart returns to it;
- **`RingExtract.face_walk_core`** — a `closed_chain` (connected `Point*Point`
  segments that loop shut) yields a `ring_closed` / `ring_has_minimum_points`
  ring whose edges are exactly the chain.

This slice is the **missing link**: the face walk, as a list of dart segments,
*is* a `closed_chain`.

## What's here

```coq
Fixpoint dart_walk (D : list Dart) (d : Dart) (n : nat) : list Dart := ...  (* d, fstep d, .., fstep^(n-1) d *)
Definition seg_of (d : Dart) : Point * Point := (dbase d, dtip d).
Definition face_chain D d n : list (Point * Point) := map seg_of (dart_walk D d n).
```

| lemma | content |
|---|---|
| `face_chain_ok` | consecutive segments connect: `dbase (fstep e) = dtip e` (`next_base`) |
| `face_chain_closed_chain` | with the orbit return `iter fstep n d = d`, the chain loops shut → `closed_chain` |
| `face_closed_chain_exists` | every dart of a well-formed arrangement spawns a closed chain (via `face_orbit_finite`) |
| **`face_ring_valid_shape`** | a face of `≥ 3` darts ⇒ a ring that is `ring_closed`, `ring_has_minimum_points`, and whose edges are exactly the face segments |

## The two connection facts

- **Connection (chain_ok).** Consecutive walk darts are `e` and `fstep e`; the
  next segment starts at `dbase (fstep e)`, which is `dtip e` by `next_base`
  (the rotational successor is based at the head vertex). So `snd (seg e) =
  dtip e = dbase (fstep e) = fst (seg (fstep e))`.
- **Closure.** The last segment ends at `dtip (fstep^{n-1} d)`. Since `fstep^n d
  = d`, i.e. `fstep (fstep^{n-1} d) = d`, again by `next_base` `dbase d =
  dtip (fstep^{n-1} d)` — so the last segment's end equals the first segment's
  start. The chain loops shut.

`face_ring_valid_shape` then composes `face_chain_closed_chain` with
`RingExtract.face_walk_core` (length `n ≥ 3` from `face_chain_length`).

## Significance

This delivers the **combinatorial core of `valid_polygon`'s outer ring for a
GENERAL overlay arrangement** — closure + min-points + edge fidelity, by
construction of the face walk — not just the buffer beachhead that
`RingExtract` originally targeted. The DCEL "assembly" half of the R5 obligation
(turn an unordered surviving-edge set into ordered closed face walks) is now
discharged end to end: `darts_of` → angular order → cyclic `next` → face orbit
finiteness → closed chain → ring.

## Deliberately deferred (the remaining R5 shell)

- **hole nesting** — the face-incidence tree distinguishing the outer ring from
  hole rings (§5 step 3), the combinatorial part of `hole_inside_outer`;
- the **analytic** `hole_inside_outer` point-set residual (§4) — the only
  genuinely JCT-adjacent piece left;
- re-defining `extract` to emit `{ outer_ring ; hole_rings }` from face walks
  (§5 step 4) and closing `extract_rings_valid` itself.

### Registry note

No `admitted-counterexamples.txt` entry: no `Admitted`. Additive — asserts and
weakens nothing about the existing pipeline.
