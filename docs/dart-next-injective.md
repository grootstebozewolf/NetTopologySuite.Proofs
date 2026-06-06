# `next` injectivity / cyclic permutation — `extract_rings_valid` R5, slice 2d

**Coq artifact:** [`theories/DartNextInjective.v`](../theories/DartNextInjective.v)
(Qed-closed; no `Admitted` / `Axiom` / `Parameter`; axioms = the allowlisted
classical-reals pair, inherited from slices 2a–2c).

**Thread:** `extract_rings_valid` R5 — see
[`docs/extract-rings-proof-structure.md`](extract-rings-proof-structure.md) §5,
building on [`docs/dart-next-spec.md`](dart-next-spec.md) (slice 2c).

---

## Why this slice

Slice 2c pinned `next` down as *the* rotational successor. This slice proves the
companion fact that makes it a **cyclic permutation** of the fan rather than an
arbitrary self-map: it is **injective** (and, on a duplicate-free fan, onto).

Injectivity is exactly what an orbit argument needs to know the `face_of` walk
(`next ∘ twin`) is a genuine **cycle** — every dart on a closed loop — rather
than a "rho" shape with a tail running into a cycle.

## The geometric content: unique predecessors

In a cyclic angular order each dart has a **unique predecessor**:

- if `m` is **not** the global minimum, its predecessor is the maximal dart
  below it (reached in `next`'s non-wrap branch);
- if `m` **is** the global minimum, its predecessor is the (unique) global
  maximum (reached on wrap).

Either way at most one dart maps to `m`.

| lemma | content |
|---|---|
| `filter_succ_empty` / `filter_succ_ex` | decide "`d` has a strictly-greater dart" by emptiness of the strictly-greater filter — **no `classic` axiom** |
| `next_no_collision` | `d1 < d2 ⇒ next d1 ≠ next d2` (the directed core) |
| **`next_injective`** | `next` is injective on a `fan_ok` fan |
| `NoDup_map_inj_on` | `NoDup` is preserved by a map injective *on the list* |
| `next_surjective` | on a `NoDup` `fan_ok` fan, `next` is onto — every dart has a predecessor |

`next_no_collision` splits on the strict order between `d1, d2` and on whether
each has a successor, deriving a contradiction from `next d1 = next d2` via
`dart_lt_irrefl` / `dart_lt_asym`. `next_surjective` is the standard
"injective endofunction on a finite set is surjective" argument, via stdlib's
`NoDup_length_incl` against the image `map (next F) F` (which is `incl` in `F` by
orbit closure `next_in`, and `NoDup` by `next_injective`).

Together, injective + surjective = `next` is a **bijection of the fan**.

## Deliberately deferred (the §9 crux)

- **`face_of`** = the orbit of `next ∘ twin`, and its **finiteness**
  (`face_orbit_finite`). The `next ∘ twin` map composes `twin` (a global
  bijection on darts, `twin_involutive`) with the per-vertex `next` bijection;
  its orbit is a closed dart cycle = a face boundary.
- face orbit ⇒ `closed_chain` feeding `RingExtract.ring_of_chain` ⇒ the
  `ring_closed` / `ring_has_minimum_points` combinatorial core of
  `valid_polygon`.

### Registry note

No `admitted-counterexamples.txt` entry: no `Admitted`. Additive — asserts and
weakens nothing about the existing pipeline.
