# Dart angular comparator — `extract_rings_valid` R5, slice 2a

**Coq artifact:** [`theories/DartAngularOrder.v`](../theories/DartAngularOrder.v)
(Qed-closed; no `Admitted` / `Axiom` / `Parameter`; axioms = the allowlisted
classical-reals decidability pair, via the real-order decision in
`first_half_dec`).

**Thread:** `extract_rings_valid` R5 — see
[`docs/extract-rings-proof-structure.md`](extract-rings-proof-structure.md) §5,
building on the dart foundation
([`docs/dart-halfedge-foundation.md`](dart-halfedge-foundation.md)).

---

## Why this slice

Slice 1 ([`Dart.v`](../theories/Dart.v)) gives the `outgoing v` fan of darts
based at a vertex. To define the cyclic `next` (rotational successor), the fan
must be **ordered by angle** — and the `Azimuth` design forbids a materialised
`atan2`. So the order is a pure **half-plane + cross-product** comparator
(`Azimuth.turn_sign = vcross`). This slice delivers that comparator and proves
it is a **strict total order** on directions in general position.

## What's here

```coq
Definition first_half (p : Vec) : Prop :=          (* angle in [0, pi) *)
  vy p > 0 \/ (vy p = 0 /\ vx p > 0).

Definition dir_lt (p q : Vec) : Prop :=            (* p has smaller angle *)
  (first_half p /\ ~ first_half q)
  \/ (((first_half p /\ first_half q) \/ (~ first_half p /\ ~ first_half q))
      /\ vcross p q > 0).
```

| lemma | content |
|---|---|
| `first_half_dec` | the half is decidable (real-order decision) |
| `dir_lt_irrefl`, `dir_lt_asym` | strict (irreflexive + asymmetric) |
| **`dir_lt_trans`** | transitive, for non-parallel endpoints — the crux |
| `dir_lt_total` | total on non-parallel pairs |
| `dart_lt_*` | the same four laws lifted to darts via `ddir d = tip − base` |

## The transitivity crux

A cross-product sign is **not** a cyclic order on its own; transitivity is the
classic hard step. Two ingredients make it clean:

1. **The algebraic certificate** (`vcross_chain_cert`, a pure `ring` identity):

   ```
   vy w · vcross u z  =  vy z · vcross u w  +  vy u · vcross w z
   ```

   So *within one half-plane* (all `vy ≥ 0`, or all `vy ≤ 0`), `vcross u w > 0`
   and `vcross w z > 0` force `vcross u z` to have the same sign — `nra`
   discharges it from the certificate plus the half-plane sign hypotheses.
   Strictness uses the endpoints being non-parallel (distinct directions); the
   middle direction is forced strictly off-axis, else `vcross u w ≤ 0`.

2. **The case collapse.** Of the eight `first_half` configurations of `(p,q,r)`,
   only **all-first** and **all-second** invoke the certificate; the other six
   are either immediate from the half split (`first_half p ∧ ¬first_half r`) or
   have a contradictory hypothesis (`dir_lt` cannot run against the half order).

`dir_lt` is thus a strict total order on directions **in general position**
(pairwise non-parallel) — exactly the fan of a noded arrangement, where no two
darts at a vertex share a direction.

## Deliberately deferred (next slices)

- **cyclic `next`** = the rotational successor in `outgoing v` *built from*
  `dart_lt` (pick the `dart_lt`-successor, wrapping around the fan).
- **`face_of`** = the orbit of `next ∘ twin`, and its **finiteness** — the
  `face_orbit_finite` crux of §9.
- face orbit ⇒ `closed_chain`, feeding `RingExtract.ring_of_chain`.

### Registry note

No `admitted-counterexamples.txt` entry: no `Admitted`. Additive foundation —
asserts and weakens nothing about the existing pipeline.
