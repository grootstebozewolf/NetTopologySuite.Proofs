# Cyclic `next` operator — `extract_rings_valid` R5, slice 2b

**Coq artifact:** [`theories/DartNext.v`](../theories/DartNext.v)
(Qed-closed; no `Admitted` / `Axiom` / `Parameter`; axioms = the allowlisted
classical-reals pair, via the real-order decisions reused from slice 2a).

**Thread:** `extract_rings_valid` R5 — see
[`docs/extract-rings-proof-structure.md`](extract-rings-proof-structure.md) §5,
building on [`docs/dart-angular-order.md`](dart-angular-order.md) (slice 2a) and
[`docs/dart-halfedge-foundation.md`](dart-halfedge-foundation.md) (slice 1).

---

## Why this slice

Slice 2a proved `dir_lt` / `dart_lt` a strict total order on directions — but as
a **`Prop`**. The fan is a `list Dart` (`Dart.outgoing v D`), so selecting the
rotational successor needs the order to be **computable**. This slice reflects
the comparator into `bool` and builds the `next` function on top.

## What's here

### Boolean reflection

```coq
Definition dir_ltb (p q : Vec) : bool := ...        (* mirrors dir_lt *)
Lemma dir_ltb_spec  : dir_ltb p q = true <-> dir_lt p q.
Definition dart_ltb (d1 d2 : Dart) : bool := dir_ltb (ddir d1) (ddir d2).
Lemma dart_ltb_spec : dart_ltb d1 d2 = true <-> dart_lt d1 d2.
```

Built from slice 2a's `first_half_dec` plus the real-order decision on `vcross`
— no new axioms.

### The rotational successor

```coq
Definition list_min (l : list Dart) : option Dart := ...   (* dart_ltb-minimum *)

Definition next (F : list Dart) (d : Dart) : Dart :=
  match list_min (filter (fun e => dart_ltb d e) F) with
  | Some e => e                                 (* minimal strictly-greater dart *)
  | None => match list_min F with               (* wrap: d is the fan maximum    *)
            | Some e => e | None => d end        (* -> global minimum             *)
  end.
```

| lemma | content |
|---|---|
| `list_min_in` / `list_min_none_iff` | the minimum is a member; `None` iff empty |
| `next_in` | **orbit closure** — the successor never leaves the fan |
| `next_base` | the successor stays based at the same vertex |
| `next_advances` | while a strictly-greater dart exists, `next d` is one of them (`dart_lt d (next d)`) — it advances in angle |

`next` lands in the fan and advances in angle, with a wrap-around at the fan
maximum that closes the cycle — the rotational-successor shape the face walk
needs.

## Deliberately deferred (slice 2c and the §9 crux)

- **minimal-successor correctness** — that `next d` is *the* (`dart_ltb`-least)
  successor, not merely *a* successor. Needs transitivity threaded through the
  `fold_left` minimum under a **general-position** hypothesis (pairwise
  non-parallel fan directions, the noded JCT-seam guarantee).
- **injectivity / cyclic permutation** — `next` is a bijection of the fan.
- **`face_of`** — the orbit of `next ∘ twin`, and its **finiteness** (the
  `face_orbit_finite` crux of §9); then face orbit ⇒ `closed_chain` feeding
  `RingExtract.ring_of_chain`.

### Registry note

No `admitted-counterexamples.txt` entry: no `Admitted`. Additive — asserts and
weakens nothing about the existing pipeline.
