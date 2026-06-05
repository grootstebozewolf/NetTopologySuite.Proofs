# `next` rotational-successor correctness — `extract_rings_valid` R5, slice 2c

**Coq artifact:** [`theories/DartNextSpec.v`](../theories/DartNextSpec.v)
(Qed-closed; no `Admitted` / `Axiom` / `Parameter`; axioms = the allowlisted
classical-reals pair, via the real-order decisions and `Req_EM_T` reused here).

**Thread:** `extract_rings_valid` R5 — see
[`docs/extract-rings-proof-structure.md`](extract-rings-proof-structure.md) §5,
building on [`docs/dart-next.md`](dart-next.md) (slice 2b) and
[`docs/dart-angular-order.md`](dart-angular-order.md) (slice 2a).

---

## Why this slice

Slice 2b *defined* `next` and proved it well-defined (`next_in` / `next_base` /
`next_advances`), but explicitly deferred its **defining property**: that
`next d` is the *minimal* strictly-greater dart (and, on wrap, the global
minimum). The reason is that the `fold_left` minimum (`list_min`) is only a
*true* minimum when the comparator is a strict **total** order on the fan — and
that needs transitivity *and* totality threaded through the fold. This slice
supplies exactly that.

## The well-formed fan

```coq
Definition fan_ok (F : list Dart) : Prop :=
  (forall d, In d F -> proper_dart d)                                    (* real edges *)
  /\ (forall d e, In d F -> In e F -> d <> e -> ~ parallel (ddir d) (ddir e)).  (* general position *)
```

A noded arrangement's outgoing fan satisfies `fan_ok`: every dart is a genuine
edge (nonzero direction), and no two distinct darts at a vertex point the same
way. Under `fan_ok`, slice 2a's order becomes a strict **total** order on `F`
(`dart_ltb_trans_on` + `dart_ltb_total_on`, with the unconditional
`dart_ltb_irrefl`).

## The crux: `list_min` is a genuine minimum

```coq
Lemma fold_min_lb : ...     (* under transitivity + totality on (d0 :: l),
                               every element x satisfies dart_ltb x (fold ...) = false *)
Lemma list_min_lb :
  forall L m, sto_on L -> list_min L = Some m -> forall x, In x L -> dart_ltb x m = false.
```

The fold-minimality induction is where the order laws earn their keep: when the
running minimum's seed advances, the *discarded* head can never later turn out
to be smaller than the final minimum — proved by a transitivity chain
(`a < d0 < m ⇒ a < m`) against the IH, with totality resolving the
`¬(a < d0)` case into `a = d0 ∨ d0 < a`.

## `next` pinned down as the rotational successor

| lemma | content |
|---|---|
| `next_min_successor` | non-wrap: `next d ∈ F`, `dart_lt d (next d)`, and `next d ≤ e` for **every** strictly-greater `e` — i.e. *the* minimal successor |
| `next_wrap_least` | wrap (`d` is the fan maximum): `next d` is the global minimum of `F` |

Together these characterise `next` uniquely as the angular rotational successor
around the vertex.

## Deliberately deferred (slice 2d and the §9 crux)

- **injectivity / cyclic permutation** — that `next` is a bijection of the fan
  (each dart has a unique predecessor). This is the property the orbit argument
  needs to know the face walk is a genuine *cycle* rather than a "rho" shape;
  it builds directly on `next_min_successor` here.
- **`face_of`** — the orbit of `next ∘ twin`, and its **finiteness** (the
  `face_orbit_finite` crux of §9); then face orbit ⇒ `closed_chain` feeding
  `RingExtract.ring_of_chain`.

### Registry note

No `admitted-counterexamples.txt` entry: no `Admitted`. Additive — asserts and
weakens nothing about the existing pipeline.
