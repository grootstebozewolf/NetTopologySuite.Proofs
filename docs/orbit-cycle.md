# Orbit cycle — `face_orbit_finite` core — `extract_rings_valid` R5, slice 2e

**Coq artifact:** [`theories/OrbitCycle.v`](../theories/OrbitCycle.v)
(Qed-closed; **axiom-free** — `Print Assumptions orbit_returns` = *Closed under
the global context*; no `Admitted` / `Axiom` / `Parameter`).

**Thread:** `extract_rings_valid` R5 — see
[`docs/extract-rings-proof-structure.md`](extract-rings-proof-structure.md)
§5 step 2 (`face_walk_closed`), building on the `next`-bijection slices
([`docs/dart-next-injective.md`](dart-next-injective.md), slice 2d).

---

## Why this slice

The §9 crux of the DCEL route is **`face_orbit_finite`**: iterating the face
step `next ∘ twin` from a dart eventually **returns** to it, so a face boundary
is a finite closed walk. This slice isolates and proves the pure-combinatorial
heart of that fact, with **no geometry**:

> an **injective** self-map of a **finite** set, iterated, **cycles back** to
> its start.

Keeping it abstract makes it reusable and keeps the proof axiom-free; wiring it
to the concrete dart face step is the next slice.

## What's here

A `Section` over `f : A → A`, a finite list `S`, decidable equality on `A`, and
two hypotheses — `f` maps `S` into itself (`Hclos`) and is injective on `S`
(`Hinj`) — exactly the shape slice 2d established for `next`:

| lemma | content |
|---|---|
| `iter_in` | every iterate of a point of `S` stays in `S` — the orbit ⊆ `S`, hence **finite** |
| `iter_comp` | `iter (a+b) x = iter a (iter b x)` |
| `iter_inj_on` | each `iter n` is injective on `S` (composite of `S`-injective maps) |
| `iter_pigeon` | among `iter 0 d … iter |S| d` two indices coincide (pigeonhole into `S`) |
| **`orbit_returns`** | there is `n ≥ 1` with `iter n d = d` — the orbit is a genuine **cycle** |

Plus a reusable list lemma proved en route, `seq_map_dup`: if a `seq`-indexed
family has a repeat among its first `m` values, two distinct indices `< m` map
equal — proved by a clean induction (the fresh value either repeats an earlier
one, or the prefix already collides), avoiding any `~NoDup → index` extraction.

## The argument

`orbit_returns` is pigeonhole + injective cancellation: the `|S|+1` iterates
`iter 0 d … iter |S| d` all lie in the `|S|`-element set `S` (`iter_in`), so two
coincide — `iter i d = iter j d`, `i < j` (`iter_pigeon`, via `seq_map_dup` and
stdlib `NoDup_incl_length`). Since `iter i` is injective on `S` (`iter_inj_on`)
and `iter j d = iter i (iter (j−i) d)` (`iter_comp`), we cancel the common `iter
i` prefix to get `iter (j−i) d = d` with `j−i ≥ 1`.

## Deliberately deferred (slice 2f / the assembly)

- **the dart instantiation** — set `f := fun d ⇒ next (outgoing (dtip d) D)
  (twin d)` and discharge `Hclos`/`Hinj` from: `D` closed under `twin`
  (`darts_of_closed_under_twin`), each vertex fan `fan_ok`, slice 2d's
  `next_injective`, `twin_inj`, and `next_base` (distinct head vertices ⇒
  distinct images). Then `orbit_returns` gives `face_orbit_finite` directly.
- **`face_of`** as the closed dart walk, ⇒ `closed_chain` feeding
  `RingExtract.ring_of_chain` ⇒ the `ring_closed` /
  `ring_has_minimum_points` core of `valid_polygon`.

### Registry note

No `admitted-counterexamples.txt` entry: no `Admitted`. Additive and
axiom-free — asserts and weakens nothing about the existing pipeline.
