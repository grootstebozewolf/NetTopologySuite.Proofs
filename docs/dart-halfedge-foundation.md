# The half-edge (dart) foundation — `extract_rings_valid` R5, slice 1

**Coq artifact:** [`theories/Dart.v`](../theories/Dart.v)
(Qed-closed; no `Admitted` / `Axiom` / `Parameter`; axioms = the allowlisted
classical-reals decidability pair, inherited via `point_eq_dec`).

**Thread:** `extract_rings_valid` R5 — see
[`docs/extract-rings-proof-structure.md`](extract-rings-proof-structure.md) §5.

---

## Why this slice

The combinatorial core R1/R2 ([`RingExtract.v`](../theories/RingExtract.v))
deliberately **sidestepped** the half-edge layer: it takes a face walk as a
*pre-ordered* `closed_chain` (which the buffer assembler supplies directly), so
the buffer beachhead never needs to order edges. The proof-structure doc's own
note marks the still-open piece for the **general overlay** case:

> "ordering an *unordered* overlay edge set into chains (the dart / next /
> turn_sign assembly)."

[`ExtractFlattenCounterexample.v`](../theories/ExtractFlattenCounterexample.v)
(the R5 RED/GREEN) shows *why* this ordering is unavoidable: the naive flatten
emits non-closed rings; only a traced, walk-ordered chain is valid. **This slice
lays the dart layer that ordering will run on.**

## What's here — the dart algebra

A **dart** is a directed half-edge `base → tip`; each undirected edge yields two.

```coq
Definition Dart := (Point * Point)%type.
Definition twin (d : Dart) : Dart := (snd d, fst d).      (* reverse *)
Definition darts_of (E : list Edge) : list Dart := E ++ map twin E.
Definition outgoing (v : Point) (D : list Dart) : list Dart := (* fan at v *)
  filter (fun d => if point_eq_dec (dbase d) v then true else false) D.
```

| lemma | content |
|---|---|
| `twin_involutive` | `twin (twin d) = d` |
| `twin_inj` | `twin` is injective |
| `twin_neq_self` | a proper dart (base ≠ tip) is not its own twin — the two orientations are genuinely distinct |
| `dbase_twin` / `dtip_twin` | twin swaps base and tip |
| `darts_of_length` | `length (darts_of E) = 2 · length E` |
| `darts_of_closed_under_twin` | the dart set is closed under `twin` (the half-edge invariant `next ∘ twin` relies on) |
| `in_outgoing` | `d ∈ outgoing v D ↔ d ∈ D ∧ dbase d = v` |
| `outgoing_base` | every outgoing dart is based at `v` |

`vdeg v D := length (outgoing v D)` names the vertex degree the (future) cyclic
order rotates through.

## Deliberately deferred (the hard parts)

This slice is the *pure algebra* — no geometry, no ordering. The higher-risk
pieces come next, each its own slice:

1. **cyclic `next`** = rotational successor within `outgoing v` by
   `Azimuth.turn_sign` (the cross-product angular order; general-position
   dependent).
2. **`face_of`** = the orbit of `next ∘ twin`, and its **finiteness** — the
   `face_orbit_finite` crux flagged in §9.
3. **face orbit ⇒ `closed_chain`**, feeding `RingExtract.ring_of_chain` to close
   the general (non-buffer) `extract_rings_valid` via R2's `face_walk_core`.

So the dart layer is the foundation; the angular order and orbit finiteness are
where the real combinatorial work (and risk) lives.

### Registry note

No `admitted-counterexamples.txt` entry: no `Admitted`. This is additive
foundation — it asserts and weakens nothing about the existing pipeline.
