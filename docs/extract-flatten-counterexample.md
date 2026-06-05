# `extract`'s flatten is not a ring assembler — counterexample (R5)

**Coq artifact:** [`theories/ExtractFlattenCounterexample.v`](../theories/ExtractFlattenCounterexample.v)
(Qed-closed; no `Admitted` / `Axiom` / `Parameter`; axiom footprint = the
standard classical-reals pair pulled transitively through `R`).

**Thread:** `extract_rings_valid` R5 — see
[`docs/extract-rings-proof-structure.md`](extract-rings-proof-structure.md) §7.

---

## The stub

`OverlayGraph.extract` keeps the surviving edges and **flattens their endpoints
in edge-list order**, with no tracing, ordering, or closure:

```coq
let ring := flat_map (fun e => [fst (fst e); snd (fst e)]) filtered in
match ring with nil => nil | _ :: _ => [{| outer_ring := ring; hole_rings := [] |}] end
```

Its own header already warns this "is NOT, in general, `ring_simple` or
`ring_closed`". This file turns that warning into a Qed-closed refutation: the
stub violates the **conclusion** of the deferred `extract_rings_valid` obligation
(`forall poly, In poly (extract ...) -> valid_polygon poly`).

## RED — the stub emits invalid polygons

| witness | edge set | `extract Union` ring | fails |
|---|---|---|---|
| `extract_unordered_not_valid` | the triangle A,B,C given **out of walk order** `[(A,B);(C,A);(B,C)]` | `[A;B;C;A;B;C]` | `ring_closed` (head `A` ≠ last `C`) |
| `extract_single_not_valid` | a single edge `[(A,B)]` | `[A;B]` | `ring_has_minimum_points` (only 2 vertices) |

The first is the pointed one: the surviving edges form a **perfectly good closed
triangle boundary**, yet because flatten preserves edge-list order and duplicates
every endpoint, the emitted ring is the non-closed 6-vertex `[A;B;C;A;B;C]`. No
amount of validity in the *edge set* survives the flatten — tracing is required.

This is the ring-assembly analogue of
[`RingSimple.not_ring_simple_bowtie`](../theories/RingSimple.v): the raw input is
insufficient, so a real assembly step (R5) is required.

## GREEN — the fix is to trace

The same triangle, **walk-ordered** into a face walk and traced by
`RingExtract.ring_of_chain` (start-points + closing vertex), is the clean
4-vertex ring `[A;B;C;A]`:

```coq
Lemma ring_of_chain_tri_value : ring_of_chain tri_chain = [cA; cB; cC; cA].

Theorem ring_of_chain_traces_valid_shape :
  ring_closed (ring_of_chain tri_chain) /\ ring_has_minimum_points (ring_of_chain tri_chain).
```

proved directly from `face_walk_closed` / `face_walk_min_points` (R2, already
Qed). So the two combinatorial `valid_polygon` conjuncts the stub flatten loses
are recovered **for free** once the edges are walk-ordered — which is exactly what
R5 (face tracing via the DCEL `next`-around-vertex operator) must supply.

## What this pins for R5

R5's job is precisely the gap this witness exposes: **order the surviving edges
into per-face closed walks** before `ring_of_chain`. The combinatorial core
(R2, `RingExtract`), simplicity (`RingSimple`), and the buffer beachhead
(R6/R7, `ExtractBufferRings` / `ExtractRingsShell`) all already consume an
*ordered* chain; the missing piece is the general overlay edge-set → ordered-walk
step (the half-edge `next` operator, still greenfield per §5). This counterexample
is the formal statement of *why* that step cannot be skipped.

### Registry note

No `admitted-counterexamples.txt` entry: the file has no `Admitted`. It refutes a
property of the existing `extract` stub; it does not weaken or assume anything.
