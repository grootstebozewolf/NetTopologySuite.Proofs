# Ring orientation primitive — `extract_rings_valid` R5, slice 3d

**Coq artifact:** [`theories/RingOrientation.v`](../theories/RingOrientation.v)
(Qed-closed; no `Admitted` / `Axiom` / `Parameter`; rests on the standard
three-axiom classical-reals base — inherited via `R` arithmetic, introduces none
of its own).

**Thread:** `extract_rings_valid` R5 — see
[`docs/extract-rings-proof-structure.md`](extract-rings-proof-structure.md)
§5 step 3 (hole nesting), the orientation foundation beyond the hole-free case
([`docs/face-polygon.md`](face-polygon.md), slice 3c).

---

## Why this slice

After the hole-free case (slice 3c), the remaining piece of
`extract_rings_valid` is **distinguishing the outer ring from holes**. The
combinatorial handle is **orientation**: in a planar subdivision a bounded face
is traversed one way (positive signed area) and the face across each edge the
other way — and the face across an edge is reached by `twin`, which **reverses**
each segment.

This slice isolates the orientation invariant as pure shoelace algebra, with no
geometry beyond the signed-area cross product.

## What's here

```coq
Definition cross_pt (p q : Point) : R := px p * py q - py p * px q.
Definition swap_seg (e : Point * Point) : Point * Point := (snd e, fst e).
Definition signed_area2 (segs : list (Point * Point)) : R :=
  fold_right (fun e acc => cross_pt (fst e) (snd e) + acc) 0 segs.
```

| lemma | content |
|---|---|
| `signed_area2_app` | additive over concatenation |
| `signed_area2_rev` | invariant under reversing the segment order |
| `signed_area2_map_swap` | **negated** by swapping every segment's endpoints |
| **`signed_area2_reverse_traversal`** | walking a chain backwards (reverse order + swapped segments) negates the signed area — the orientation flip |
| `seg_twin_swap` | a dart's `twin` swaps its segment's endpoints — the DCEL link |

## The orientation flip

`signed_area2_reverse_traversal` is the headline: reversing a traversal —
`rev (map swap_seg segs)` — negates the signed area, because
`signed_area2_rev` says the *order* doesn't matter and `signed_area2_map_swap`
says swapping each segment's endpoints negates each `cross_pt` term (`cross_pt q
p = − cross_pt p q`).

`seg_twin_swap` ties this to the half-edge structure: `(dbase (twin d), dtip
(twin d)) = swap_seg (dbase d, dtip d)`. So the face across an edge (reached by
`twin`) walks the *orientation-reversed* segments — which, with the flip law, is
why **adjacent faces carry opposite orientation sign**: the combinatorial seed
of "outer boundary one way, holes the other".

## Note on axioms

This file uses real arithmetic (`cross_pt`), so — unlike the abstract
`OrbitCycle` core (slice 2e, genuinely axiom-free) — it rests on Rocq's standard
three-axiom classical-reals base (`functional_extensionality_dep`,
`ClassicalDedekindReals.sig_forall_dec`, `sig_not_dec`), the same set the rest of
the real-arithmetic corpus uses. It introduces no axioms of its own.

## Deliberately deferred

- the **outer/hole classification** itself — assigning a consistent orientation
  to a whole arrangement's faces and reading the sign as outer-vs-hole;
- the **analytic** `hole_inside_outer` point-set containment (§4) — the only
  genuinely JCT-adjacent piece, shared with R3's H1 gap;
- assembling faces-with-holes into a `valid_polygon` (the hole-free case is
  already done, slice 3c).

### Registry note

No `admitted-counterexamples.txt` entry: no `Admitted`. Additive — asserts and
weakens nothing about the existing pipeline.
