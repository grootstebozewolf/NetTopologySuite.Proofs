# Valid polygon with holes, modulo one analytic seam — R5 slice 3f

**Coq artifact:** [`theories/FacePolygonHoles.v`](../theories/FacePolygonHoles.v)
(Qed-closed; no `Admitted` / `Axiom` / `Parameter`; standard three-axiom
classical-reals base, introduces none of its own).

**Thread:** `extract_rings_valid` R5 — see
[`docs/extract-rings-proof-structure.md`](extract-rings-proof-structure.md) §4
("shrink the residual to a single analytic hypothesis") and §5 step 4,
generalising the hole-free slice 3c ([`docs/face-polygon.md`](face-polygon.md)).

---

## Why this slice

Slice 3c produced a `valid_polygon` for the **hole-free** case. This slice closes
the **combinatorial** assembly for the general (with-holes) case, achieving the
§4 goal precisely: every `valid_polygon` condition except `hole_inside_outer`
holds *by construction* of the face walks, so the entire remaining gap is that
one analytic predicate.

## What's here

| theorem | content |
|---|---|
| `polygon_valid_of_rings` | a polygon is `valid_polygon` once its outer ring is closed/simple/min-points and each hole is closed/simple/min-points **and** `hole_inside_outer` (i.e. `valid_polygon` as an assembly constructor) |
| `face_outer_polygon_valid` | when the **outer** ring is a face ring, its three conditions are automatic (slice 3b) — holes need only be valid-shape rings inside it |
| **`face_polygon_holes_valid`** | when the **holes** are also face rings (each from a `≥3`-dart returning face), *their* three conditions are automatic too — leaving **`hole_inside_outer` as the sole remaining input** |

```coq
Theorem face_polygon_holes_valid :
  forall D, arrangement_ok D -> pairwise_no_proper_cross D ->
    forall d, In d D -> forall n, (3 <= n)%nat -> iter (fstep D) n d = d ->
    forall hspecs : list (Dart * nat),
      (forall s, In s hspecs -> In (fst s) D /\ (3 <= snd s)%nat
                 /\ iter (fstep D) (snd s) (fst s) = fst s) ->
      (forall s, In s hspecs ->                            (* <-- THE sole analytic input *)
          hole_inside_outer (ring_of_chain (face_chain D d n)) (hole_ring_of D s)) ->
      valid_polygon (mkPolygon (ring_of_chain (face_chain D d n))
                               (map (hole_ring_of D) hspecs)).
```

Every hypothesis other than the `hole_inside_outer` line is combinatorial
(membership in `D`, a `≥3`-dart returning face — the orbit data from
`face_orbit_finite`).

## Significance — the residual is now a single predicate

Combined with the earlier slices, the combinatorial core of `extract_rings_valid`
is **fully assembled**:

> `darts_of` → angular order → bijective `next` → orbit finiteness → closed
> chain → closed + min-points + simple rings → **`valid_polygon`** — with the
> outer ring and every hole ring discharged by construction.

The lone remaining gap for the full theorem is:

1. **`hole_inside_outer`** — the point-set containment that a hole face lies
   inside the outer face. The **only** analytic seam, JCT-adjacent, shared with
   R3's H1 gap. (The orientation scaffolding of slice 3e is the combinatorial
   half of distinguishing which faces are holes.)
2. **rewiring `extract`** to emit these face polygons against the real pipeline
   input — structural.

### Registry note

No `admitted-counterexamples.txt` entry: no `Admitted`. Additive — asserts and
weakens nothing about the existing pipeline.
