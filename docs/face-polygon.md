# Hole-free face → valid_polygon — `extract_rings_valid` R5, slice 3c

**Coq artifact:** [`theories/FacePolygon.v`](../theories/FacePolygon.v)
(Qed-closed; no `Admitted` / `Axiom` / `Parameter`; axioms = the allowlisted
classical-reals pair).

**Thread:** `extract_rings_valid` R5 — see
[`docs/extract-rings-proof-structure.md`](extract-rings-proof-structure.md)
§5 step 4, the capstone of slices 3a–3b
([`docs/face-chain.md`](face-chain.md), [`docs/face-ring-simple.md`](face-ring-simple.md)).

---

## Why this slice

`Overlay.valid_polygon` is

```coq
ring_closed (outer) /\ ring_simple (outer) /\ ring_has_minimum_points (outer)
/\ (forall h, In h (hole_rings) -> ... /\ hole_inside_outer (outer) h).
```

For a polygon with **no holes** (`hole_rings = []`), the last conjunct is
`forall h, In h [] -> ...` — **vacuously true**. So the analytic
`hole_inside_outer` residual does not arise, and slice 3b's
`face_ring_combinatorial_valid` already supplies the three outer-ring
conditions.

## What's here

```coq
Definition face_polygon D d n : Polygon :=
  mkPolygon (ring_of_chain (face_chain D d n)) [].
```

| theorem | content |
|---|---|
| **`face_polygon_valid`** | a `≥ 3`-dart face of a noded, well-formed arrangement, as a hole-free polygon, satisfies `Overlay.valid_polygon` |
| `face_polygon_valid_exists` | existence form: such a dart spawns *some* `valid_polygon` |

The proof destructs `face_ring_combinatorial_valid` (closed + min-points +
simple) and discharges the hole conjunct by `In hr [] → False`.

## Significance — first full `valid_polygon` from the DCEL machinery

This is the **first time the half-edge pipeline produces an actual
`Overlay.valid_polygon`**, fully `Qed`, end to end from a dart set:

> `darts_of` → angular order (`dir_lt`) → bijective `next` → orbit finiteness
> (`face_orbit_finite`) → closed chain (`face_chain_closed_chain`) →
> closed + min-points + simple ring → **`valid_polygon`** (hole-free).

It discharges the **combinatorial core of `extract_rings_valid` for the
hole-free case**. The 5–7 session DCEL rebuild that R5 had deferred is now a
landed, axiom-disciplined reality for hole-free faces.

## Deliberately deferred (the genuine residual)

- **hole nesting** — for faces *with* holes: the face-incidence tree
  distinguishing the outer ring from hole rings (§5 step 3), and the
  combinatorial half of `hole_inside_outer`;
- the **analytic** `hole_inside_outer` point-set containment (§4) — the only
  genuinely JCT-adjacent piece, shared with R3's H1 gap;
- re-defining `extract` itself to emit these face polygons and closing
  `extract_rings_valid` against the real pipeline input.

### Registry note

No `admitted-counterexamples.txt` entry: no `Admitted`. Additive — asserts and
weakens nothing about the existing pipeline.
