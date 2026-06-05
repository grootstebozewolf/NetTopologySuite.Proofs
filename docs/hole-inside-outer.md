# `hole_inside_outer` — grounded status + concrete witness

**Coq artifact:** [`theories/HoleInsideOuterExample.v`](../theories/HoleInsideOuterExample.v)
(Qed-closed; standard three-axiom classical-reals base).

**Thread:** `extract_rings_valid` R5 — the final analytic seam (§4 of
[`docs/extract-rings-proof-structure.md`](extract-rings-proof-structure.md)).

---

## What `hole_inside_outer` actually is (grounded)

Reading the real definitions in `theories/Overlay.v`:

```coq
Definition hole_inside_outer (outer hole : Ring) : Prop :=
  exists p, In p hole /\ point_in_ring p outer.

Definition point_in_ring (p : Point) (r : Ring) : Prop :=
  ray_parity_odd p (ring_edges r).

Inductive ray_parity_odd (p : Point) : list Edge -> Prop := ...   (* a Prop, not a bool *)
with     ray_parity_even (p : Point) : list Edge -> Prop := ...
```

`edge_crosses_ray p (a,b)` is the concrete real-arithmetic upward/downward
crossing test. So `hole_inside_outer` is a **crossing-parity** statement, *not* a
separate topological "strictly inside" predicate.

### Corrections to the proposed routes

Earlier route sketches referenced primitives that **do not exist** in this
corpus, and should not be planned against:

| referenced | reality |
|---|---|
| `RayParity` module | none — `ray_parity_odd` lives in `Overlay.v` |
| `ray_parity_odd ... = true` | it is an **inductive `Prop`**, not a `bool` |
| `tangent_test`, `no_tangent_crossing`, `Inside` | not defined anywhere |
| `leftmost_vertex`, `on_ring` | not defined |
| "parity ⇒ strictly inside" bridge | this **is** the JCT — see below |

What *does* exist in `theories/PointInRingTangents.v`: the bounded-component
predicates (`ring_complement`, `in_bounded_component`,
`geometric_interior_stdlib`) and the **conditional** bridge

```coq
Theorem point_in_ring_correct_jct : ... ->
  (interior_pred p <-> Nat.odd (count_crossings_ray p r) = true) ->   (* H2: JCT, assumed *)
  (geometric_interior_stdlib p r <-> interior_pred p) ->              (* H3: assumed *)
  point_in_ring p r <-> geometric_interior_stdlib p r.               (* Qed, but conditional *)
```

i.e. the route already exists **in conditional form** — the JCT content
(parity ⟺ geometric interior) is a *named hypothesis*, not proven.

## The genuine residual

Discharging `hole_inside_outer` for *arbitrary* extracted faces requires the
unconditional **Jordan-curve / parity ⟺ interior** fact — the registered H1/JCT
analytic gap, shared across the corpus (`overlay_ng_correct_conditional`,
`point_in_ring_correct_jct`). It is **not** closeable by a quick combinatorial
slice, and is deliberately left as the analytic shell (§4). Slice 3f
(`FacePolygonHoles.face_polygon_holes_valid`) already takes `hole_inside_outer`
as its sole remaining hypothesis, so the combinatorial side is complete and the
gap is isolated to exactly this predicate.

## What this file delivers (honest, bounded)

A **concrete, unconditional** witness that the predicate is reachable: a 4×4
square `outer_sq` with a smaller square `hole_sq` sharing the centre `(2,2)`.

```coq
Lemma ctr_in_outer            : point_in_ring ctr outer_sq.
Theorem hole_inside_outer_example : hole_inside_outer outer_sq hole_sq.
```

`ctr_in_outer` walks the `ray_parity_odd` constructors: the rightward ray from
`(2,2)` skips the two horizontal edges and the far-left vertical edge, and
crosses the right edge exactly once (odd). Each `edge_crosses_ray` decision is a
real inequality closed by `lra` (vertical-edge intercept terms collapse to `0`
via two small helpers, keeping `lra` division-free).

This is a **regression anchor** (the parity predicate is satisfiable and behaves
as intended) and the concrete seed the general JCT generalises — nothing more is
claimed. No `Admitted`; it introduces no axioms of its own.

### Registry note

No `admitted-counterexamples.txt` entry: no `Admitted`. Additive — asserts and
weakens nothing about the existing pipeline.
