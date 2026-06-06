# Besicovitch–Kakeya Set Plan (Non-Dumb Version)

**Status:** Phase A landed (`theories/PerronStage.v`). Phases B–D are design only.
**Goal:** Add a finite, polygonal, DCEL-compatible Kakeya construction that fits
the existing corpus architecture without overclaiming measure-theoretic results
we do not yet have.

## 1. Philosophy

We do not attempt to prove the full Kakeya conjecture or that the set has
Lebesgue measure zero. We do build a concrete, finite-stage Perron tree that is:

- Polygonal and representable as `list Ring`
- Compatible with `OverlayGraph`, DCEL extraction, and ray-parity machinery
- A strong future regression anchor once Lebesgue measure theory is added

## 2. What the Corpus Can Already Do

- Finite unions of polygons (`Ring`, `OverlayGraph`, `FacePolygon`)
- Arbitrarily thin triangles with slanted/near-collinear edges
- Separation fields (`SeparationField.v`, `ConvexField.v`, `GeneralTriangleSeparation.v`)
- Guards (`ring_closed`, `ray_avoids_vertices`, `no_horizontal_edge_at`)
- Regression anchors (Spectre, Hat, Diamond, rectangles)

All of these are exactly the tools needed for a finite-stage Perron tree.

## 3. What the Corpus Cannot Do Yet

- Lebesgue outer measure / area tending to zero
- Countable intersections with measure-theoretic semantics
- Hausdorff dimension or Vitali-type covering arguments

Therefore we stay strictly finite and polygonal at every stage.

## 4. The Object to Formalise Now

**Finite-stage Perron tree**

```coq
perron_stage (n : nat) : list Ring
```

Each stage is a finite collection of triangles (each a `Ring`). The union
represents a polygonal approximation of the Kakeya construction at depth `n`.

Then define (future):

```coq
kakeya_stage (n : nat) : Point -> Prop := ⋃ (map ring_to_pointset (perron_stage n))
```

a finite union of polygonal point sets — fully compatible with the existing
machinery.

## 5. What We Can Prove at Each Finite Stage

For each `n`:

- Contains line segments in `2^n` distinct directions
- Bounded and closed
- DCEL-representable (can run `OverlayGraph`, `RingExtract`, `FaceChain`)
- Satisfies all existing guards (`no_horizontal_edge_at`, `ray_avoids_vertices`)
- Ray-parity and orientation tests remain well-defined

## 6. Long-Term Plan (4 Phases)

- **Phase A — Polygonal Perron tree.** Implement `perron_stage` and prove
  structural invariants + direction coverage. **Landed** in
  `theories/PerronStage.v` (see below).
- **Phase B — DCEL integration.** Represent each stage as a face-walk in the
  overlay DCEL and lift it to OGC validity. **Landed** in
  `theories/KakeyaOverlay.v` (see below).
- **Phase C — Regression anchors.** Freeze `perron_stage 5` (or similar) as a
  `Qed`-closed example with tests for near-collinearity, tiny angles, and
  overlapping triangles. **Landed** in `theories/KakeyaExample.v` (see below).
- **Phase D — Future measure theory.** Once Lebesgue measure is in the corpus,
  prove area → 0 and finally define the infinite intersection with measure zero.

## 7. Proposed Module Layout

The corpus keeps `theories/` flat, so the Phase-A module landed as
`theories/PerronStage.v` (registered in `_CoqProject.full`, the Overlay-dependent
lane). Future phases:

- `PerronStage.v` — finite polygonal stages **(landed)**
- direction-coverage proofs — folded into `PerronStage.v` for now
- DCEL integration — future (`OverlayGraph` of a stage)
- a fixed regression anchor, e.g. stage 5 — future
- measure-theory stubs — future

All files stay `Qed`-closed within the three-axiom footprint.

## 8. Why This Plan Is Not Dumb

- It respects the current architectural limits (no measure theory yet).
- It produces immediately useful, finite, DCEL-compatible objects.
- It aligns with the existing regression-anchor philosophy (Spectre, Hat, Diamond).
- It sets up the exact scaffolding needed for the future measure-theoretic
  Kakeya proof.

## Phase A — what landed (`theories/PerronStage.v`)

The Phase-A object is the **elementary figure** of the Perron-tree construction:
the apex-fan over a unit base. With apex `(1/2, 1)` over the base
`[0,1] × {0}`, stage `n` subdivides the base into `2^n` equal pieces and forms
sub-triangle `k` as `(apex, B_k, B_{k+1})` with `B_k = (k / 2^n, 0)`, each
packaged as a closed `Ring` `[apex; B_k; B_{k+1}; apex]`.

This is the figure the Perron-tree area reduction *starts from*; the
area-reducing translations (the actual "tree") and the area → 0 analysis are
Phase D and are **not** claimed here.

Proved at every finite stage `n`:

| Result | Statement |
|---|---|
| `perron_stage_length` | the stage has exactly `2^n` triangles |
| `perron_stage_rings_valid` | every triangle is `ring_closed` and `ring_has_minimum_points` (so the DCEL / ray-parity machinery applies) |
| `perron_tri_edges_count` | each triangle has 3 edges |
| `perron_tri_area` | signed area of sub-triangle `k` is `1 / 2^n` |
| `perron_tri_nondegenerate` | every sub-triangle is non-degenerate |
| `perron_stage_directions_distinct` | **direction coverage** — distinct sub-triangles carry non-parallel apex-rays, so the `2^n` triangles realise `2^n` pairwise-distinct directions |
| `base_pt_inj` | the base points (hence the rays) are genuinely distinct |
| `perron_stage_in_unit_square` | the whole stage lies in the closed unit square (bounded) |
| `perron_dir_translation_invariant` | Phase-D hook: the directions are invariant under the sliding translations the area reduction uses |

Direction coverage is the honest, finite, polygonal analogue of "contains
segments pointing in many directions": we prove the apex-ray cross product
`cross apex B_k B_j = (j − k) / 2^n` is non-zero for distinct indices, i.e. the
directions are pairwise non-parallel. No statement is made about *every*
direction in `[0, π)` or about measure — those require the limit and Lebesgue
theory of Phase D.

Pure-ℝ, three-axiom footprint, no `Admitted` / `Axiom` / `Parameter`.

## Phase B — what landed (`theories/KakeyaOverlay.v`)

Phase B connects the Phase-A triangles to the corpus's overlay-DCEL and OGC
validity machinery — **unconditionally**, with no analytic-shell hypothesis.

| Result | Statement |
|---|---|
| `perron_tri_closed_chain` | a triangle's edge list is a `closed_chain` (a DCEL face walk) |
| `perron_tri_chain_roundtrip` | `ring_of_chain (ring_edges (perron_tri n k)) = perron_tri n k` |
| `perron_tri_face_walk_core` | closure + min-vertex + edge-fidelity via `RingExtract.face_walk_core` |
| `sip_shared_no_cross` | two non-collinear segments sharing a vertex never intersect properly |
| `perron_tri_ring_simple` | **every triangle is `ring_simple`** (no proper edge crossings) — discharged outright |
| `perron_tri_valid_polygon` | each triangle, packaged hole-free, is an OGC `valid_polygon` |
| `perron_geometry_valid` | the whole stage, as a multi-polygon `Geometry`, is `valid_geometry` |

The key novelty over the general buffer pipeline is that `ring_simple` — there
the post-noding "analytic shell" supplied as a hypothesis — is here **proved
unconditionally**, because the Perron triangles are concrete and non-degenerate:
their three edges pairwise share a vertex and, being non-collinear, cannot cross
at an interior point. Consequently a Perron-tree stage is a bona-fide
`valid_geometry`, a legitimate operand for `Overlay.boolean_op` and the
OverlayNG pipeline.

Pure-ℝ, three-axiom footprint, no `Admitted` / `Axiom` / `Parameter`.

## Phase C — what landed (`theories/KakeyaExample.v`)

A frozen regression anchor over the depth-5 stage (`perron_stage 5`, 32
triangles), exercising the machinery on the hard configurations the plan calls
out: thin near-collinear slivers, tiny apex angles, and overlapping triangles.

| Result | Statement |
|---|---|
| `kakeya_anchor_count` | the depth-5 stage is exactly 32 triangles |
| `kakeya_anchor_valid_geometry` | it is an OGC `valid_geometry` (Phase-B `perron_geometry_valid` at 5) |
| `kakeya_anchor_all_ring_simple` | every triangle is `ring_simple` |
| `kakeya_anchor_area` / `_area_pos` | every sub-triangle is a thin sliver of signed area exactly `1/32`, yet strictly positive (non-degenerate) — the near-collinear / tiny-angle stress |
| `perron_consecutive_share_cevian` | consecutive triangles share the apex cevian (opposite orientation) — the edge-to-edge overlap |
| `perron_area_decreasing` | the sliver area `1/2^n` strictly decreases with depth — the finite, polygonal shadow of the Phase-D `area → 0`, which itself needs Lebesgue measure and is **not** attempted here |

Pure-ℝ, three-axiom footprint, no `Admitted` / `Axiom` / `Parameter`.
