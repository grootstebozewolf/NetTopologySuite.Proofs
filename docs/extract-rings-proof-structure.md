# `extract_rings_valid` — proof structure & plan (hole-topology route)

> **Status: PLAN ONLY.** No Coq in this document; no proof attempted yet.
> This captures, while the buffer hole-formation work is fresh, a route to
> the registered deferred proof `extract_rings_valid`
> (`theories-flocq/OverlayBridge.v`, `docs/admitted-deferred-proofs.txt`)
> that leans on the corpus's existing **bounded-complement-component**
> machinery and the **hole-count heuristic** rather than on a full DCEL
> rebuild. It extends — does not replace — the DCEL plan in
> [`docs/audit-phase3-milestone5.md`](audit-phase3-milestone5.md) §4.3 / §5.2.

---

## §1 The obligation

```coq
(* theories-flocq/OverlayBridge.v — Admitted, registered deferred *)
Lemma extract_rings_valid :
  forall (op : BooleanOp) (A B : Geometry),
    valid_geometry A -> valid_geometry B ->
    fully_intersected (noded_segments A B) ->
    forall poly, In poly (extract op (noded_labeled_graph A B)) ->
      valid_polygon poly.
```

`valid_polygon` (`theories/Overlay.v:268`) is the conjunction of four OGC
§6 conditions on the outer ring and every hole:

| condition | `Overlay.v` | character |
|---|---|---|
| `ring_closed` | 235 | **combinatorial** (first = last vertex) |
| `ring_has_minimum_points` | 262 | **combinatorial** (`4 <= length`) |
| `ring_simple` | 244 | **analytic** (no proper self-intersection in ℝ²) |
| `hole_inside_outer` | 256 | **analytic** (a hole vertex is `point_in_ring` the outer) |

The current `extract` (`theories/OverlayGraph.v:653`) is the naive
S2 form: `List.filter` the edges by `edge_in_result op`, then `flat_map`
the survivors' endpoints into **one** ring. It does *not* satisfy
`valid_polygon` in general (the flattened endpoint list is neither closed
nor simple, and collapses all faces into a single "ring").

## §2 Why this has been deferred

Two independently thesis-shaped sub-problems (audit-phase3-milestone5.md
§4.3, §5.2):

1. **Assembly.** Turn the unordered surviving-edge set into *ordered closed
   walks* = the face boundaries of the planar subdivision. The standard
   tools (DCEL traversal, or cyclic-order-around-vertex Euler walks) are
   not in the stdlib, and `TopologyGraph` stores edges unordered with no
   face/incidence data. The recorded estimate is a 5–7 session DCEL rebuild.
2. **Geometric validity.** `ring_simple` and `hole_inside_outer` are
   point-set / Jordan-curve facts, entangled with the absent JCT toolkit
   (the same gap as H1 in `overlay_ng_correct_conditional`).

## §3 The lever: the hole-formation / dissolving heuristic

[`oracle/buffer_hole_count.py`](../oracle/buffer_hole_count.py) computes
the hole count of a region by **rasterising it on a grid, flood-filling the
complement, and counting bounded components** (components that do not touch
the grid border). Its self-test encodes the non-monotonic C-shape law:

```
  d:   0.0  0.3  1.0  2.0  3.0  5.0  8.0
holes:  0    0    1    1    0    0    0     (mouth seals -> hole; pocket fills -> gone)
```

i.e. a hole **forms** when a concavity's mouth seals and **dissolves** when
the pocket fills — `0 → 1 → 0`.

The decisive observation for this plan: **"bounded component of the
complement" is already a corpus predicate.**
`theories/PointInRingTangents.v` ships

```coq
ring_complement r q        := ~ ring_image r q          (* off the edge skeleton *)
connected_in_complement r p q := exists path, ... stays in ring_complement
in_bounded_component r p   := exists M>0, reachable q stay within radius M
geometric_interior_stdlib p r := ring_complement r p /\ in_bounded_component r p
```

`buffer_hole_count` is the **computable, grid-discretised oracle for
`in_bounded_component`**: each bounded flood-fill component is a witness
that its points are `in_bounded_component`, and "touches the border" is the
refutation (an unbounded path to infinity). So the heuristic is not a proof
device by itself, but it (a) gives a RocqRefRunner-style **differential
oracle** for any executable ring/face extractor, and (b) tells us the right
**invariant** to prove: *the assembled bounded faces are in bijection with
the heuristic's bounded complement components.*

## §4 Reframing `valid_polygon`: combinatorial core vs analytic shell

Split the obligation along the table in §1.

- **Combinatorial core (target of this plan, tractable):** `ring_closed`
  and `ring_has_minimum_points` hold *by construction* of a face walk, and
  hole nesting can be stated **combinatorially** as a parity/winding
  relation on faces rather than as point-set containment.
- **Analytic shell (kept deferred / named):** the upgrade of combinatorial
  nesting to the point-set `hole_inside_outer`. Remains JCT-adjacent.

The win: discharge the core unconditionally, and shrink the residual to a
*single* analytic hypothesis (the combinatorial→point-set nesting bridge)
that is strictly smaller than today's whole-of-`valid_polygon` gap — and
that the heuristic validates empirically.

> **`ring_simple` resolved (`theories/RingSimple.v`).** Contrary to the
> first cut above, `ring_simple` is **not** the hard analytic residual — it
> is **delivered by the noder**: `ring_simple_of_subset` proves a ring whose
> edges are drawn from a pairwise-non-properly-crossing (i.e. NODED)
> arrangement is `ring_simple` (instantiate with the snap-rounding noder's
> `fully_intersected` output). The *raw* offset is genuinely not simple
> (`not_ring_simple_bowtie`, a verified self-crossing counterexample — the
> hole-forming sealing mouth), which is precisely why the pipeline nodes
> before extracting. So the only remaining analytic residual is
> `hole_inside_outer`'s point-set half (= the H1/JCT gap of R3).

## §5 Proposed structure — half-edge faces + bounded-component invariant

A "DCEL-lite" that avoids re-doing M2's lemmas: keep `TopologyGraph` as is,
and define face walks as a *derived* notion.

1. **Half-edges.** For the surviving edge multiset, form directed
   half-edges (each undirected edge → two darts). `next` around a vertex =
   the cyclic successor by angle (`Azimuth.turn_sign` gives the comparison;
   no atan needed for a cyclic order via half-plane + cross-product sign).
2. **Face walk.** `face_of dart` = iterate `next ∘ twin`; a face is the
   orbit. **Targets (combinatorial, by induction on the orbit):**
   - `face_walk_closed`: every face orbit is a `ring_closed` ring.
   - `face_walk_min_points`: a bounded face orbit has `>= 4` vertices
     (a face of the fully-noded arrangement has no spurs).
3. **Bounded-face ↔ component invariant.** Prove the orbit-count /
   Euler relation `V - E + F = 1 + C` (C = connected components) so that
   **#bounded faces is determined combinatorially**, and connect a bounded
   face's interior points to `in_bounded_component` of its boundary ring.
   - `bounded_face_in_bounded_component`: a point strictly inside a bounded
     face orbit satisfies `in_bounded_component (face_ring) p`.
   This is the rung that the heuristic's flood-fill *counts*; the proof is
   a discrete reachability argument (no analytic JCT), mirroring the
   parity machinery already in `Overlay.ray_parity_odd` /
   `Overlay.point_in_ring`.
4. **`extract` re-defined** to emit `{ outer_ring := bounded-face-walk ;
   hole_rings := nested inner face-walks }`, with hole nesting read off the
   face-incidence tree (step 3), then `extract_rings_valid` becomes:
   composition of `face_walk_closed` + `face_walk_min_points` (core, Qed) +
   the residual analytic `ring_simple`/nesting bridge (named).

## §6 The tractable beachhead: specialise to **buffer**

The general overlay arrangement is arbitrary; the **buffer** offset curve
is not. For the buffer pipeline (`theories/BufferCorrectness.v`), the
output's hole topology is exactly the C-shape law the heuristic verifies:
holes are the pockets that *sealed but did not fill*. This is far more
structured than a generic two-geometry overlay.

**Proposal:** prove a buffer-specialised `extract_buffer_rings_valid`
first — it discharges the `H_valid` hypothesis of
`buffer_correct_conditional` for the buffer pipeline — using:
- the offset/join/cap geometry already Qed-closed
  (`BufferOffset`, `BufferJoin`, `BufferMiter`, `BufferBevel`,
  `BufferEndcap`): the raw curve's local structure is known exactly;
- the heuristic's hole law as the *specification* of which bounded faces
  survive (mouth-sealed-not-filled ⇒ hole), differentially tested;
- the §5 face machinery, but over the buffer curve's restricted topology
  (single input ring ⇒ at most the pockets as holes), where `ring_simple`
  of the offset is controlled by the parallel/limit results we already have
  (`offset_seg_parallel`, `miter_within_limit_iff`).

Closing the buffer case unblocks a real consumer (issue #65 / JTS#979)
without waiting on the fully-general DCEL + JCT.

## §7 Slice plan

| # | Slice | Ends in | Risk |
|---|---|---|---|
| R1 | Half-edge / dart layer + cyclic `next` via `turn_sign`; `face_of` orbit definition. | **✅ refined + LANDED** `theories/RingExtract.v` | low |
| R2 | `face_walk_closed`, `face_walk_min_points` (combinatorial, by orbit induction). | **✅ LANDED (Qed, axiom-free)** | low-med |

> **R1+R2 landed (`theories/RingExtract.v`, axiom-free).** Refinement: a
> *face walk is a closed chain of edges*, and `BufferAssembly` already
> produces such chains as concrete finite lists — so we take the face walk
> as a `closed_chain` (finite by construction, sidestepping the
> `face_orbit_finite` crux of §9) and extract its ring directly.
> `ring_of_chain` maps a chain to a `Ring`; `face_walk_closed` gives
> `ring_closed`; `face_walk_min_points` gives `ring_has_minimum_points` for
> ≥3 segments; `ring_edges_of_closed_chain` proves the ring's edges are
> **exactly** the chain (the faithful assembly↔ring bridge); `face_walk_core`
> bundles the three. This is the §6 buffer beachhead's combinatorial core.
> **Still open in R1:** ordering an *unordered* overlay edge set into chains
> (the dart/`next`/`turn_sign` assembly) — needed for the general (non-buffer)
> case. **Still the analytic shell (§4):** `ring_simple`, `hole_inside_outer`.
| R3 | `bounded_face_in_bounded_component` — discrete reachability ↔ `PointInRingTangents.in_bounded_component`. | **🟡 structure LANDED (Qed); geometric rung = named residual** `theories/BoundedComponent.v` | **med** (the heuristic's invariant) |

> **R3 split landed (`theories/BoundedComponent.v`, JCT-free).** The
> *component structure* the heuristic counts is now rigorous:
> `connected_in_complement` is an equivalence relation on the complement
> (`_refl`/`_sym`/`_trans`, via explicit reparametrisations — the path
> relation carries no continuity obligation, so this needs no analysis);
> `in_bounded_component` is a **component invariant** (`in_bounded_component_iff`
> — boundedness is constant on a connectivity class); and
> `not_in_bounded_component_intro` refutes boundedness from unbounded
> reachability (the tool for the OUTER face). So "bounded component" is a
> well-defined notion = what `buffer_hole_count.py` flood-fills.
> **The geometric rung stays the named residual:** that a point strictly
> inside an assembled face lies in a *bounded* class (the ring separates the
> plane into bounded inside / unbounded outside) is the Jordan-curve content
> — identical to `overlay_ng_correct_conditional`'s H1 / `point_in_ring` ↔
> `geometric_interior_stdlib`. It is carried as a downstream hypothesis (R6),
> **not admitted** (no new registry debt).
| R4 | Euler / face-count `V-E+F` relation; #bounded faces = heuristic component count (oracle bridge). | Qed + differential test | med |
| R5 | Re-define `extract` (or `extract_buffer`) to emit face-walk rings + nesting tree. | defs | low |
| R6 | `extract_buffer_rings_valid` = R2 ⊕ `ring_simple`; discharge `BufferCorrectness.H_valid`. | **✅ LANDED (Qed), hole-free unconditional** `theories/ExtractBufferRings.v` | med |

> **R6 landed (`theories/ExtractBufferRings.v`).** For the **hole-free**
> regime, `valid_polygon` is just its three outer-ring conditions, all now
> Qed: `valid_polygon_of_noded_chain` proves a hole-free polygon whose outer
> ring is a closed chain (≥3 segs) from a noded set is `valid_polygon`,
> **with NO Jordan-curve residual** (composes R2 `face_walk_core` + RingSimple
> `ring_simple_of_subset`). `H_valid_of_chain_extractor` lifts this to
> `BufferCorrectness`'s `H_valid` for any extractor meeting `chain_extractor_spec`,
> and `buffer_correct_hole_free` plugs it into `buffer_correct_conditional` —
> so for hole-free buffers the headline reduces to **just the semantic
> `H_bridge`**. The with-holes path (`valid_polygon_with_holes`) carries the
> `hole_inside_outer` clause as the single H1/JCT hypothesis (R3's residual).
| R7 | (stretch) general `extract_rings_valid`; or register the residual analytic shell as a *smaller* deferred entry. | **✅ analytic shell COMPLETED (Qed)** `theories/ExtractRingsShell.v` | high |

> **R7 analytic shell landed (`theories/ExtractRingsShell.v`).** The
> with-holes case no longer carries the whole per-hole conjunction as an
> opaque hypothesis. `hole_noded_chain_conditions` discharges a hole's
> `ring_closed` + `ring_simple` + `ring_has_minimum_points` from its being a
> noded closed chain (the same combinatorial + `ring_simple_of_subset` route
> as the outer ring), so `valid_polygon_noded_shell` reduces `valid_polygon`
> (outer + holes) to EXACTLY ONE analytic clause: the per-hole
> `hole_inside_outer` nesting. `H_valid_of_chain_extractor_holes` /
> `buffer_correct_with_holes` lift this to `BufferCorrectness.H_valid` and the
> end-to-end headline for the with-holes regime, modulo only that single
> JCT/nesting seam (R3's residual = H1 of `overlay_ng_correct_conditional`).
> The combinatorial core + `ring_simple` of the analytic shell are now Qed for
> outer rings AND holes alike; the only thing left of `extract_rings_valid`'s
> geometry is the point-set nesting bridge.

Each slice is independently `Qed`-able or ends in a documented, **smaller**
registered sub-deferred entry — never a silent stub. The combinatorial
core (R1–R2, R5) carries no analytic content and should close cleanly;
R3–R4 are where the heuristic earns its keep; R6 is the headline beachhead.

> **General-assembler progress (the "still open in R1" ordering piece).**
> The general overlay case — ordering an *unordered* edge set into chains —
> is now being built as its own sub-slices, since R1/R2 only ever consumed a
> pre-ordered `closed_chain`:
> - **R5 motivation (`theories/ExtractFlattenCounterexample.v`,
>   `docs/extract-flatten-counterexample.md`).** The naive `OverlayGraph.extract`
>   flatten is refuted: a closed triangle boundary given out of walk order
>   flattens to a non-closed ring (`extract_unordered_not_valid`), while the
>   walk-ordered trace through `ring_of_chain` is valid
>   (`ring_of_chain_traces_valid_shape`). So ordering is unavoidable.
> - **R5 slice 1 — dart foundation (`theories/Dart.v`,
>   `docs/dart-halfedge-foundation.md`), LANDED Qed.** The half-edge layer the
>   ordering runs on: `twin` (involutive/injective/fixed-point-free on proper
>   edges), `darts_of` (both orientations, closed under `twin`), the `outgoing`
>   fan + `vdeg`. Pure dart algebra; no geometry, no ordering yet.
> - **R5 slice 2a — angular comparator (`theories/DartAngularOrder.v`,
>   `docs/dart-angular-order.md`), LANDED Qed.** Orders the `outgoing v` fan
>   BY ANGLE without a materialised `atan2`: a half-plane + cross-product
>   (`Azimuth.turn_sign`) comparator `dir_lt`, proven a **strict total order**
>   on directions in general position (`dir_lt_irrefl/_asym/_trans/_total`, via
>   the pure-`ring` certificate `vcross_chain_cert` + `nra`), lifted to darts as
>   `dart_lt_*`. `dir_lt_total`/`dir_lt_trans` carry the general-position
>   (non-parallel) hypothesis the noded JCT seam supplies.
> - **R5 slice 2b — cyclic `next` (`theories/DartNext.v`,
>   `docs/dart-next.md`), LANDED Qed.** Reflects the slice-2a order into `bool`
>   (`dir_ltb`/`dart_ltb` + `*_spec` bridges), defines `list_min` and `next`
>   (minimal strictly-greater dart, wrapping to the global min at the fan
>   maximum), and proves it WELL-DEFINED: `next_in` (orbit closure), `next_base`
>   (stays at the vertex), `next_advances` (advances in angle). Minimal-successor
>   correctness, injectivity/permutation, and the `face_of` orbit are deferred.
> - **R5 slice 2c — `next` correctness (`theories/DartNextSpec.v`,
>   `docs/dart-next-spec.md`), LANDED Qed.** Under `fan_ok` (proper +
>   general-position fan), proves `list_min` a genuine lower bound (`fold_min_lb`
>   / `list_min_lb` -- the fold-minimum is correct under a strict total order)
>   and pins `next` down: `next_min_successor` (the minimal strictly-greater
>   dart) and `next_wrap_least` (global min on wrap). Injectivity/permutation and
>   the `face_of` orbit are deferred.
> - **R5 slice 2d — `next` injectivity (`theories/DartNextInjective.v`,
>   `docs/dart-next-injective.md`), LANDED Qed.** In a cyclic angular order each
>   dart has a unique predecessor, so `next_injective`: `next` is injective on a
>   `fan_ok` fan; and `next_surjective`: on a `NoDup` fan it is onto (injective
>   endo on a finite set via `NoDup_length_incl`), hence a CYCLIC PERMUTATION --
>   what makes the `face_of` walk a genuine cycle. The `face_of` orbit of
>   `next o twin` + its FINITENESS (§9 crux) is deferred.
> - **R5 slice 2e — orbit cycle / `face_orbit_finite` core
>   (`theories/OrbitCycle.v`, `docs/orbit-cycle.md`), LANDED Qed, AXIOM-FREE.**
>   The pure-combinatorial heart of `face_orbit_finite`, free of geometry: an
>   INJECTIVE self-map of a FINITE set, iterated, cycles back. For `f` mapping a
>   finite list `S` into itself and injective on `S`: `iter_in` (orbit ⊆ `S`,
>   finite), `iter_inj_on`, `iter_pigeon`, and `orbit_returns` (some `n >= 1`
>   with `iter n d = d`). Slice 2d gives these hypotheses for `next`;
>   instantiating `f := next o twin` (the dart face step) is slice 2f.
> - **R5 slice 2f — face step + FACE ORBIT FINITENESS
>   (`theories/DartFace.v`, `docs/dart-face.md`), LANDED Qed.** The §9 crux,
>   discharged. `fstep D d = next (outgoing (dtip d) D) (twin d)`; under
>   `arrangement_ok` (`D` twin-closed + every vertex fan `fan_ok`): `fstep_in`
>   (orbit closure), `fstep_inj` (injective -- equal images share a vertex,
>   reducing to slice-2d `next_injective` + `twin_inj`), and `face_orbit_finite`
>   = slice-2e `orbit_returns` instantiated at `f := fstep D`, so iterating the
>   face step from any dart RETURNS to it (a finite closed walk). Reading the
>   closed orbit off as a `closed_chain` / ring feeding `ring_of_chain` is the
>   remaining assembly.
> - **R5 slice 3a — face orbit -> closed chain -> ring
>   (`theories/FaceChain.v`, `docs/face-chain.md`), LANDED Qed.** The missing
>   link between slice-2f `face_orbit_finite` and `RingExtract.face_walk_core`:
>   `face_chain D d n = map (dbase,dtip) (dart_walk ...)`; `face_chain_ok`
>   (consecutive segments connect via `next_base`); `face_chain_closed_chain`
>   (the orbit return loops the chain shut -> `BufferAssembly.closed_chain`);
>   `face_closed_chain_exists` (every dart spawns a closed chain, via
>   `face_orbit_finite`); and `face_ring_valid_shape` (a >=3-dart face yields a
>   `ring_closed` + `ring_has_minimum_points` ring whose edges are exactly the
>   face segments). The combinatorial core of `valid_polygon`'s outer ring, now
>   for a GENERAL arrangement -- the DCEL assembly discharged end to end.
>   Remaining: hole nesting + the analytic `hole_inside_outer` residual (§4).
> - **R5 slice 3b — face ring is `ring_simple` (`theories/FaceRingSimple.v`,
>   `docs/face-ring-simple.md`), LANDED Qed.** A face segment `(dbase d, dtip d)`
>   IS the dart `d` (`Dart = Edge`), so `face_chain_subset`: every face edge is in
>   `D`; with `pairwise_no_proper_cross D` (noding), `ring_simple_of_subset` gives
>   `face_ring_simple`. `face_ring_combinatorial_valid` bundles `ring_closed` +
>   `ring_has_minimum_points` + `ring_simple` for a >=3-dart face -- THREE of the
>   four `valid_polygon` conditions, by construction.
> - **R5 slice 3c — hole-free face -> `valid_polygon` (`theories/FacePolygon.v`,
>   `docs/face-polygon.md`), LANDED Qed.** The FIRST full `Overlay.valid_polygon`
>   from the DCEL machinery. `valid_polygon`'s hole conjunct is vacuous when
>   `hole_rings = []`, so the analytic `hole_inside_outer` residual does not
>   arise; with slice-3b's three outer-ring conditions, `face_polygon D d n =
>   mkPolygon (ring_of_chain (face_chain D d n)) []` satisfies `valid_polygon`
>   (`face_polygon_valid`). The combinatorial core of `extract_rings_valid` for
>   the hole-free case, end to end. Faces WITH holes need hole nesting + the
>   analytic `hole_inside_outer` (§4).
> - **R5 slice 3g — the EXTRACT REWIRE (`theories/ExtractFaces.v`,
>   `docs/extract-faces.md`), LANDED Qed.** The §5-step-4 "extract re-defined",
>   wiring the face machinery to the pipeline: `result_edges`/`result_darts`
>   (`OverlayGraph.extract`'s `edge_in_result` filter, dart view);
>   `orbit_returns_bounded` (the pigeonhole bound `n <= length D` that
>   `OrbitCycle.orbit_returns` proves but does not export); `face_period`
>   (COMPUTABLE first-return search, pinned down by `face_period_spec`);
>   `extract_faces` (one hole-free face polygon per surviving dart -- face
>   walks instead of the refuted flatten); the headline `extract_faces_valid`
>   -- the OBLIGATION SHAPE of the deferred `extract_rings_valid` (`forall
>   poly, In poly (extract_faces ..) -> valid_polygon poly`), hole-free, NO
>   JCT residual, under the noder's three structural hypotheses (`fan_ok`
>   fans, `pairwise_no_proper_cross`, `no_short_faces`); and
>   `extract_faces_label_fidelity` (emitted rings trace ONLY op-kept edges).
>   Remaining: with-holes emission (nesting tree + the §4 analytic residual)
>   and discharging the three hypotheses from `fully_intersected`.
> - **R5 slice 3d — ring orientation primitive (`theories/RingOrientation.v`,
>   `docs/ring-orientation.md`), LANDED Qed.** The signed-area (shoelace)
>   orientation invariant for hole nesting: `signed_area2`; `signed_area2_app` /
>   `_rev` (order-invariant) / `_map_swap` (negated by endpoint swap) /
>   `_reverse_traversal` (walking a chain backwards negates the signed area --
>   the orientation flip); and `seg_twin_swap` (a dart's `twin` swaps its
>   segment), so the face across an edge is the orientation-reversed traversal --
>   the combinatorial seed of outer vs hole. The outer/hole classification and
>   the analytic `hole_inside_outer` containment are deferred (§4).
> - **R5 slice 3e — face orientation classification (`theories/FaceOrientation.v`,
>   `docs/face-orientation.md`), LANDED Qed.** Lifts slice-3d's signed-area
>   primitive to rings/faces: `ring_signed_area2` + `ring_ccw`/`ring_cw`
>   classifier (exclusive, trichotomy); `ring_signed_area2_of_chain` (a face
>   ring's area = its chain's); and the headline `twin_face_chain_signed_area` --
>   the face built from the TWIN darts walked in reverse has the NEGATED signed
>   area, so the face across each edge is oppositely oriented (the combinatorial
>   heart of outer vs hole). Deferred: the geometric meaning of the sign
>   (positive <-> encloses) and the analytic `hole_inside_outer` (§4).
> - **R5 slice 3f — valid_polygon with holes, modulo one analytic seam
>   (`theories/FacePolygonHoles.v`, `docs/face-polygon-holes.md`), LANDED Qed.**
>   `polygon_valid_of_rings`, `face_outer_polygon_valid`, and
>   `face_polygon_holes_valid` -- every `valid_polygon` condition except
>   `hole_inside_outer` holds by construction of the face walks; the residual is
>   now exactly that one analytic predicate (§4) plus the `extract` rewire.
> - **R5 `hole_inside_outer` — grounded status + concrete witness
>   (`theories/HoleInsideOuterExample.v`, `docs/hole-inside-outer.md`),
>   LANDED Qed.** A concrete unconditional witness (square hole inside square
>   outer, via the `ray_parity_odd` constructors + `lra`); the GENERAL discharge
>   is the registered JCT/H1 residual (`point_in_ring_correct_jct` the conditional
>   bridge; slice 3f takes `hole_inside_outer` as its sole hypothesis). See the
>   multi-beachhead route in `docs/hole-inside-outer-plan.md`.
> - **R5 analytic seam Stage B — rectangle `hole_inside_outer` (UNCONDITIONAL)
>   (`theories/HoleInsideOuterRect.v`, `docs/hole-inside-outer-rect.md`),
>   LANDED Qed.** Generalises the fixed-4x4 witness to ALL rectangles, with no
>   JCT hypothesis: `RectangleJCT.point_in_ring_rect_iff` characterises
>   `point_in_ring` for a rectangle as box-membership, and `hole_inside_outer` is
>   defined via `point_in_ring`, so `hole_inside_outer_rect` needs only a hole
>   vertex in the box. First non-toy discharge of the analytic seam; convex (C),
>   triangle (D), and the general JCT (E) remain.
> - **R5 analytic seam Stage A — conditional `valid_polygon` headline via the JCT
>   bridge (`theories/ExtractFacePolygonJCT.v`, `docs/extract-face-polygon-jct.md`),
>   LANDED Qed.** `hole_jct_witness`, `hole_inside_outer_of_witness`, and
>   `face_polygon_valid_via_jct` -- a face polygon with holes is `valid_polygon`
>   modulo only the named JCT predicate `parity_characterises_interior_cont_strict`
>   (matching `overlay_ng_correct_conditional` / `point_in_ring_correct_jct`).
> - **R5 analytic seam Stage C (opened) — convex instance
>   (`theories/HoleInsideOuterConvexExample.v`, `docs/hole-inside-outer-convex.md`),
>   LANDED Qed.** First convex instance beyond rectangles: a diamond (rotated
>   square) with SLANTED edges; `diamond_interior_point_in_ring` and
>   `hole_inside_outer_diamond`. Regression anchor; the GENERAL convex parity
>   characterisation (convex-chain monotonicity) remains substantial work.
> - **Next slices (deferred, higher risk):** the cyclic `next` = rotational
>   successor in `outgoing v` via `Azimuth.turn_sign`; the `face_of` orbit of
>   `next ∘ twin` and its **finiteness** (the `face_orbit_finite` crux of §9);
>   then face-orbit ⇒ `closed_chain` feeding `ring_of_chain`.

## §8 Oracle bridge (differential testing)

Extract the executable face/ring assembler (Coq → OCaml, RocqRefRunner
pattern) and test bounded-face counts against
`oracle/buffer_hole_count.py` on the C-shape family and the JTS#979
fixed-precision cases. Mismatch = a bug in the assembler *or* a too-coarse
grid (`res`); convergence under refinement is the acceptance gate. This
gives confidence in R5's definition *before* R6's proof, exactly as the
orientation / intersection lanes were de-risked.

## §9 Risks & decision points

- **Cyclic order without atan.** `next`-around-vertex needs a total cyclic
  order of darts. Use the half-plane split + `turn_sign` (cross-product
  sign) comparator — stays 3-axiom; avoid `Azimuth`/`atan2` to keep the
  combinatorial layer classic-clean. *Decision at R1.*
- **R3 is the crux.** If the discrete reachability ↔ `in_bounded_component`
  bridge resists (it is a small Jordan-flavoured argument), fall back to
  carrying it as the *named residual hypothesis* of R6 — still a strict
  shrink of today's gap, and the heuristic certifies it case-by-case.
- **`ring_simple` — RESOLVED (was thought analytic).** It is delivered by
  the noder, not by ℝ²-geometry: `RingSimple.ring_simple_of_subset` derives
  it from the noded arrangement's pairwise-non-crossing property
  (`fully_intersected`), and `not_ring_simple_bowtie` shows the raw offset
  is not simple (hence noding is required). No longer a residual.
- **Scope discipline.** Anything not `Qed` at the end of a slice is added
  to `docs/admitted-deferred-proofs.txt` as a *narrower* entry than
  `extract_rings_valid`, with its own section here.

## §10 References

- Obligation: `theories-flocq/OverlayBridge.v:extract_rings_valid`;
  `docs/admitted-deferred-proofs.txt`; `docs/audit-phase3-milestone5.md`
  §4.3, §5.2, §5.3.
- Reused predicates: `theories/PointInRingTangents.v`
  (`ring_complement`, `connected_in_complement`, `in_bounded_component`,
  `geometric_interior_stdlib`); `theories/Overlay.v`
  (`ring_edges`, `ray_parity_odd`, `point_in_ring`, `valid_polygon`,
  `ring_*`); `theories/OverlayGraph.v` (`extract`, `build_graph`);
  `theories/Azimuth.v` (`turn_sign`).
- Heuristic / oracle: [`oracle/buffer_hole_count.py`](../oracle/buffer_hole_count.py)
  (JTS#979 family).
- Consumer: `theories/BufferCorrectness.v:buffer_correct_conditional`
  (the `H_valid` hypothesis this would discharge for the buffer pipeline);
  buffer geometry `theories/Buffer{Offset,Join,Miter,Bevel,Endcap}.v`.

## §11 2026-06-05: status — combinatorial core complete; frontier = the JCT residual

A re-audit of this lane (R1–R7 all landed on `main`) shows the slice plan is,
for practical purposes, **mined out down to a single analytic obstruction**.
What is Qed-closed and what remains:

**Qed-closed (combinatorial + noder-delivered `ring_simple`), JCT-free:**
- R1+R2 face-walk core — `theories/RingExtract.v` (`ring_of_chain`,
  `face_walk_closed`, `face_walk_min_points`, `ring_edges_of_closed_chain`,
  `face_walk_core`).
- R3 *component structure* — `theories/BoundedComponent.v`
  (`connected_in_complement` equivalence; `in_bounded_component` invariant;
  `not_in_bounded_component_intro`).
- `ring_simple` — RESOLVED via the noder (`RingSimple.ring_simple_of_subset`
  + `not_ring_simple_bowtie`); not an analytic residual.
- R6 hole-free `valid_polygon` + `H_valid` + end-to-end
  `buffer_correct_hole_free` / `buffer_correct_hole_free_split` —
  `theories/ExtractBufferRings.v`, `theories/BufferBridge.v`. **No JCT.**
- R7 analytic shell — `theories/ExtractRingsShell.v`
  (`hole_noded_chain_conditions`, `valid_polygon_noded_shell`,
  `H_valid_of_chain_extractor_holes`, `buffer_correct_with_holes`): the
  with-holes case is reduced to EXACTLY ONE analytic clause.

**The single remaining residual (thesis-scale, JCT-gated):** the point-set
`hole_inside_outer` nesting bridge = R3's geometric rung = "a point strictly
inside a bounded face orbit lies in `in_bounded_component` of its boundary
ring". This is **the same theorem** as:
- `overlay_ng_correct_conditional`'s H1 (`OverlayCorrectness.v`);
- `parity_characterises_interior_cont` (`theories/JCT.v:398`);
- the `point_in_ring` ↔ `geometric_interior_cont` equivalence.

**Strategic consequence.** All of the corpus's remaining *general* headlines —
general `extract_rings_valid`, with-holes buffer, OverlayNG correctness —
**converge on this one polygonal-Jordan-Curve fact.** The hole-free buffer
headline is already unconditional. The combinatorial assembly that is still
JCT-free but unlanded is narrow:
- **R1-open:** ordering an *unordered* overlay edge set into closed chains
  (the dart / `next`-via-`turn_sign` machinery; `face_orbit_finite` is the §9
  crux). Needed only for the *general* (non-buffer) case.
- **R4:** the Euler `V − E + F = 1 + C` face-count relation (oracle bridge).

**Cost/risk update.** The recorded "5–7 session DCEL" estimate is largely
*spent*: the combinatorial core landed and the hole-free buffer consumer is
discharged. Remaining headline value in this lane is **JCT-gated** (the same
3–5-month topology piece tracked for #65), with R1-open / R4 as the only
incremental, JCT-free combinatorial work left — valuable for the general case
but not reaching a headline on their own.

### §11.1 update (2026-06-05): rectangle special case fully discharged

`theories/RectangleSeparation.v` closes the rectangle case **unconditionally**:
`rect_confines` (the box-separation residual of §2b) is now proved for
strict-interior points, so `rect_parity_characterises_interior` gives
`point_in_ring p ↔ geometric_interior_cont p` for axis-aligned rectangle
interiors with **no residual hypothesis**. Method: a single continuous scalar
field `box_min` (>0 inside, =0 on the edge skeleton, <0 outside) reduces the 2-D
separation to Stdlib's 1-D intermediate value theorem (a complement path avoids
the boundary, so `box_min` along it never vanishes and cannot change sign).
Three-axiom footprint. The *general* polygonal JCT seam remains the open
frontier for arbitrary rings; the rectangle is now a complete worked instance.

### §11.2 update (2026-06-10): arbitrary-triangle parity — RED on the queued spec

Continuing the special-case ladder toward `hole_inside_outer` (rectangle →
right triangle → arbitrary triangle), the arbitrary-triangle **separation** half
is done (`GeneralTriangleSeparation.gtri_interior_is_geometric`), and the parity
half was *reduced* to the named hypothesis `GeneralTriangleParity.gtri_parity_spec`
(`point_in_ring p ↔ 0 < gtri p`). `theories/GeneralTriangleParityRED.v` shows
that spec is **FALSE as stated** (`gtri_parity_spec_false`): the witness `(0,2)`
on the left edge of triangle `(0,0),(4,0),(0,4)` has `point_in_ring` true (the
ray test is **half-open** — left edge included, just like
`RectangleJCT.point_in_ring_rect_iff`'s `x0 ≤ px`) while `gtri = 0`. So `↔ strict
interior` is the wrong RHS. Corrected next GREEN: the half-open characterisation,
or the single TRUE downstream-useful direction
`0 < gtri p ∧ ray_avoids_vertices p (gtri_ring …) ⇒ point_in_ring p`
(the `ray_avoids_vertices` guard is itself necessary — a strict-interior point at
a vertex's height makes the ray graze it, cf.
`theories/JCT_VertexGrazingCounterexample.v`), composing to the triangle
hole-nesting headline `hole_inside_outer_triangle` (the analogue of
`HoleInsideOuterRect.hole_inside_outer_rect`).

### §11.3 update (2026-06-10): arbitrary-triangle hole nesting — GREEN

`theories/GeneralTriangleHoleNesting.v` lands the corrected GREEN. The true,
useful parity direction `gtri_band_in_ring` proves: for an interior-side point
(`0 < gtri p`) whose height lies in one of the three **directed edge bands**
(`ay<py<by_ ∨ by_<py<cy ∨ cy<py<ay`), `point_in_ring p (gtri_ring …)` holds.
Mechanism: with all three inward slacks positive, `edge_cross_sign` collapses
each edge's ray-crossing to exactly its directed band (the opposite slack-sign
disjunct is dead), and the bands are pairwise disjoint, so a point in one band
crosses *exactly one* edge → odd parity. The directed band is the triangle
counterpart of the rectangle's explicit `y0 < py < y1`. Composing with
`In p hole` gives `hole_inside_outer_triangle`, the arbitrary-triangle analogue
of `HoleInsideOuterRect.hole_inside_outer_rect` — an **unconditional** discharge
of `hole_inside_outer` for a triangular outer ring, with no JCT hypothesis. So
the special-case ladder now reads rectangle → right triangle → **arbitrary
triangle (done)** → general convex (the `convex_separation` engine awaits a
convex-n-gon consumer; the half-plane↔edge skeleton bridge is the next frontier).

### §11.4 update (2026-06-10): the band hypothesis discharged — guarded coverage + H1-seam iff

`theories/GeneralTriangleJCT.v` removes §11.3's explicit band hypothesis:
`gtri_ray_coverage` proves that `0 < gtri p` **plus the `ray_avoids_vertices`
guard** already places `py p` in one of the three directed bands, so
`gtri_interior_in_ring` needs interior positivity and genericity only.
Coverage is a 27-branch trichotomy over `py p` vs the three vertex heights:
the strict branches land in a band or die on the barycentric height identity
`gsB·(ay−py) + gsC·(by_−py) + gsA·(cy−py) = 0` (a `ring` consequence of
`g_sum`/`g_baryy`); in the equality (grazing) branches the guard forces the
grazed vertex strictly **west**, which factors the two adjacent slacks as
(height difference)·(vertex x − px) and orients the remaining heights — every
guard-consistent equality branch is one a band already covers, the rest are
`nra` contradictions. The guard is necessary at exactly the middle-vertex
height (cf. `JCT_VertexGrazingCounterexample.v`). No orientation hypothesis:
`0 < gtri p` forces `0 < gdbl` via `g_sum`.

Headlines: `general_triangle_parity_characterises_interior` (`point_in_ring ↔
geometric_interior_cont` for guarded strict-interior points — the **third fully
Qed-closed family** after the rectangle and right triangle on the H1 parity
seam) and `hole_inside_outer_triangle_guarded` (+ `_generic`: three height
disequalities discharge the guard) — hole nesting with no band bookkeeping,
closing the "assembly TODO" of Stage D (triangle) in
`docs/hole-inside-outer-plan.md`. Three-axiom; no `Admitted`.

### §11.5 update (2026-06-10): first with-holes valid_polygon (unconditional)

`theories/TriangleValidPolygon.v` composes §11.3's `hole_inside_outer_triangle`
into a concrete **`Overlay.valid_polygon` with a hole**, discharged with NO
Jordan hypothesis: `triangle_with_hole_valid` (outer triangle `(0,0),(6,0),(0,6)`,
hole `(1,1),(3,1),(1,3)`). All four OGC conditions hold for outer and hole; the
analytic `hole_inside_outer` clause — the residual that gated the with-holes
case of `extract_rings_valid` — is now unconditional for triangular outers. The
reusable ingredient `gtri_ring_simple` (a non-degenerate triangle ring is simple,
the `gtri_ring` analogue of `KakeyaOverlay.perron_tri_ring_simple`) supplies the
`ring_simple` conjunct for both rings. This is the first concrete `valid_polygon`
*with a hole* in the corpus whose analytic clause carries no named seam.

### §11.5b update (2026-06-14): the diamond — fourth total family, first convex assembly user

The H1 parity seam has since been carried to the corrected **off-ring** form
`parity_characterises_interior_cont_offring` (interior *and* exterior, off the
skeleton), made **total** (unconditional) for the rectangle
(`RectangleOffringSeam.v`), the general triangle (`GeneralTriangleOffringSeam.v`),
and the right triangle (`ConvexOffringSeam.v`); the generic convex assembly
`ConvexOffringSeam.convex_parity_seam_offring_of` reduces it for any
half-plane-presented ring to four presentation facts + two guarded-parity facts.

`theories/DiamondOffringSeam.v` lands the **fourth total family** —
`diamond_parity_seam_offring : forall p, parity_characterises_interior_cont_offring
p diamond_ring` — the **first convex four-gon** and the **first instantiation of
`convex_parity_seam_offring_of`**. The diamond `(0,-2),(2,0),(0,2),(-2,0)`
(the region `|x|+|y| <= 2`) is presented by its four edge half-planes
`diamond_hps`; the presentation obligations (zero-set of `conv_min` on the
skeleton, vertices in all half-planes, non-degeneracy, bounded positive region)
are mechanical, and the two guarded-parity obligations go through the already-Qed
monotone-chain split (`MonotoneChainParity.bimonotone_split_parity` over
`ConvexChainSplit.diamond_bimonotone`) + `GeneralTriangleParity.edge_cross_sign`:
a strict-interior point's rightward ray crosses the right (increasing) chain
exactly once, an exterior point's ray crosses the two chains both-or-neither.
`diamond_point_in_ring_iff_geometric` is the off-ring biconditional corollary;
three-axiom, no `Admitted`. A **general** convex *n*-gon remains open only on the
"split-from-convexity" derivation (`ConvexChainSplit.interior_hits_one_chain` /
`bimonotone_split` from `vertices_in_halfplane`) — isolated, not yet built.

### §11.5c update (2026-06-14): rung 3.5 — the bimonotone split, now general

`theories/MonotoneChainConstruction.v` removes the per-family hand-construction
of `bimonotone_split`. Until now every split was built by hand: the diamond
exhibits explicit `diamond_inc` / `diamond_dec` edge lists and proves
`bimonotone_split diamond_ring diamond_inc diamond_dec` by `reflexivity` over the
edge concatenation plus four `lra` height checks. The new file proves the split
**generically** from a purely combinatorial hypothesis on the *vertex list*:

```
Theorem bimonotone_split_unimodal :
  forall (up down : list Point) (apex : Point),
    y_strict_incr (up ++ [apex]) ->        (* heights rise strictly to the apex *)
    y_strict_decr (apex :: down) ->        (* then fall strictly back down      *)
    bimonotone_split (up ++ apex :: down)
                     (ring_edges (up ++ [apex]))
                     (ring_edges (apex :: down)).
```

The proof has three combinatorial pieces, all `Qed`: `ring_edges_app_shared`
(the skeleton of `l1 ++ m :: l2` is the skeleton of the closed prefix `l1 ++ [m]`
followed by the skeleton of the suffix `m :: l2`, joined at the shared vertex
`m`); and `chain_increasing_of_y_strict_incr` /
`chain_decreasing_of_y_strict_decr` (a strictly monotone vertex run yields a
monotone chain — connectivity `snd e = fst e2` is automatic because consecutive
`ring_edges` share their middle vertex). **Convexity is not used**: this isolates
exactly the combinatorial content of the split. The geometric implication
(convex `vertices_in_halfplane` ⟹ the vertex order is y-unimodal) and the dual
`interior_hits_one_chain` remain the open residual for a fully general *n*-gon.

The split obligation is thereby reduced to an **arithmetic** per-family check:
`diamond_bimonotone_via_unimodal` re-derives the diamond split in one
`apply` + two `cbn`/`lra` calls, and `hexagon_bimonotone` exhibits the split of a
genuinely convex CCW **hexagon** `(0,-3),(3,-1),(4,2),(1,3),(-2,1),(-3,-2)` with
no extra machinery — only the height comparisons change. Three-axiom, no
`Admitted`. This is the reusable substrate that makes the split of any future
convex family a one-liner; the remaining frontier is `interior_hits_one_chain`.

### §11.5d update (2026-06-15): rung 4 — the edge-halfplane algebraic bridge, `interior_hits_one_chain` closed

`theories/MonotoneChainCoverage.v` closes the `interior_hits_one_chain` residual for
any convex polygon family whose CCW inward half-planes are supplied in `hps`.

The **key algebraic identity** (`hp_slack_edge_inward_cross_product`, `ring` proof):

```
hp_slack (edge_inward_hp (mkPoint vx vy, mkPoint wx wy)) q
  = (wx - vx) * (py q - vy) - (wy - vy) * (px q - vx)
```

This is exactly the signed cross-product that `GeneralTriangleParity.edge_cross_sign`
uses to characterise `edge_crosses_ray`, yielding two algebraic bridge lemmas:

- `edge_up_crosses_iff_hp`: for an inc edge (vy < wy),
  `edge_crosses_ray q e ↔ (vy < py q < wy) ∧ (hp_slack (edge_inward_hp e) q > 0)`.
- `edge_dn_crosses_iff_hp`: for a dec edge (wy < vy),
  `edge_crosses_ray q e ↔ (wy < py q < vy) ∧ (hp_slack (edge_inward_hp e) q < 0)`.

A strictly-interior point has `hp_slack > 0` for ALL half-planes in `hps`
(`conv_min_pos_iff`), so:

- inc chain edges that straddle the ray height ARE crossed;
- dec chain edges that straddle are NOT crossed (hp_slack > 0 contradicts < 0).

The height-band coverage lemma `chain_increasing_straddles_y` (induction over
the monotone vertex list) guarantees that some inc chain edge straddles the query
height whenever `py bottom < py q < py apex`. Vertex-height avoidance (`py v ≠ py q`
for all vertices `v`) is derived from `ray_avoids_vertices` via the x-bound:
`hp_slack > 0` at height `wy` forces `px q < wx`, while `ray_avoids_vertices`
forbids `px q ≤ px v` at matching heights — a contradiction.

The **headline theorem** (`interior_hits_one_chain_of_edge_hps`) assembles these
pieces to deliver `chain_crossed q inc ∧ ¬ chain_crossed q dec` for any y-unimodal
ring under the edge-hp and ray-avoidance guards. Concrete validations:
`diamond_interior_chain_hit` and `hexagon_interior_chain_hit` discharge all
premises by `cbn`/`lra`. Three-axiom, no `Admitted`.

The convexity ⟹ y-unimodal vertex-order implication remains the only open residual
for a fully general convex *n*-gon.

### §11.5e update (2026-06-15): rung 5 — the convex hexagon, the fifth total family (n > 4)

`theories/HexagonOffringSeam.v` lands the CCW hexagon
`(0,-3),(3,-1),(4,2),(1,3),(-2,1),(-3,-2)` as the **fifth total off-ring JCT
family** and the **first convex polygon with more than four edges**. It is the
first family to consume rung 4, and it shows the rung-1…5 stack scales past four
edges with only an arithmetic per-family check.

The hexagon is presented by its six edge inward half-planes
(`MonotoneChainCoverage.hexagon_edge_hps`) and discharges the six obligations of
`ConvexOffringSeam.convex_parity_seam_offring_of`:

- **Presentation (1-4).** Zero-set on skeleton (six `Exists` cases, each giving
  the on-edge parameter `t` from the vanishing slack), vertices-in-half-planes,
  non-degeneracy, and a bounded positive region: the six slacks pin the point
  into the box `[-3,4] × [-3,3]` (linear combinations, `lra`), inside radius 5.
- **Interior-odd (5).** Now a near one-liner: from `0 < conv_min` the six slacks
  give the y-span `-3 < py q < 3` by `lra`, then rung 4's
  `hexagon_interior_chain_hit` yields "crosses the increasing chain once, misses
  the decreasing one", and `bimonotone_split_parity` turns that XOR into
  `point_in_ring`.
- **Exterior-even (6).** A six-edge per-band case analysis. From the bimonotone
  split a point with odd parity crosses exactly one chain; for each crossed chain
  edge its y-band fixes the unique straddling opposite-chain edge, and either all
  six slacks are forced nonnegative (so `0 ≤ conv_min`, contradicting
  `conv_min < 0`) or the two opposite straddling slacks are geometrically
  incompatible (`lra`). The four span-interior vertex heights (`y = -2, -1, 1, 2`)
  are excluded using `ray_avoids_vertices`, exactly as the diamond used the guard
  at `y = 0`.

Per-edge crossing is captured by six `gK_cross_iff` lemmas (`edge_cross_sign` +
`lra`), each in clean `(y-band, slack-sign)` form. Three-axiom, no `Admitted`.
The remaining open residual for a fully general convex *n*-gon is unchanged: the
convexity ⟹ y-unimodal vertex-order implication, plus a general (rather than
per-family) exterior-even — the latter needs the convex "between the two boundary
edges ⟹ inside" fact, which for a concrete polygon is a finite `lra`/`nra`
consequence of the explicit half-plane coefficients (as exercised here) but is
the genuine convex content in the general case.

### §11.6 update (2026-06-11): the extract rewire — `extract_faces` lands

`theories/ExtractFaces.v` closes §11's "R1-open" item (the §5-step-4
"`extract` re-defined"): the DCEL face machinery is now **wired to the
pipeline**. `extract_faces op g` filters `tg_edges g` by `edge_in_result op`
(exactly `OverlayGraph.extract`'s filter) and emits one hole-free face polygon
per surviving dart by walking `fstep` orbits — face walks instead of the
refuted flatten. The period of each orbit is **computed** (`face_period`, a
bounded first-return search justified by `orbit_returns_bounded` — the
pigeonhole bound `OrbitCycle` proves internally but does not export). The
headline `extract_faces_valid` has the obligation shape of the registered
deferred `extract_rings_valid` itself — `forall poly, In poly (extract_faces
op g) -> valid_polygon poly` — hole-free, **no JCT residual**, under the
noder's three structural hypotheses (per-vertex `fan_ok`,
`pairwise_no_proper_cross`, `no_short_faces`); and
`extract_faces_label_fidelity` proves the emitted rings trace ONLY op-kept
edges. Remaining in this lane: with-holes emission (nesting tree + the §4
analytic residual), discharging the three hypotheses from
`fully_intersected`'s concrete output, and R4. See
[`docs/extract-faces.md`](extract-faces.md).
