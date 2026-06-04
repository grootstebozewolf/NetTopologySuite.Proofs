# The buffer / noder pipeline — end-to-end seam map

> **Status (design doc, no proofs).** This document maps the JTS buffer
> operation, *end to end*, onto the corpus as it stands today. It names
> the exact `theories/` and `theories-flocq/` identifiers that already
> exist for each stage, marks what is **absent**, and specifies the
> target theorem shapes a future contributor would prove to land the
> pipeline. It introduces **no new `.v` content** and changes no proof.
> It is the buffer analogue of
> [`docs/hobby-theorem-proof-structure.md`](hobby-theorem-proof-structure.md)
> and the Phase 3 audit docs: "what the corpus has, what the precise gap
> is, what a future session needs to resume."
>
> **Headline finding.** The buffer operation is *not* a new pipeline. Its
> back three stages — **node → build labelled graph → extract rings** —
> are *exactly* the OverlayNG spine the corpus already ships
> (`snap_round_segments` → `build_labeled_graph` → `extract`, with the
> Qed-closed conditional headline `overlay_ng_correct_conditional`). What
> is genuinely buffer-specific is the **front**: offset-curve generation
> (parallel curves at distance `d`, joins, endcaps) and **depth
> labelling** in place of source labelling. So the work is "build a
> front-end that emits a segment list, then reuse the proven spine,"
> not "verify a second OverlayNG."
>
> The end-to-end headline is
> `theories/BufferCorrectness.v:buffer_correct_conditional` (mirroring
> `overlay_ng_correct_conditional`); see §3–§4. `H_valid` is discharged for
> hole-free buffers in `theories/ExtractBufferRings.v`, and `H_bridge` is
> decomposed into soundness/completeness in `theories/BufferBridge.v`.
>
> Drives issues
> [#65](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/issues/65)
> (buffer/offset curves) and
> [#66](https://github.com/grootstebozewolf/NetTopologySuite.Proofs/issues/66)
> (snap-rounding / noding / OverlayNG soundness), and is the formal
> counterpart of the heuristic hole-topology oracle
> [`oracle/buffer_hole_count.py`](../oracle/buffer_hole_count.py)
> (JTS#979 family).
>
> **Seams landed (Qed) so far.** S2 offset-segment soundness
> (`theories/BufferOffset.v`), S3 round-join corner-arc relation /
> Roadmap target 6 (`theories/BufferJoin.v`), S3 miter-join geometry —
> apex, limit cap, law-of-cosines, and the half-angle soundness link to
> `Azimuth` (`theories/BufferMiter.v` + `theories/BufferMiterAngle.v`,
> JTS#180), S3 bevel-join chord (`theories/BufferBevel.v`), S4 line
> endcaps — flat/round/square (`theories/BufferEndcap.v`, JTS#739/#1028),
> and S1 the end-to-end conditional headline
> (`theories/BufferCorrectness.v`) — all `Qed`-closed and kernel-verified
> under Rocq 9.1.1. Remaining seams (join/cap *edge-list* assembly, depth
> labelling, and the inherited DCEL / Hobby / JCT gaps) are tracked in
> §5–§6.

---

## §1 — The JTS buffer pipeline, end to end

JTS computes `Geometry.buffer(g, d)` as a fixed five-stage pipeline
(`BufferOp` → `BufferBuilder` → `OffsetCurveSetBuilder` /
`OffsetCurveBuilder` → `Noder` → `PolygonBuilder`):

```
            ┌──────────────────────────────────────────────────────────┐
  input g   │  STAGE 1  decompose to segments / curve segments          │
  + dist d  └──────────────────────────────────────────────────────────┘
                                   │ list of (curve)segments
                                   ▼
            ┌──────────────────────────────────────────────────────────┐
            │  STAGE 2  OFFSET-CURVE GENERATION  (buffer-specific)       │
            │   • parallel curve at signed distance d for each segment   │
            │   • JOIN at each vertex (round = arc, miter, bevel)        │
            │   • ENDCAP at each line end (round, flat, square)          │
            │   ⇒ a RAW, self-intersecting closed "buffer curve"         │
            └──────────────────────────────────────────────────────────┘
                                   │ raw offset edges (self-intersecting)
                                   ▼
            ┌──────────────────────────────────────────────────────────┐
            │  STAGE 3  NODING                       (REUSED from spine) │
            │   make every crossing an explicit vertex ⇒ fully noded     │
            └──────────────────────────────────────────────────────────┘
                                   │ noded, fully-intersected arrangement
                                   ▼
            ┌──────────────────────────────────────────────────────────┐
            │  STAGE 4  TOPOLOGY GRAPH + LABELLING    (spine + new label)│
            │   build graph; label each edge by DEPTH (inside/outside    │
            │   the d-offset region) instead of by source A/B            │
            └──────────────────────────────────────────────────────────┘
                                   │ labelled topology graph
                                   ▼
            ┌──────────────────────────────────────────────────────────┐
            │  STAGE 5  RING ASSEMBLY / RESULT       (REUSED from spine) │
            │   discard edges not in result; traverse faces ⇒ polygons   │
            └──────────────────────────────────────────────────────────┘
                                   │
                                   ▼
                           buffer(g, d) : Geometry
```

The **point-set specification** the whole pipeline must meet is Minkowski
dilation of the input by the closed disk of radius `d`:

```
  p ∈ buffer(g, d)   ⟺   ∃ q, point_set g q ∧ dist p q ≤ d        (d ≥ 0)
```

i.e. `buffer(g,d) = { p | dist(p, g) ≤ d }`. (`dist` is
`theories/Distance.v:dist`; the disk object itself is
`theories/Disk.v:Disk` / `in_disk`.) Negative `d` (erosion) is the
inward analogue and is **out of scope for the first landing** — see §6.

Two JTS structural realities the corpus is already aligned with:

- **The noder is the snap-rounding noder.** JTS's default buffer noder
  is `MCIndexNoder` + `IntersectionAdder`, but under a fixed
  `PrecisionModel` it snap-rounds — which is the path behind JTS#979
  ("buffer with fixed precision removes a hole"). The corpus's *only
  proven* noder is the Hobby snap-rounding noder
  (`snap_round_segments`), so the corpus naturally models exactly the
  fixed-precision buffer path that #979/#66 are about. The non-snapping
  `MCIndexNoder` path is not modelled (and is not needed for the
  fixed-precision soundness story).
- **The result is single-input.** Buffer takes one geometry and a
  distance, not two geometries and a boolean op. Stage 5's extract is the
  same, but the labelling rule (Stage 4) is a *depth* rule, not the
  `Union/Intersection/...` rule of `boolean_op`.

---

## §2 — Stage-by-stage seam map

Legend: ✅ Qed-closed and reusable · 🟡 present but partial / conditional
· 🔴 absent (must be built) · ⛓️ inherited gap (already registered).

| Stage | What it needs | Corpus status | Key identifiers |
|---|---|---|---|
| 1 decompose | input → segment list | ✅ | `OverlayGraph.extract_segments`, `polygon_to_pairs`; curve side `CurveGeometry.{CurveSegment,CurveRing,curve_segment_start/end}` |
| 2a offset @ d | parallel curve at distance `d` | 🔴 | *none* — `Direction.vperp`/`perpendicular`, `Disk.in_disk` are the raw material only |
| 2b joins | round/miter/bevel at corners | 🟡 | round-join central angle ✅ `BufferJoin.corner_arc_sweep_eq_turn(_unit)` (Roadmap target 6); miter apex + limit cap + half-angle ✅ `BufferMiter.*` / `BufferMiterAngle.miter_cap_iff_sin_half` (JTS#180); bevel chord ✅ `BufferBevel.bevel_length_sq_sin_half`; still no emitted join *edge lists* |
| 2c endcaps | round/flat/square at line ends | 🟡 | ✅ `BufferEndcap.*` — flat (`flat_cap_length_sq`/`_perp_edge`), round (`round_cap_endpoints_on_circle`/`_apex_on_circle`), square (`square_cap_extension`/`square_cap_corner_dist_sq`) defining geometry (JTS#739/#1028); still no emitted cap *edge list* |
| 3 noding | full noding of raw curve | ✅ | `HobbyTheorem_b64.snap_round_segments`, `fully_intersected`, `hobby_theorem_4_1_conditional` (✅, conditional on ⛓️ `hobby_lemma_4_3_no_proper`) |
| 4a graph | build topology graph | ✅ | `OverlayGraph.{build_graph,build_labeled_graph,TopologyGraph,valid_topology_graph}`, `valid_topology_graph_build_labeled_graph` |
| 4b labelling | **depth** label (in/out of d-region) | 🔴 | reshape of `OverlayGraph.{EdgeLabel,edge_in_result,merge_labeled_edges}` + `OverlayBridge.correct_labels` — buffer needs a depth/winding label, not `in_left/in_right` |
| 5 ring assembly | faces → valid polygons | ⛓️ | `OverlayGraph.extract`; correctness is `OverlayBridge.extract_rings_valid` (Admitted, registered deferred) |
| spec/JCT | point-in-result ⟺ interior | ⛓️ | `Overlay.{point_set,point_in_polygon,point_in_ring,valid_polygon}`; JCT seam `PointInRingTangents.geometric_interior_stdlib` (H1 named hypothesis) |

### 2.1 Stage 1 — decompose (✅ reusable)

`theories/OverlayGraph.v` already turns a `Geometry` into the
`list (Point * Point)` the noder consumes:

- `extract_segments : Geometry -> list (Point * Point)` via
  `polygon_to_pairs` (outer ring + holes → consecutive endpoint pairs).

The buffer front-end's Stage 2 must *produce* a `list (Point * Point)` in
the same shape so Stages 3–5 attach unchanged. For curve input the
decomposition is `CurveGeometry` →
`CurveSegment` (`CSChord`/`CSArc`); `curve_segment_start` /
`curve_segment_end` give the polyline skeleton the offset acts on.

### 2.2 Stage 2 — offset-curve generation (🔴 the real new work)

This is the buffer-specific front-end and the **largest gap**. Nothing in
the corpus today constructs an offset curve. What exists is *raw
material*:

- **Perpendicular direction** for the parallel-curve normal:
  `theories/Direction.v:vperp` (the `(−vy, vx)` rotation),
  `perpendicular`, `same_direction`, `opposite_direction`;
  `theories/Parallel.v:{seg_dir,seg_parallel,seg_perpendicular}`.
- **The disk** that defines the buffer point-set: `theories/Disk.v:Disk`,
  `in_disk`, `disk_is_valid`.
- **Join *decisions*** (which join, miter cap test) in
  `theories/Azimuth.v`: `turn_sign` (CCW/CW corner),
  `sin_half_turn` (half-angle for miter length), and `miter_ratio_le_iff`
  (the operational miter-limit cap `1 ≤ miterLimit · sin(θ/2)`).
- **Round-join / round-cap geometry** would reuse
  `CurveGeometry.CircularArc` plus `ArcLength.{arc_length,chord_subtended}`
  and `AngleBetween.angle_between` (the central/exterior angle of the
  corner arc — this is exactly Roadmap "Original target 6, buffer corner
  relations": *the arc of a convex corner has central angle = exterior
  angle*).

**Landed (Qed) — `theories/BufferOffset.v`:**

- `offset_seg : Point -> Point -> R -> (Point * Point)` — both endpoints
  translated by `d · unit_perp(seg_vec A B)`. Soundness proven, pure-ℝ,
  three-axiom footprint:
  - `offset_seg_dir` / `offset_seg_parallel` — the offset edge has the
    *same* direction vector as its source, hence is parallel (the
    property whose failure makes kinked flat-endcap / short-segment
    linework, JTS#739/#180).
  - `offset_point_dist` — each offset endpoint is at Euclidean distance
    `|d|` from its source endpoint.
  - `offset_perp_dist_to_line` — the offset endpoint's signed
    perpendicular distance to the *source line* is exactly `d`. This is
    the defining "offset at distance d" property.

**Still absent, must be defined and proven:**
- `corner_join : ... -> list (Point * Point)` — miter / bevel / round
  join edges between two consecutive offset segments, dispatched on
  `turn_sign` and `miter_ratio_le_iff`. **Soundness target:** the join
  fills the angular gap with points at distance `d` from the shared
  vertex (round join), or the miter point capped by the limit.
- `endcap : ... -> list (Point * Point)` — round/flat/square cap.
- `offset_curve : Geometry -> R -> list (Point * Point)` — assemble the
  raw closed buffer curve = offset segments ∪ joins ∪ caps.

For **curve-aware** buffer (issue #65 BUF-* producing `CurvePolygon`
output) the offset of an arc is another arc (concentric, radius `r ± d`);
that is strictly further out and rides on Option B — see §6.

### 2.3 Stage 3 — noding (✅ reusable, conditional on a registered gap)

The proven noder is consumed verbatim:

- Entry point `HobbyTheorem_b64.snap_round_segments :
  list (Point*Point) -> list (Point*Point)` (R-side discretiser `D_T`),
  with executable binary64 mirror `b64_passes_through_hot_pixel` /
  `b64_snap` (`HotPixel_b64.v`) gated by Liang–Barsky
  `b64_liang_barsky_touches`.
- The arrangement invariant `fully_intersected` and the preservation
  headline `hobby_theorem_4_1_conditional` (✅ Qed) — conditional on the
  per-pair lemma whose hard half, `hobby_lemma_4_3_no_proper`, is the
  registered deferred proof (`docs/admitted-deferred-proofs.txt`).
- **Directly relevant to #66/#979/#1133:**
  `PassesThrough_b64_spec_symmetric.b64_passes_through_hot_pixel_symmetric`
  proves the spec is order-independent — refuting the order-dependent
  noding behind "snapRoundingNoder on polygons → MultiLineString".
  `SnapRoundingScale_b64.v` lifts the grid to power-of-two scales (the
  fixed-`PrecisionModel` regime of the buffer bug).

Buffer reuses this with **zero change**: feed `offset_curve g d` where
overlay feeds `extract_segments A ++ extract_segments B`.

### 2.4 Stage 4 — graph + **depth** labelling (✅ graph, 🔴 label)

The graph machinery is fully reusable:

- `OverlayGraph.{TopologyGraph,build_graph,build_labeled_graph,
  valid_topology_graph}` with structural validity
  `valid_topology_graph_build_labeled_graph` (✅ Qed), lifted through the
  noder by `OverlayBridge.valid_topology_graph_noded_labeled_graph`
  (✅ Qed).

What differs is the **label**. Overlay labels an edge by *source* —
`EdgeLabel{in_left; in_right}`, with `edge_in_result op` dispatching on
`boolean_op`. Buffer must label by **depth**: which side of the edge is
*inside* the d-offset region (winding/depth count, JTS
`OffsetCurveSetBuilder` `addCurve(... leftLoc, rightLoc ...)` /
`SubgraphDepthLocater`). The required new pieces:

- a buffer edge label (a depth pair, or reuse `in_left/in_right` as
  inside/outside),
- `buffer_edge_in_result : <label> -> bool` — keep an edge iff exactly
  one side is interior (the result boundary), the depth analogue of
  `edge_in_result`,
- `buffer_correct_labels` — the depth analogue of
  `OverlayBridge.correct_labels` / `correct_labels_all_ops`.

The merge/canonicalisation infrastructure
(`merge_labeled_edges`, `merge_unique`, the `merge_in_left/right_*`
family) is reusable as-is; note the recorded orientation-canonicalisation
follow-up in `OverlayBridge.v §6` applies here too.

### 2.5 Stage 5 — ring assembly (⛓️ inherited deferred gap)

Identical to overlay:

- `OverlayGraph.extract : BooleanOp -> TopologyGraph -> Geometry`
  (naive edge-filter form today) and its validity obligation
  `OverlayBridge.extract_rings_valid` — **Admitted, registered** as a
  deferred proof; the real fix is DCEL face traversal. Buffer inherits
  this gap unchanged (a buffer-specific `extract` would still need the
  same DCEL ring assembly). The validity target is
  `Overlay.valid_polygon` (the four OGC §6 conditions: `ring_closed`,
  `ring_simple`, `ring_has_minimum_points`, `hole_inside_outer`).

---

## §3 — The reuse spine (why this is mostly assembly)

The OverlayNG headline already composes the back three stages:

```coq
(* theories-flocq/OverlayCorrectness.v — EXISTS, Qed-closed *)
Theorem overlay_ng_correct_conditional :
  forall (A B : Geometry) (op : BooleanOp) (p : Point),
    valid_geometry A -> valid_geometry B ->
    fully_intersected (noded_segments A B) ->
    (* H1 JCT *) (forall q r, ring_closed r -> ring_simple r ->
                    point_in_ring q r <-> geometric_interior_stdlib q r) ->
    (* H2 DCEL *) (forall op' g, valid_topology_graph g ->
                    valid_geometry (extract op' g)) ->
    (* H_bridge *) (forall g, valid_topology_graph g -> correct_labels op g A B ->
                    valid_geometry (extract op g) -> (...) ->
                    (point_set (extract op g) p <-> boolean_op op A B p)) ->
    point_set (extract op (noded_labeled_graph A B)) p <-> boolean_op op A B p.
```

`noded_segments` / `noded_labeled_graph` (`OverlayBridge.v`) are nothing
but `snap_round_segments` applied to `extract_segments`. The buffer
pipeline replaces the *input edge source* and the *label/spec*, and
keeps the rest:

| Overlay | Buffer counterpart |
|---|---|
| `extract_segments A ++ extract_segments B` | `offset_curve g d` (Stage 2, 🔴 new) |
| `boolean_op op A B p` | `buffer_spec g d p` (Minkowski dilation, §1) |
| `correct_labels op g A B` (source) | `buffer_correct_labels g d` (depth, 🔴 new) |
| `noded_labeled_graph A B` | `noded_buffer_graph g d` (🔴 thin new def) |
| `extract op g`, `extract_rings_valid` | same `extract`, same ⛓️ gap |
| H1 JCT, H_bridge | same shapes, single-input |

---

## §4 — Target headline theorem

The buffer analogue of `overlay_ng_correct_conditional`, stated for the
**linear** buffer (polygon/line input; round joins/caps chord-approxed),
single distance `d ≥ 0`:

```coq
(* TARGET — not yet in the corpus. theories-flocq/BufferCorrectness.v *)

(* Minkowski-dilation spec: the buffer is the d-neighbourhood of g. *)
Definition buffer_spec (g : Geometry) (d : R) (p : Point) : Prop :=
  exists q : Point, point_set g q /\ dist p q <= d.

Theorem buffer_correct_conditional :
  forall (g : Geometry) (d : R) (p : Point),
    valid_geometry g ->
    0 <= d ->
    (* H_offset (NEW, buffer-specific): the generated offset curve's noded
       arrangement has its boundary exactly the d-level set of g.  The
       load-bearing geometric content of Stage 2 (offset-at-d + joins +
       caps soundness), stated as a named hypothesis. *)
    offset_curve_sound g d ->
    (* H_node: the offset curve nodes to a fully-intersected arrangement
       (discharged by hobby_theorem_4_1_conditional once 4.3 lands). *)
    fully_intersected (snap_round_segments (offset_curve g d)) ->
    (* H_depth (NEW): depth labelling is correct on the noded graph. *)
    buffer_correct_labels (noded_buffer_graph g d) g d ->
    (* H1 JCT: point_in_ring captures topological interior (shared with overlay). *)
    (forall q r, ring_closed r -> ring_simple r ->
       point_in_ring q r <-> geometric_interior_stdlib q r) ->
    (* H2 DCEL: extract assembles valid polygons (shared ⛓️ extract_rings_valid). *)
    (forall g', valid_topology_graph g' -> valid_geometry (extract_buffer g')) ->
    (* H_bridge: on a valid, correctly depth-labelled graph, the extracted
       point-set is the d-neighbourhood (depth analogue of overlay H_bridge). *)
    (forall G, valid_topology_graph G -> buffer_correct_labels G g d ->
       valid_geometry (extract_buffer G) ->
       (point_set (extract_buffer G) p <-> buffer_spec g d p)) ->
    point_set (extract_buffer (noded_buffer_graph g d)) p <-> buffer_spec g d p.
```

Same epistemic shape as the existing conditional headlines: zero
`Admitted` in the body, gaps carried as **named Section/forall
hypotheses** (`offset_curve_sound`, `buffer_correct_labels`, the two
shared overlay gaps), instantiable when each piece lands. `Print
Assumptions` would show the README three-axiom set plus the Flocq
`Classical_Prop.classic` transitive pull inherited from
`snap_round_segments` (same Category-C footprint as `OverlayBridge.v`,
already covered by `docs/audit-exceptions.txt`).

---

## §5 — Gap inventory

**Buffer-specific (new work, 🔴):**

1. **Offset-curve generation** (§2.2): `offset_segment`, `corner_join`
   (miter/bevel/round via `Azimuth`), `endcap`, `offset_curve`, plus the
   soundness lemma `offset_curve_sound` (boundary = d-level set). This is
   the bulk of issue #65.
2. **Depth labelling** (§2.4): buffer edge label, `buffer_edge_in_result`,
   `buffer_correct_labels` — depth/winding analogues of the overlay
   source-labelling family.
3. **`buffer_spec` + `extract_buffer`** glue and the headline
   `buffer_correct_conditional` (§4).

**Inherited, already registered (⛓️ — buffer adds no new debt here):**

4. `hobby_lemma_4_3_no_proper` — noding preservation
   (`docs/admitted-deferred-proofs.txt`).
5. `extract_rings_valid` — DCEL ring assembly. **Largely dispatched for
   buffers:** `theories/ExtractBufferRings.v` discharges `H_valid` for the
   hole-free regime with NO JCT residual (`valid_polygon_of_noded_chain`,
   composing `RingExtract.face_walk_core` + `RingSimple.ring_simple_of_subset`);
   `theories/RingExtract.v` + `theories/BoundedComponent.v` + `theories/RingSimple.v`
   carry R1–R3. Only `hole_inside_outer` (with holes) remains = the H1/JCT gap.
6. JCT (H1) and the semantic `H_bridge` — carried as named hypotheses in
   the overlay headline; reappear identically here. `H_bridge` is now
   **decomposed** (`theories/BufferBridge.v`) into soundness (⊆ d-nbhd) +
   completeness (⊇ d-nbhd); `buffer_correct_hole_free_split` reduces the
   hole-free headline to exactly those two geometric directions (with
   `H_valid` discharged). The `buffer_spec` d-dilation algebra is proven there.
   The **soundness** direction is further pinned at the boundary-distance
   level in `theories/BufferBridgeSound.v` (Qed, three-axiom): the offset
   walls and bevel/round-join chords stay within `d` of the corner
   (`offset_point_within_d`, `bevel_chord_within_d` via `ball_convex`), while
   the miter apex escapes the corner's `d`-ball
   (`miter_apex_overshoots_vertex`, `dist_sq V apex = 2 d²` for the unit
   right angle, via the closed `miter_length_sq`) — the precise reason
   soundness needs a non-miter join or the miter limit. The residual is the
   short-edge / edge-segment-neighbourhood refinement (still in
   `buffer_extract_sound`).

**Registry implication.** No *new* `Admitted` is required to land the
conditional headline: like overlay, every gap is either a registered
deferred proof or a named hypothesis. Stage-2 soundness lemmas, when
attempted directly (not as a hypothesis), would each be ordinary
Qed-targets or — if a sub-step proves thesis-scale — new registered
deferred entries with their own proof-structure section.

---

## §6 — Suggested slice plan

Each slice is a session-sized unit ending in `Qed.` (or a registered,
documented `Admitted`). Ordering puts reusable/cheap wins first and
defers the thesis-scale geometry.

1. **S1 — spec + glue. ✅ LANDED (Qed), `theories/BufferCorrectness.v`.**
   `buffer_spec` (Minkowski dilation), concrete `offset_curve` (via
   `BufferOffset.offset_seg`), and `buffer_correct_conditional` composing
   the overlay graph spine with an abstract noder + extractor and the
   geometric gaps as named hypotheses (`H_valid`, `H_bridge`) — mirrors
   `overlay_ng_correct_conditional`. Plus `buffer_contains_input` and
   `buffer_spec_monotone`. Pure-ℝ, three-axiom footprint, no Admitted.
   **The end-to-end headline is landed.**
2. **S2 — offset segment soundness. ✅ LANDED (Qed), `theories/BufferOffset.v`.**
   `offset_seg` + parallelism (`offset_seg_dir`/`offset_seg_parallel`),
   distance-`|d|` (`offset_point_dist`), and perpendicular-distance-to-line
   (`offset_perp_dist_to_line`). Pure-ℝ, three-axiom footprint, no Admitted.
3. **S3 — joins.** Round-join corner-arc relation ✅ **LANDED (Qed),
   `theories/BufferJoin.v`** — `corner_arc_sweep_eq_turn` proves the
   arc's central angle (sweep between the offset normals) equals the
   exterior/turn angle between the edges, closing **Roadmap target 6**;
   `corner_arc_sweep_eq_turn_unit` reads it off the unit normals via
   `atan2_pos_scale`. **Miter-join apex** ✅ **LANDED (Qed),
   `theories/BufferMiter.v`** — `miter_apex` (Cramer's-rule intersection
   of the two offset lines) with `miter_apex_on_both_offsets` proving it
   sits at perpendicular distance `d` from *both* edge lines (JTS#180);
   `miter_length_sq` + `miter_within_limit_iff` give the exact,
   division-free / sqrt-free **miter-limit decision** (apex within cap
   `L·d` ⟺ scaled offset numerator within `L²·det²`), and `miter_length_sq_cos`
   the law-of-cosines form. **Miter-cap ↔ half-angle soundness** ✅
   **LANDED (Qed), `theories/BufferMiterAngle.v`** —
   `miter_numerator_sin_half` ties the offset numerator to
   `Azimuth.sin_half_turn(u, vneg w)`, and `miter_cap_iff_sin_half` proves
   the algebraic cap and the half-angle cap (`Azimuth.miter_ratio_le_iff`)
   decide the *same* predicate (3-axiom, `sin_half_turn` is sqrt-only).
   **Bevel-join chord** ✅ **LANDED (Qed), `theories/BufferBevel.v`** —
   `bevel_length_sq_dot` (law-of-cosines) and `bevel_length_sq_sin_half`
   show the bevel segment is `2·d·sin(θ/2)`, exactly the chord of the
   round-join arc (radius `d`, central angle = the turn). So round join
   (arc) and bevel join (chord) subtend the same angle at radius `d`.
   Still open in S3: the chord-approxed round-join / bevel *edge lists*
   (turning these lengths into emitted segment lists).
4. **S4 — endcaps. ✅ LANDED (Qed), `theories/BufferEndcap.v`.** Flat
   (diameter `2|d|`, perpendicular to edge), round (endpoints + apex on the
   radius-`d` circle about the line end), and square (corners extended `|d|`
   along the edge, `√2·|d|` from the end) cap geometry. 3-axiom, no Admitted.
5. **S5 — `offset_curve` assembly.** ✅ **Structural part LANDED (Qed),
   `theories/BufferAssembly.v`** — `assemble_open` / `assemble_closed`
   interleave offset walls with bevel joins, and the assembled boundary is
   proven a **closed chain by construction** (`assemble_open_chain`,
   `close_chain_closed`, `assemble_closed_closed`); `wall_parallel` ties each
   wall to its source edge. Round/miter joins replace the single `obevel`
   with a multi-segment insertion (the chain structure generalises). Still
   open: the *geometric* `offset_curve_sound` (boundary = the `d`-level set
   of the input) — the analytic half, carried by `H_bridge` in the headline
   and likely a registered deferred entry.
6. **S6 — depth labelling** (`buffer_correct_labels`), reusing the merge
   family; address edge-orientation canonicalisation
   (`OverlayBridge.v §6`).
7. **Inherited** — `hobby_lemma_4_3_no_proper`, `extract_rings_valid`,
   JCT close on their own tracks and discharge the shared hypotheses for
   both overlay and buffer at once. A concrete, hole-topology-based route
   for `extract_rings_valid` (with a buffer-specialised beachhead that
   discharges `H_valid` here) is planned in
   [`docs/extract-rings-proof-structure.md`](extract-rings-proof-structure.md).

**Out of first landing:** negative `d` (erosion / inward offset);
curve-aware buffer producing `CurvePolygon` arc output (Option A region
semantics — rides behind `arc_overlay_correct_chord_approx`'s deferred
`H_A_bridge`/`H_B_bridge`); single-sided buffer (JTS#178/#592).

---

## §7 — Relation to the issues and the hole-count oracle

- **#65 (buffer/offset curves, "Immediate")** — Stage 2 (§2.2) is its
  formal core; flat-endcap and miter bugs (JTS#739/#1028/#180) are
  endcap/join soundness (S3–S4).
- **#66 (snap-rounding/noding/OverlayNG, "Urgent")** — Stage 3 is already
  the proven snap-rounding noder; the symmetry result
  (`b64_passes_through_hot_pixel_symmetric`) and power-of-two scaling
  (`SnapRoundingScale_b64`) are the fixed-precision soundness levers.
- **JTS#979 ("buffer with fixed precision removes a hole")** — a
  *topological* (hole-count) buffer bug. The corpus's heuristic
  hole-topology oracle [`oracle/buffer_hole_count.py`](../oracle/buffer_hole_count.py)
  encodes the non-monotonic C-shape ground truth (0→1→0 holes as `d`
  grows). The formal counterpart is `buffer_spec` (§1) composed with the
  hole conditions of `valid_polygon` (`hole_inside_outer`,
  `ring_simple`): a *sound* extract preserves the hole structure of the
  d-neighbourhood, which is exactly what #979 violates under fixed
  precision. The oracle is the differential-test witness; the headline is
  the proof obligation.

---

## §8 — Placement and audit notes

- **`offset_curve` / joins / endcaps / `buffer_spec`** are pure-ℝ and
  belong in `theories/` (Stdlib-only), reusing `Direction`, `Azimuth`,
  `Disk`, `Distance`, `Overlay`, `OverlayGraph`. Only the binary64
  *executable* offset (if/when extracted, mirroring the `b64_*` compute
  modules) and anything depending on `snap_round_segments` land in
  `theories-flocq/`.
- **`BufferCorrectness.v`** (the headline) must sit in `theories-flocq/`
  because `noded_buffer_graph` consumes `snap_round_segments` (same
  placement constraint as `OverlayBridge.v` / `OverlayCorrectness.v`),
  and so inherits the `Classical_Prop.classic` Category-C footprint
  already enumerated in `docs/audit-exceptions.txt`. No new axiom; no new
  `Admitted` for the headline itself.
- Add new modules to `_CoqProject.full` (container build); the pure-ℝ
  Stage-2 modules may additionally go in the host `_CoqProject` if they
  avoid Flocq.

---

## References

- Corpus: `theories/Overlay.v`, `theories/OverlayGraph.v`,
  `theories-flocq/OverlayBridge.v`, `theories-flocq/OverlayCorrectness.v`
  (the reuse spine); `theories-flocq/HobbyTheorem_b64.v`,
  `HotPixel_b64.v`, `SnapRounding_b64.v`, `SnapRoundingScale_b64.v`,
  `PassesThrough_b64_spec_symmetric.v` (the noder);
  `theories/Direction.v`, `theories/Azimuth.v`, `theories/Disk.v`,
  `theories/Distance.v`, `theories/AngleBetween.v`,
  `theories/ArcLength.v`, `theories/CurveGeometry.v` (Stage-2 raw
  material).
- Docs: [`hobby-theorem-proof-structure.md`](hobby-theorem-proof-structure.md),
  [`audit-phase3-overlay.md`](audit-phase3-overlay.md),
  [`audit-phase3-milestone5.md`](audit-phase3-milestone5.md),
  [`audit-phase4-curves.md`](audit-phase4-curves.md),
  [`admitted-deferred-proofs.txt`](admitted-deferred-proofs.txt),
  [`audit-exceptions.txt`](audit-exceptions.txt).
- Oracle: [`oracle/buffer_hole_count.py`](../oracle/buffer_hole_count.py).
- Issues: #65 (buffer/offset curves), #66 (snap-rounding/noding/overlay);
  JTS#979, #739, #1028, #180, #1133, #752.
</content>
</invoke>
