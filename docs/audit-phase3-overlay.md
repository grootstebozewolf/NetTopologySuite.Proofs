# Library audit: OverlayNG correctness for Phase 3

**Question.** To formalise a verified `OverlayNG_b64` (the boolean-op
overlay engine — union, intersection, difference, symmetric difference
over polygonal geometries), what does the Phase 3 correctness theorem
have to state, what's reusable from Phase 0/1/2 (landed and *planned*),
what would need to be vendored, and what is genuine new work?

**Decision driver.** The corpus invariant (no `Admitted` / `Axiom` /
`Parameter` outside the deferred-proof registry) makes "reuse" much
cheaper than "vendor", and "vendor" much cheaper than "build". Phase 3
is the second chokepoint where the bulk of the new work is
*combinatorial and topological* rather than *arithmetic* (Phase 2 was
the first). Phase 0/1 were about sign correctness of polynomial
expressions over binary64; Phase 2 quantises an arrangement onto an
integer grid; Phase 3 reasons about the planar topology induced by that
arrangement and lifts boolean operations through it.

**Read-only audit.** This is a documentation session. No Coq is touched.
The output is this document — a future contributor starting Phase 3
without this session's context should be able to read it and know
exactly what the correctness theorem must state, which corpus
infrastructure exists (and which is still pending in Phase 2), and
which four proof-chain links need to be built.

---

## 1. What OverlayNG does, and what the correctness theorem must say

**Input.** Two geometries `A`, `B` from the OGC SFA family (`Point`,
`LineString`, `Polygon`, `MultiPolygon`, and their multi-variants —
curves are out of scope per `docs/audit-phase4-curves.md`). A boolean
op `op ∈ {Union, Intersection, Difference, SymDifference}`.

**Output.** A geometry `G = OverlayNG(op, A, B)` such that:

1. `G` is a valid geometry (no self-intersections, properly closed
   rings, holes inside shells, no duplicate components).
2. The point set of `G` equals the set-theoretic boolean operation on
   the point sets of `A` and `B`:
   `points(G) = op(points(A), points(B))`.

### 1.1 The three-stage algorithm

OverlayNG (Davis 2020, JTS / NTS implementations) is a three-stage
pipeline:

**Stage 1 — Noding.** Find all intersections between input segments,
insert vertices at the intersection points. After noding, the
arrangement has the property that any two segments either are disjoint,
share an endpoint, or are identical — *no proper crossings*. This is
exactly what **Phase 2's snap-rounding noder** delivers.

**Stage 2 — Topology graph.** Build a planar graph from the noded
segment arrangement. Vertices are hot-pixel centres (post-snap); edges
are noded segment pieces. Each edge carries a label recording which of
`A` or `B` it came from and which side (left/right/on) of each input
geometry it lies on.

**Stage 3 — Result extraction.** Traverse the topology graph applying
boolean-op-specific labelling rules to select edges that belong to the
result, then reassemble those edges into output `Polygon`s,
`LineString`s, etc.

### 1.2 The Phase 3 correctness theorem (informal target)

```coq
Theorem overlay_ng_correct :
  forall (A B : Geometry) (op : BooleanOp),
    valid_geometry A ->
    valid_geometry B ->
    let G := overlay_ng op A B in
    valid_geometry G /\
    point_set G = boolean_op op (point_set A) (point_set B).
```

The exact statement waits on Milestone 1 (definitions of `Geometry`,
`valid_geometry`, `point_set`, `boolean_op`, `overlay_ng`). The
informal shape above is what those definitions have to support.

---

## 2. The four-link proof chain

The correctness theorem decomposes into four links along the algorithm
stages. Each link has a clear precondition and a clear postcondition;
the chain is what a future contributor builds, one link per milestone.

```
                  valid_geometry A, valid_geometry B
                                 ↓
   Link 1:  Snap-rounded noding produces a fully-intersected arrangement.
            (Hobby Theorem 4.1, applied to the segments of A ∪ B.)
                                 ↓
                 fully_intersected (snap_round_segments A B)
                                 ↓
   Link 2:  A fully-intersected snap-rounded arrangement builds into a
            well-formed planar topology graph.
            (Planar-graph theory; combinatorial.)
                                 ↓
                  well_formed (build_graph (snap_round ...))
                                 ↓
   Link 3:  The graph-building step assigns correct A/B/side labels to
            every edge.
            (Algorithmic; mechanical once representations are settled.)
                                 ↓
                          correct_labels op G
                                 ↓
   Link 4:  Result extraction over a correctly-labelled graph produces
            a valid geometry whose point set equals the set-theoretic
            boolean operation.
            (Set-theoretic; the thesis-shaped piece — see §5.)
                                 ↓
        valid_geometry (extract op G) ∧
        point_set (extract op G) = boolean_op op A B
```

**Where each link stands today:**

| Link | What it needs | Status |
|---|---|---|
| Link 1 | Hobby Theorem 4.1, snap-round-preserves-passes-through, snap-round-preserves-shared-hot-pixel | **Conditionally landed (PR #21).** `hobby_theorem_4_1_conditional` is Qed-closed in `theories-flocq/HobbyTheorem_b64.v`. Two supporting lemmas (`hobby_lemma_4_2`, `hobby_lemma_4_3`) are Admitted with deferred-proof entries; the conditional theorem takes the per-pair preservation as an explicit hypothesis. Phase 3 inherits Link 1 as a conditional black box. |
| Link 2 | Planar graph representation + soundness of graph-building from a noded arrangement | **Greenfield.** No corpus content. No turnkey Coq planar-graph library on the corpus's pinned Rocq 9.1.1 / Flocq 4.2.2 stack. |
| Link 3 | Label-assignment algorithm + soundness vs the geometric A/B/side relation | **Greenfield.** |
| Link 4 | Set-theoretic correctness — graph traversal extracts the right point set for each boolean op | **Greenfield.** This is the thesis-shaped piece (§5). |

Links 2–4 are entirely new work. Link 1 is in the corpus as of PR #21
(branch `claude/snap-rounding-correctness-8v1rz`), conditional on
`hobby_lemma_4_3` — Phase 3 inherits it as a conditional black box and
the conditionality flows through to `overlay_ng_correct`. Closing
`hobby_lemma_4_3` upgrades Link 1 (and therefore the headline) from
conditional to unconditional with zero Phase 3 work.

---

## 3. Corpus infrastructure: what Phase 3 can build on

This section distinguishes **landed** corpus content (currently
`Qed`-closed) from **planned** Phase 2 content that Phase 3 depends on.
Phase 3 cannot start Milestone 3 (Link 1+2 bridge) until the planned
Phase 2 milestones land — but Milestones 1 and 2 of Phase 3 (definitions
and graph representation) can start in parallel with Phase 2.

### 3.1 Landed: Phase 0 orient2d predicate chain

In `theories-flocq/Orient_b64_stage_d.v` and predecessors:

- `b64_orient_sign_stage_d_sound` — Stage D (Shewchuk expansion
  arithmetic) sign of the exact 2D cross-product determinant. Sound vs
  `cross_R_BP`. **Cited paper:** Shewchuk (1997), adaptive precision
  arithmetic.
- `b64_orient_sign_exact_sound` — full-precision exact path, used as
  the spec the filter chain is sound against.

In `theories-flocq/Orient_b64_expansion.v`:

- `b64_orient2d_expansion_sign_correct` — Piece 6, sign correctness of
  the expansion-arithmetic path under
  `b64_orient2d_expansion_safe`. Chains through the deferred
  `fast_expansion_sum_nonoverlap_shewchuk` (the single
  registry entry — see §3.5).

**Phase 3 role.** Every orientation test in the topology graph
(left/right side of an edge relative to a polygon ring, hot-pixel
centre side test against a noded segment, ring-traversal direction)
reduces to `b64_orient_sign_stage_d`. The integer-regime soundness
(`b64_orient_sign_filtered_sound_small_int`) applies directly because
snap-rounded vertices are integer-valued by construction.

### 3.2 Landed: Phase 1 intersection coordinates

In `theories-flocq/Intersect_b64_exact.v`:

- `b64_intersect_point_x` / `b64_intersect_point_y` — line-line
  intersection coordinates over `binary64`.
- `b64_intersect_point_x_forward_error` (and y-companion) — `K·eps`
  forward error bounds on the intersection coordinate under
  `intersect_point_inputs_int_safe`. **Cited paper:** Fortune and Van
  Wyk (1996), Section 4.1 static error bound framework; Figure 3
  operation counts.
- `HasIntersect_sound_BPoint` typeclass instance — packages the bound
  for downstream consumers.

**Phase 3 role.** Stage 1 noding needs intersection coordinates; Phase
1 supplies them with a bound. The bound feeds into the hot-pixel
containment test (Phase 2): a Phase-1-bounded intersection point lands
in *exactly one* hot pixel under the unit-grid scale, provided the
inputs are in the integer regime. Phase 3 doesn't touch this directly
once Phase 2 packages it; the dependency is via Link 1.

### 3.3 Landed: Phase 2 hot-pixel + passes-through foundations

In `theories/HotPixel.v` and `theories-flocq/HotPixel_b64.v` (Slices
1–11; 59 theorems, all `Qed`-closed; see
`docs/phase2-hotpixel-progress.md`):

- `b64_in_hot_pixel` + `b64_in_hot_pixel_sound` /
  `b64_in_hot_pixel_complete` — sound and complete decision for "does
  point P lie in hot pixel C" in the integer regime.
- `b64_liang_barsky_touches` — parameter-interval filter for
  "does segment `P0P1` touch hot pixel `C`". **Cited paper:** Liang and
  Barsky (1984), but only the algorithm is reused; the corpus's
  parameter-interval reformulation avoiding `sign(c1−c0)` case splits
  is the corpus's own work, see Slice 10 in
  `docs/phase2-hotpixel-progress.md`.
- `b64_liang_barsky_complete` — complete vs the half-open touch
  relation (no false negatives — the noder-critical direction).
- `b64_liang_barsky_sound_closed` — sound vs the closed-pixel touch
  relation (conservative — over-nodes only on a measure-zero boundary
  set, safe for the noder).
- `snap_round` / `snap_round_coord` / `b64_snap` / `b64_snap_coord` —
  the snap operation, pinned to Flocq's
  `round radix2 (FIX_exp 0) (round_mode mode_NE)` /
  `Binary.Bnearbyint ... mode_NE` (round-half-to-even — the IEEE
  default and the mode used everywhere else in the corpus).
- `b64_snap_coord_B2R : B2R (b64_snap_coord x) = snap_round_coord (B2R
  x) 1` — *unconditional* `B2R`-equation (no finiteness side
  condition) via `Bnearbyint_correct`. **This is why no deferred-proof
  entry was needed for the snap operation itself.**
- `passes_through_hot_pixel` (R-side definition) — the segment touches
  the pixel **and** the snap-rounded segment still touches it.
- `b64_passes_through_hot_pixel` (b64 mirror).
- `b64_passes_through_complete` — bool fires whenever the half-open
  passes-through holds (noder-critical direction).
- `b64_passes_through_sound` — bool firing implies the closed-pixel
  passes-through (conservative direction).
- `snap_round_on_grid` — snapped coordinates land on the integer grid
  (`FIX_exp 0`).

**Phase 3 role.** Primitives consumed by Phase 2 Slices 12–13 and the
Hobby conditional theorem (§3.4), which package them into the Link 1
black box.

### 3.4 Landed (PR #21): Phase 2 Slices 12–13 + Hobby Theorem 4.1 conditional

PR #21 (`claude/snap-rounding-correctness-8v1rz`, four commits on top
of the Phase 2 hot-pixel foundations) closes Phase 2 Milestones 3 and 4
*core* and lands the Hobby Theorem 4.1 conditional. Three new files,
all `Qed`-closed where stated.

**`theories-flocq/SnapRounding_b64.v` — Slice 12, snap-rounding
algorithm correctness:**

- `snap_round_idempotent` — `snap_round (snap_round p 1) 1 = snap_round
  p 1`. Via Flocq's `round_generic` on an already-rounded value; this
  is the key insight that drives the rest of the slice.
- `snap_round_preserves_passes_through` (R-side) and
  `b64_snap_round_preserves_passes_through` (binary64) — *unconditional*
  preservation. The `passes_through_hot_pixel` definition already
  carries the snapped touch, so preservation reduces to snap
  idempotence. No `Znearest_IZR` machinery was needed.
- `b64_liang_barsky_touches_B2R_congr` — 6-coord `B2R`-level congruence
  for the Liang–Barsky filter. Avoids any float-level NaN/inf case
  analysis (the anticipated `b64_snap_preserves_lb` is not needed
  because the filter reads only `B2R`).
- `b64_snap_round_segment` — the per-segment snap operation; plus
  `b64_snap_round_segment_correct`.

**`theories-flocq/TopologicalCorrectness_b64.v` — Slice 13, topological
correctness core (Shape B):**

- `share_hot_pixel` / `b64_share_hot_pixel` — predicate: two segments
  share a hot pixel they both pass through.
- `snap_round_preserves_shared_hot_pixel` and
  `b64_snap_round_preserves_shared_hot_pixel` — Shape B preservation
  (the *provable* local kernel of the audit doc's
  share-point ⇒ shared-vertex conjunct).
- `b64_snap_round_preserves_pixel_cover` — whole-arrangement
  (`list (BPoint * BPoint)`) lift over a list of segments.
- **Shape A (exact `IntersectPoint` preservation) is false.** Snapping
  flips orientation signs (the very topology change Hobby's theorem
  bounds). The file header documents the precise gap to the full
  arrangement theorem.

**`theories-flocq/HobbyTheorem_b64.v` — Hobby Theorem 4.1 conditional:**

- `segments_intersect_properly` — interior crossing predicate
  (both `t` and `s` strictly in `(0, 1)`).
- `segments_intersect_only_at_endpoints` — Hobby's "intersect only at
  endpoints" relation.
- `fully_intersected` — arrangement invariant: distinct segments meet
  only at endpoints.
- `snap_round_segments` — Hobby's `D_T` operator, applied to a list
  of segments.
- `in_snap_region` — Hobby's `R⁻` (paper p.210–211), in
  closed-staircase form; the half-open boundary refinement is a
  resumption item per `docs/hobby-theorem-proof-structure.md` §7.
- `hobby_lemma_4_2` — **Admitted** (registered, 2–3 sessions).
- `hobby_lemma_4_3` — **Admitted** (registered, 4–6 weeks,
  thesis-shaped).
- `hobby_theorem_4_1_conditional` — **`Qed`-closed.** Takes the
  per-pair preservation as an explicit hypothesis (`Hlemma43`) and
  lifts it to the arrangement via `List.in_map_iff`.

**Companion doc.** `docs/hobby-theorem-proof-structure.md` — mirrors
`docs/shewchuk-theorem-13-proof-structure.md` (§1 theorem, §2 proof
structure, §3 Lemma 4.2, §4 Lemma 4.3, §5 corpus content, §6 precise
gap, §7 resumption checklist). The paper-specific numbering ("Theorem
4.1 / Lemma 4.2 / Lemma 4.3"), the page reference to the R⁻ convention
(p.210–211), and the proof sketches are taken from the maintainer's
verification of Hobby 1999 against the PDF; the session assistant for
PR #21 could not reach the PDF (network policy blocked the hosts) and
recorded that honestly in the file header. This audit doc adopts the
same provenance disclosure for any paper-specific claim.

**Phase 3 role.** This is exactly Link 1 of the proof chain. Phase 3
Milestone 3 (noding-to-graph bridge) cites
`hobby_theorem_4_1_conditional` directly. The conditionality
(`Hlemma43`) flows through Phase 3's headline as an explicit hypothesis
until `hobby_lemma_4_3` lands.

### 3.5 NOT YET landed: still pending for Phase 2

- **Bounded-displacement theorem.** "Every snapped vertex is within
  `√2 / (2r)` of its corresponding input feature." Per
  `docs/audit-phase2-snap-rounding.md` §2.5: "easier than topological
  consistency; mostly a triangle-inequality argument plus the
  hot-pixel definition", ~1–2 weeks. **Phase 3 impact:** none — Phase
  3's correctness theorem does not require displacement, only
  topological consistency.
- **Full topological correctness (Shape A — exact `IntersectPoint`
  preservation).** Slice 13's file header documents that Shape A is
  false as-stated, and what the full arrangement theorem would have to
  reformulate. Likely subsumed by closing `hobby_lemma_4_3`.
- **Iterated Snap Rounding (Halperin & Packer 2002).** Out of scope
  for Phase 3's correctness theorem.

### 3.6 Deferred-proof registry status

From `docs/admitted-deferred-proofs.txt` (post-PR-#21: **3 deferred-proof
entries** + 3 counterexample entries — 6 total registry entries):

- `theories-flocq/B64_FastExpansionSum_Shewchuk.v:fast_expansion_sum_nonoverlap_shewchuk`
  — Shewchuk Theorem 13. Cascade `pathA_chain` gap; structural
  framework landed (Route 2, see `B64_FastExpansionSum_Shewchuk_Route2.v`).
  Per the registry: "3–4 sessions of focused work" remaining.
  **Phase 3 impact:** indirect. The Stage D `orient2d` sign chain
  flows through this Admitted theorem. Closing it tightens Phase 3's
  foundation but is not on the critical path.
  **Cited paper:** Shewchuk (1997), Theorem 13.

- `theories-flocq/HobbyTheorem_b64.v:hobby_lemma_4_2`
  — Monotone-coordinate lemma. Pure real arithmetic; Flocq-independent.
  Per the registry: 2–3 sessions. Proof sketch:
  `docs/hobby-theorem-proof-structure.md` §3.
  **Phase 3 impact:** *indirect*. Closing Lemma 4.2 unblocks Lemma 4.3,
  which unblocks the unconditional Hobby Theorem 4.1 → which unblocks
  Phase 3 dropping the `Hlemma43` hypothesis. **Cited paper:** Hobby
  (1999), Lemma 4.2, p. 211.

- `theories-flocq/HobbyTheorem_b64.v:hobby_lemma_4_3`
  — Piecewise-linear ordering lemma; the CORE of Hobby's argument.
  Per the registry: 4–6 weeks, thesis-shaped. Proof sketch:
  `docs/hobby-theorem-proof-structure.md` §4.
  **Phase 3 impact:** *direct*. Closing Lemma 4.3 lets Phase 3 drop the
  `Hlemma43` hypothesis from `overlay_ng_correct` and ship the
  unconditional headline. **Cited paper:** Hobby (1999), Lemma 4.3,
  pp. 211–212.

**Phase 3 obligations unblocked per entry:**

| Deferred entry | Direct Phase 3 effect when closed |
|---|---|
| `fast_expansion_sum_nonoverlap_shewchuk` | Tightens Stage D `orient2d` foundation. No Phase 3 statement changes. |
| `hobby_lemma_4_2` | None — flows through Lemma 4.3 first. |
| `hobby_lemma_4_3` | Drops `Hlemma43` hypothesis from `overlay_ng_correct`. Headline becomes unconditional. |

The audit doc's earlier recommendation ("consider closing
`hobby_lemma_4_2` first") still stands: Lemma 4.2 is the cheaper of
the two (2–3 sessions) and is on the path to Lemma 4.3. Phase 3 work
on Milestones 1–4 does not depend on either lemma closing.

---

## 4. Missing concepts: what Phase 3 has to build

### 4.1 `Geometry` and `valid_geometry`

OGC SFA §6 defines validity for `Polygon` / `MultiPolygon`:
- All rings are closed (first point = last point).
- Rings do not self-intersect.
- Shell and holes do not cross.
- Holes are interior-disjoint and inside the shell.
- No duplicate points except for the closing point.

```coq
(* Sketch — exact definition is Milestone 1's deliverable *)
Inductive Geometry : Type :=
  | GPoint        : BPoint -> Geometry
  | GLineString   : list BPoint -> Geometry
  | GPolygon      : Ring -> list Ring -> Geometry  (* shell + holes *)
  | GMultiPolygon : list (Ring * list Ring) -> Geometry.

Definition valid_geometry (g : Geometry) : Prop := ...
```

**Scope.** Definition + decidability + structural lemmas:
~1–2 sessions. No Coq library known to ship this directly on the
corpus's pinned stack (the closest formalisations — e.g. CGAL — are
C++).

**Reference.** OGC Simple Features Access (ISO 19125-1), §6 — the
authoritative validity model. (Not separately cited in §7 because it
is a standards document, not a paper provided in this engagement; the
audit doc names it as the design reference, and Milestone 1 will
re-cite from primary text rather than from this audit.)

### 4.2 `point_set` and `boolean_op`

The *specification* against which the algorithm is verified.

```coq
Definition point_set (g : Geometry) : (BPoint -> Prop) := ...

Definition boolean_op
  (op : BooleanOp) (PA PB : BPoint -> Prop) : BPoint -> Prop :=
  match op with
  | Union        => fun p => PA p \/ PB p
  | Intersection => fun p => PA p /\ PB p
  | Difference   => fun p => PA p /\ ~ PB p
  | SymDiff      => fun p => (PA p /\ ~ PB p) \/ (PB p /\ ~ PA p)
  end.
```

**Scope.** Definition of `point_set` for `Polygon` is non-trivial —
point-in-polygon over `R²` (the corpus's `theories/Disk.v` and
`theories/Convex.v` have related machinery; a generic
non-convex-polygon membership predicate does not exist). ~2–3 sessions.

### 4.3 Planar topology graph

The intermediate data structure between Stage 1 (noding output) and
Stage 3 (result extraction).

```coq
(* Sketch *)
Record EdgeLabel := {
  el_from_A   : bool;
  el_from_B   : bool;
  el_side_A   : Side;  (* Left / Right / On / Undefined *)
  el_side_B   : Side;
}.

Record TopologyGraph := {
  tg_vertices : list BPoint;   (* hot-pixel centres *)
  tg_edges    : list (nat * nat * EdgeLabel);  (* index pairs into vertices *)
  tg_planar   : planar tg_vertices tg_edges;   (* invariant *)
}.
```

**Scope.** Definition + planarity invariant + ring-traversal
machinery: ~2–3 sessions. **No turnkey Coq planar-graph library** on
the corpus's pinned stack as of 2026-05 — mathcomp-analysis and
coq-community do not ship one. (Recommend a `general-purpose` agent
search at the start of Milestone 2 to re-confirm before committing to
"build" over "vendor".)

### 4.4 Labelling rules

Per-`op` predicates that decide whether a graph edge belongs to the
result. Mechanical once §4.3 is settled.

```coq
Definition belongs_to_result
  (op : BooleanOp) (e : EdgeLabel) : bool :=
  match op with
  | Union        => el_from_A e || el_from_B e
  | Intersection => el_from_A e && el_from_B e
  | Difference   => el_from_A e && negb (el_from_B e)
  | SymDiff      => xorb (el_from_A e) (el_from_B e)
  end.
```

**Scope.** Definition + soundness vs the side-relation: ~1–2 sessions.

### 4.5 Noding-to-graph bridge

The connection between Phase 2's snap-rounded segment arrangement
(unstructured list of segments) and Phase 3's topology graph
(planar structure with adjacencies).

```coq
(* Sketch *)
Theorem noding_produces_valid_graph :
  forall (segs : list (BPoint * BPoint)),
    fully_intersected (snap_round_segments segs) ->
    well_formed (build_graph (snap_round_segments segs)).
```

This is **Link 2** of the proof chain. It cites
`hobby_theorem_4_1_conditional` (PR #21, Phase 2's conditional
headline) as `fully_intersected`'s witness, carrying the `Hlemma43`
hypothesis forward.

**Scope.** ~4–6 sessions. The "build_graph" function itself is
straightforward to define; proving that the output is well-formed
(no parallel edges, no isolated vertices except those required, every
edge has two correct endpoints) is the work.

---

## 5. The thesis-shaped piece: Link 4 set-theoretic correctness

Links 1–3 are bridges between data representations (segments → noded
arrangement → topology graph → labelled graph). Link 4 is different:
it is the bridge between a *computational* object (the extracted
geometry from the labelled graph) and a *mathematical* object (the
set-theoretic boolean operation on the input point sets). This is
where Phase 3 is genuinely thesis-shaped.

### 5.1 What Link 4 has to prove

```coq
Theorem extract_correct :
  forall (op : BooleanOp) (G : TopologyGraph)
         (A B : Geometry),
    well_formed G ->
    correct_labels op G A B ->
    let result := extract op G in
    valid_geometry result /\
    point_set result = boolean_op op (point_set A) (point_set B).
```

The validity conjunct (`valid_geometry result`) reduces to
combinatorial properties of the extraction algorithm — every emitted
ring is closed, no two rings cross, holes nest correctly. Reasoning of
the same flavour as `valid_geometry` itself (§4.1).

The set-theoretic conjunct (`point_set result = boolean_op op ...`)
is the hard piece. It requires:

1. **A point set semantics for `TopologyGraph`** — every graph,
   restricted to edges that pass the labelling rule, must correspond
   to a definable subset of `R²` (or `BPoint`).
2. **Stability under hot-pixel snapping.** Two points that should be
   equal (geometrically — both at a shared intersection) but
   differ by `< √2/(2r)` are forced to the same hot-pixel centre.
   The set-theoretic argument must account for the resulting
   discrepancy between `point_set(A)` (over `R²`) and the
   integer-grid `point_set(result)`.
3. **A density / closure argument** showing that the symmetric
   difference between `point_set(extract op G)` and
   `boolean_op op (point_set A) (point_set B)` has measure zero
   (lives on hot-pixel boundaries). The corpus's
   `b64_liang_barsky_sound_closed` already over-nodes on a
   measure-zero boundary set — Link 4 inherits this and must show
   the over-noding does not change the *set* (modulo the boundary).

### 5.2 Why it's harder than Phases 0–2

Phases 0–2 are all *forward error / structural* arguments: a
predicate evaluated on `binary64` agrees with a predicate evaluated
on the exact real values, modulo a quantifiable error term. The
proofs decompose along the predicate's arithmetic structure.

Link 4 is a *set equality* argument over uncountable sets. It does
not decompose along arithmetic structure; it decomposes along
*topological* structure (interior, closure, boundary, connected
components). The corpus's `theories/` layer has `Convex.v`,
`Bbox.v`, `Disk.v` — none of which carry the closure / interior
machinery this link needs. Either:

- The corpus builds enough point-set topology to formalise the
  density argument (substantial — likely 4–6 sessions just for the
  topological-spaces scaffolding), or
- Link 4 is restated in a *pointwise* form ("for every `p` in
  `point_set result`, `p ∈ boolean_op op (point_set A) (point_set
  B)` modulo a hot-pixel-boundary equivalence") that sidesteps the
  set-equality machinery. This is the recommended route.

**Recommendation for Milestone 5.** Restate Link 4 pointwise from
the outset. The set-equality form is a corollary if needed, but the
pointwise form is what every downstream consumer (differential
testing, C# `OverlayNG_b64` mirror, application-layer overlay
calls) actually wants. Estimated effort with the pointwise
reformulation: 6–10 sessions.

---

## 6. Milestone structure

Five milestones in dependency order. As of PR #21, Link 1 is in the
corpus (conditional on `hobby_lemma_4_3`), so all five milestones can
start whenever Phase 3 work begins — there is no Phase 2 blocker on
Milestone 3 any more. The `Hlemma43` hypothesis threads through
Milestones 3–5 until `hobby_lemma_4_3` lands.

### Milestone 1 — Geometry types and specifications

**Deliverables.**
- `theories/Geometry.v` — R-side `Geometry` ADT, `point_set`,
  `valid_geometry`, `boolean_op`.
- `theories-flocq/Geometry_b64.v` — `binary64` mirror; `BPoint`-based
  geometries; integer-regime validity decidability.
- Statement of the headline theorem `overlay_ng_correct` (with
  `overlay_ng` itself stubbed for Milestone 1).

**Estimated effort.** ~3–4 sessions.
**Phase 2 dependency.** None. Can start now.

### Milestone 2 — Topology graph representation

**Deliverables.**
- `theories/TopologyGraph.v` — planar graph, edge labels,
  well-formedness invariants.
- `theories/PlanarGraph.v` — if no turnkey library is vendorable, the
  small graph-theory kernel the corpus needs.
- Decidable equality / structural induction lemmas.

**Estimated effort.** ~4–6 sessions.
**Phase 2 dependency.** None. Can start in parallel with Milestone 1.

**Vendor / build decision.** Before committing to build, spawn a
`general-purpose` agent to search `coq-community`, `mathcomp-analysis`,
`coq-extra-graph`, and the wider opam ecosystem for a planar-graph
library compatible with Rocq 9.1.1 and not pulling in mathcomp's
ssreflect tactic dialect (which the corpus does not depend on). If
nothing fits, **build minimally** — only the operations the corpus
needs (adjacency, ring traversal, planarity invariant).

### Milestone 3 — Noding-to-graph bridge (Link 1 + Link 2)

**Deliverables.**
- `theories-flocq/OverlayNoding_b64.v` — packages Phase 2's snap-round
  output into a `TopologyGraph`. Cites
  `hobby_theorem_4_1_conditional` (carrying the `Hlemma43` hypothesis
  forward).
- `build_graph_well_formed` theorem (Link 2).
- `build_graph_preserves_input_segments` theorem.

**Estimated effort.** ~4–6 sessions.
**Phase 2 dependency.** **Satisfied as of PR #21.**
`hobby_theorem_4_1_conditional` is `Qed`-closed in
`theories-flocq/HobbyTheorem_b64.v`. Milestone 3 can start as soon as
Milestones 1 and 2 land. The `Hlemma43` hypothesis must be threaded
through Milestone 3's theorems (and onward to the Milestone 5 headline)
until `hobby_lemma_4_3` lands and the conditional theorem becomes
unconditional.

### Milestone 4 — Labelling correctness (Link 3)

**Deliverables.**
- `assign_labels` algorithm + soundness against the geometric
  side-relation.
- `correct_labels` predicate + decidability.
- Per-`op` `belongs_to_result` soundness.

**Estimated effort.** ~2–3 sessions.
**Phase 2 dependency.** Through Milestone 3.

### Milestone 5 — Set-theoretic correctness (Link 4, the thesis piece)

**Deliverables.**
- `extract` function (graph → `Geometry`).
- `extract_valid` — output is a `valid_geometry`.
- `extract_pointwise_correct` — for every `p`, `p ∈ point_set
  (extract op G) ↔ boolean_op op (point_set A) (point_set B) p`
  modulo hot-pixel-boundary equivalence (see §5.2 recommendation).
- Corollary: the unconditional headline `overlay_ng_correct`,
  assembled from Milestones 1–5.

**Estimated effort.** ~6–10 sessions.
**Phase 2 dependency.** Through Milestone 3.

### Cumulative estimate

| Milestone | Sessions | Cumulative |
|---|---|---|
| 1 — Geometry types & specs | 3–4 | 3–4 |
| 2 — Topology graph | 4–6 | 7–10 |
| 3 — Noding-to-graph bridge | 4–6 | 11–16 |
| 4 — Labelling | 2–3 | 13–19 |
| 5 — Extraction & correctness | 6–10 | 19–29 |

**Total Phase 3 scope: ~19–29 sessions.** Comparable in size to
Phase 2 (4–7 months focused work per
`docs/audit-phase2-snap-rounding.md` §5). The thesis-shaped piece
(Milestone 5) dominates the scope.

---

## 7. Bibliography (papers verified in this engagement)

Only papers that have been read and verified against corpus artefacts
in the engagement are cited here. Papers attributable only to unread
sources are not in this section; claims that would require unread
sources appear in §4 / §5 as design references with explicit "Cited
paper: …" tags pointing at sources future Milestones must re-verify
from primary text.

### Shewchuk (1997) — adaptive precision arithmetic

J. R. Shewchuk, *Adaptive Precision Floating-Point Arithmetic and Fast
Robust Geometric Predicates*, Discrete & Computational Geometry
18(3):305–363, 1997.

**Corpus appearances.** Phase 0 Stage D (`Orient_b64_stage_d.v`),
fast-expansion-sum (`B64_FastExpansionSum*.v`), Shewchuk Theorem 13
(`docs/shewchuk-theorem-13-proof-structure.md`).

**Phase 3 role.** Foundation of the `orient2d` predicate that every
side-test in the topology graph reduces to. Phase 3 inherits Stage D
soundness as a black box and does not engage with the Shewchuk
material directly.

### Hobby (1999) — snap-rounding correctness

J. D. Hobby, *Practical Segment Intersection with Finite Precision
Output*, Computational Geometry: Theory and Applications 13(4):199–214,
1999.

**Corpus appearances.** Phase 2 Slices 1–11 in
`theories/HotPixel.v` + `theories-flocq/HotPixel_b64.v` (passes-through
relation, Liang–Barsky filter); Phase 2 Slices 12–13 +
`theories-flocq/HobbyTheorem_b64.v` (PR #21) — `snap_round_preserves_
passes_through`, `snap_round_preserves_shared_hot_pixel`,
`hobby_theorem_4_1_conditional` (`Qed`-closed), `hobby_lemma_4_2` and
`hobby_lemma_4_3` (Admitted, deferred-proof entries). Companion doc:
`docs/hobby-theorem-proof-structure.md`.

**Phase 3 role.** **Link 1** of the proof chain (§2). Cited directly
via `hobby_theorem_4_1_conditional`. The conditional version
(depending on Lemma 4.3) is acceptable for Phase 3 — Phase 3 inherits
the conditionality and threads `Hlemma43` through Milestones 3–5
until Phase 2 closes Lemma 4.3.

**Provenance disclosure.** Paper-specific page numbers (Theorem 4.1
p.210, Lemma 4.2 p.211, Lemma 4.3 pp.211–212, R⁻ convention p.210–211)
are taken from the maintainer's verification of the PDF; the session
assistants that wrote PR #21 and this audit could not reach the PDF
(network policy blocks the hosts). The Coq statements are correct
mathematically regardless of paper-specific numbering; the
attributions stand on the maintainer's reading.

### Fortune and Van Wyk (1996) — static error bound analysis

S. Fortune and C. J. Van Wyk, *Static Analysis Yields Efficient Exact
Integer Arithmetic for Computational Geometry*, ACM Transactions on
Graphics 15(3):223–248, 1996.

**Corpus appearances.** Background framework for Phase 0–1
arithmetic: Section 4.1's static error bound formula and Figure 3's
operation counts for `orient2d` and segment-segment intersection.
Cited in the Phase 1 forward-error theorems
(`b64_intersect_point_x_forward_error` family).

**Phase 3 role.** Confirms Phase 0–1 predicate operation counts and
bit-length bounds that Phase 3 implicitly relies on (e.g. the integer
regime carrying through composite graph operations). No new Phase 3
content cites it directly.

### Ozaki, Ogita, Rump, Oishi (2012) — interval matrix multiplication

K. Ozaki, T. Ogita, S. M. Rump, S. Oishi, *Fast algorithms for
floating-point interval matrix multiplication*, Journal of
Computational and Applied Mathematics 236(7):1795–1814, 2012.

**Corpus appearances.** Phase 0 `b64_ozaki_filter_sound` — an
alternative `orient2d` filter using γ₂-style bounds, same
sign-interpretation as the Stage D path.

**Phase 3 role.** Same as Shewchuk — foundation of the predicate
layer, inherited as a black box.

**No other papers are cited.** In particular: Halperin & Packer 2002
(ISR — iterated snap rounding) is *mentioned* in
`docs/audit-phase2-snap-rounding.md` §2.6 as a future Phase 2
refinement, but is not part of Phase 3's chain and is not cited here.
Davis 2020 (the JTS OverlayNG paper) is the algorithmic source for
the three-stage decomposition (§1.1); future milestones will re-cite
it from primary text rather than from this audit.

---

## 8. Resumption checklist

A contributor starting Phase 3 (or resuming after a long pause) should
work through this checklist before opening any `.v` file:

- [ ] Read this document fully (§1–§8).
- [ ] Read `docs/audit-phase2-snap-rounding.md` — Phase 2's audit; the
      structural template for this document.
- [ ] Read `docs/hobby-theorem-proof-structure.md` (PR #21) — the
      precise gap to the unconditional Hobby Theorem 4.1; sections §3,
      §4, §7 are the resumption material for `hobby_lemma_4_2` and
      `hobby_lemma_4_3`.
- [ ] Read `docs/phase2-hotpixel-progress.md` — Slices 1–11
      (primitives; §3.3 of this doc surveys them).
- [ ] Read `docs/audit-phase4-curves.md` §4 — the "chord-first" stance
      that scopes Phase 3 to polygonal (non-curve) geometries.
- [ ] Skim `theories-flocq/HotPixel_b64.v` (Slices 1–11),
      `theories-flocq/SnapRounding_b64.v` (Slice 12),
      `theories-flocq/TopologicalCorrectness_b64.v` (Slice 13),
      `theories-flocq/HobbyTheorem_b64.v` (Hobby 4.1 conditional).
      Note the conventions: half-open hot pixel, `round-half-to-even`
      snap, integer-regime safety predicates, snap idempotence.
- [ ] Check the deferred-proof registry
      (`docs/admitted-deferred-proofs.txt`) for the current state of
      `hobby_lemma_4_2`, `hobby_lemma_4_3`, and
      `fast_expansion_sum_nonoverlap_shewchuk`. The audit's §3.6 captures
      the post-PR-#21 baseline (3 deferred-proof entries); cross-check
      against the live registry before relying on the conditional Link 1.
- [ ] Search opam (`coq-community`, `mathcomp-analysis`,
      `coq-extra-graph`, ...) for a Rocq-9.1.1-compatible planar-graph
      library. Update Milestone 2's vendor/build decision based on
      what exists today (vs the 2026-05 baseline this audit captured).
- [ ] Draft the `Geometry` ADT against OGC SFA §6 — Milestone 1's first
      deliverable. Do **not** specialise to `BPoint` yet; keep the R-side
      definition parametric so Milestone 1's b64 mirror is a thin
      instantiation.
- [ ] State Milestone 1's headline theorem (`overlay_ng_correct`) before
      writing any non-trivial Coq. The statement is the contract — the
      proof is the *implementation* of that contract via the four-link
      chain. The headline carries `Hlemma43` as an explicit hypothesis
      until `hobby_lemma_4_3` lands.
- [ ] **Consider closing `hobby_lemma_4_2` first** — it is the cheaper
      of the two Hobby deferred entries (2–3 sessions per the registry)
      and is on the path to `hobby_lemma_4_3`. Closing 4.2 alone does
      not directly unblock Phase 3 — the unconditional Hobby Theorem 4.1
      requires 4.3 — but it materially reduces the 4.3 effort.
      Resumption material: `docs/hobby-theorem-proof-structure.md` §3,
      §7.

**The discipline.** This document is the **audit**, not the design. It
maps the obligations; each Milestone re-derives its own design from
primary text (the JTS / NTS source, OGC SFA, Hobby 1999). The audit
exists so the design work knows where it sits in the larger structure
— not so the design work can skip primary-source reading.

One audit. One Phase 3. Five milestones. Four links. The thesis-shaped
piece is Milestone 5 / Link 4.
