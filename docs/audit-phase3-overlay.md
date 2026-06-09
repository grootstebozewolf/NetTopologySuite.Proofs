# Library audit: overlay correctness for Phase 3

**Question.** To formalise a verified overlay engine (`OverlayNG_b64`
in the project's Phase 0-7 chokepoint table), what's reusable from
Phases 0/1/2, what's the formal shape of the correctness theorem,
and how is the work milestoned?

**Decision driver.** The corpus invariant (no `Admitted` / `Axiom` /
`Parameter` outside the deferred-proof + counterexample registries)
makes "reuse" much cheaper than "vendor", and "vendor" much cheaper
than "build". Phase 3 is where the Phase 0/1/2 pointwise primitives
(orientation, intersection, snap-rounded noding) compose into a
whole-arrangement transformation: input geometries become an output
geometry that **set-theoretically equals the boolean operation** on
the inputs. That equality is the Phase 3 headline.

---

> **Status note (2026-06-09).** This is the Milestone-2-era planning audit;
> it is substantially superseded in detail by
> `docs/audit-phase3-milestone5.md` and the landed conditional headline.
> Stale passages:
>
> - **Registry counts (§2).** "Deferred-proof registry (3 entries)"
>   (Shewchuk + `hobby_lemma_4_2` + `hobby_lemma_4_3`) and "Counterexample
>   registry (3 entries)" are both out of date. `hobby_lemma_4_2` is now
>   Qed-closed; the Shewchuk nonoverlap headline and `hobby_lemma_4_3_no_proper`
>   moved to the **counterexample** registry. The live state is **1 deferred**
>   (`extract_rings_valid`) and **6 counterexample** — see
>   `docs/admitted-deferred-proofs.txt` and `docs/admitted-counterexamples.txt`.
> - **Option A/B is settled (§4).** Milestone 5 landed Option A *exact-iff in
>   conditional form* (`overlay_ng_correct_conditional`, Qed-closed) with
>   Option B as a 2-line corollary — not the Option-B default recommended
>   here. The §3.1/§4 `point_in_ring` correctness discussion is overtaken by
>   the JCT-seam vacuity finding: `geometric_interior_stdlib` was refuted as
>   vacuous and H1 re-pointed onto `geometric_interior_cont`. See
>   `docs/verified-claims.md` Phase 3 and `docs/jct-vacuity-finding.md`.

---

## 0. What OverlayNG does, and the three-stage pipeline

**Input.** Two valid geometries `A` and `B` (each a `Geometry` =
`list Polygon`), plus a boolean operation tag `op : BooleanOp`
(Union | Intersection | Difference | SymDiff).

**Output.** A single geometry `C` such that the point-set of `C`
equals the boolean operation `op` applied to the point-sets of `A`
and `B`:

    point_set C = boolean_op op A B

NTS implements this in three stages (mirroring JTS's `OverlayNG`):

  1. **Noding (Phase 2).** Decompose the edges of `A` and `B` into a
     non-crossing arrangement of snap-rounded line segments.  Phase 2
     formalised this for the snap-rounding noder; the topological
     correctness is captured by `fully_intersected (snap_round_segments
     A)` via `hobby_theorem_4_1_conditional` (conditional on
     `hobby_lemma_4_3`, currently a deferred-proof entry).

  2. **Topology graph (Milestone 2 -- this session).**  Build a planar
     graph (`TopologyGraph`) whose vertices are the snap-rounded
     intersection points and whose edges are the inter-vertex segments,
     each carrying a label that records which input geometries it
     belongs to (`EdgeLabel := { in_left : bool ; in_right : bool }`).

  3. **Result extraction (Milestones 3-5).**  Traverse the labelled
     graph to extract the rings of `C` for the chosen operation,
     assemble the polygons, and prove that the point-set of the result
     equals the boolean operation.

Informal correctness: *valid inputs produce a valid output whose
point-set is the boolean operation applied to the input point-sets.*

---

## 1. The formal correctness theorem

A four-link proof chain.  Each link is one milestone-worth of work;
the deferred dependencies sit at the entry to Link 1.

**Link 1 -- noding produces a fully-intersected arrangement.**

    valid_geometry A -> valid_geometry B ->
    fully_intersected (noded_segments A B)

  Cites: `hobby_theorem_4_1_conditional`
  (`theories-flocq/HobbyTheorem_b64.v:159`).

  Statement (literal, from the file):

      forall (A : list (Point * Point)),
        fully_intersected A ->
        (forall s1 s2 : Point * Point,
           segments_intersect_only_at_endpoints s1 s2 ->
           forall sigma1 sigma2 : Point * Point,
             In sigma1 (snap_round_segments [s1]) ->
             In sigma2 (snap_round_segments [s2]) ->
             sigma1 <> sigma2 ->
             segments_intersect_only_at_endpoints sigma1 sigma2) ->
        fully_intersected (snap_round_segments A).

  Conditional: the second hypothesis is Hobby Lemma 4.3 in
  hypothesis form.  Discharging it unconditionally requires closing
  `hobby_lemma_4_3` (deferred-proof).

**Link 2 -- the topology graph is well-formed.**

    fully_intersected segs ->
    valid_topology_graph (build_graph segs)

  This milestone delivers `valid_topology_graph`; `build_graph` and
  its noding-to-graph bridge land in Milestone 3.

**Link 3 -- the graph carries correct labels for the operation.**

    valid_topology_graph g ->
    correct_labels op g

  Milestone 4.  Each edge's `EdgeLabel` correctly records membership
  in the input geometries; the per-operation labelling rule (Union
  vs. Intersection vs. Difference vs. SymDiff) determines which
  edges enter the output.

**Link 4 -- extraction is point-set correct.**

    correct_labels op g ->
    valid_geometry (extract op g) /\
    point_set (extract op g) = boolean_op op A B

  Milestone 5.  Thesis-shaped: this is the equality that ties the
  pipeline to the mathematical semantics.  See §5.

---

## 2. Corpus infrastructure -- what Phase 3 reuses

### Phase 0 (orient2d, Stages A-D)

  - `b64_orient_sign_stage_d_sound`
    (`theories-flocq/Orient_b64_stage_d.v:143`) -- Stage-D headline:
    expansion-based decoder yielding `orient_sign_robust`,
    sign-correct on the safety predicate.  Shewchuk (1997)
    Theorem 13 lineage.
  - `b64_orient_sign_stage_d_tiny_regime_decisive`
    (`theories-flocq/Orient_b64_stage_d.v:170`) -- never returns
    `Uncertain` in the tiny-input regime.

### Phase 1 (segment intersection)

  - `HasIntersect_BPoint` instance
    (`theories-flocq/Intersect_b64_exact.v:2159`) -- the binary64
    intersection primitive packaged as the chord-paradigm typeclass
    consumed downstream.  Soundness via the integer-regime headline
    `b64_intersect_sign_filtered_sound_small_int`.

### Phase 2 (snap-rounding)

  - `b64_liang_barsky_touches`
    (`theories-flocq/SnapRounding_b64.v`) -- segment-touches-pixel
    decision, B2R-congruent on its three inputs.
  - `b64_passes_through_sound`, `b64_passes_through_complete`
    (`theories-flocq/HotPixel_b64.v:2422,2438`) -- the
    passes-through-hot-pixel relation, sound and complete.
  - `b64_passes_through_hot_pixel_halfopen_sound`,
    `b64_passes_through_hot_pixel_halfopen_complete`
    (`theories-flocq/PassesThroughHalfopen_b64.v:441,458`) --
    strict half-open variant, used for tiled-pixel arguments.
  - `b64_snap_round_preserves_passes_through`
    (`theories-flocq/SnapRounding_b64.v:175`) -- a segment passing
    through a hot pixel still does so after snapping; the local
    preservation invariant the Phase 2 Slice 13
    `share_hot_pixel_preserved_under_snap` headline rests on.
  - `hobby_theorem_4_1_conditional`
    (`theories-flocq/HobbyTheorem_b64.v:159`) -- Hobby (1999)
    Theorem 4.1 in conditional form (`hobby_lemma_4_3` as
    hypothesis).  See Link 1 above for the literal statement.

### Phase 3 Milestone 1 (geometry types)

  - `Ring`, `Polygon`, `Geometry`, `BooleanOp`
    (`theories/Overlay.v`) -- Shape C representation: structural
    `list Polygon` with `point_set : Geometry -> Point -> Prop`
    bridge.
  - `valid_geometry` -- OGC 06-103r4 §6 polygon invariants:
    `ring_closed`, `ring_simple`, `hole_inside_outer`,
    `ring_has_minimum_points`.
  - `boolean_op` -- point-set semantics for the four operations.
  - `point_in_ring` -- crossing-number parity via mutually inductive
    `ray_parity_odd` / `ray_parity_even`.  Generic-position
    convention; on-edge robustness is a deferred refinement (see
    §4).
  - Six Qed-closed structural lemmas (`valid_geometry_nil`,
    `valid_geometry_cons`, `point_set_nil`, three `boolean_op_*_comm`).
  - Axiom footprint: `ClassicalDedekindReals.sig_forall_dec` and
    `FunctionalExtensionality.functional_extensionality_dep` only;
    no `Classical_Prop.classic`; not in `audit-exceptions.txt`.

### Deferred-proof registry (3 entries, Phase 2 lineage)

These gate Link 1; none gates Milestone 2 directly.

  - `theories-flocq/B64_FastExpansionSum_Shewchuk.v:fast_expansion_sum_nonoverlap_shewchuk`
    -- structure in `docs/shewchuk-theorem-13-proof-structure.md`
    §1,§2.1,§4,§6,§6.1-6.5.  Gates Stage D's nonoverlap chain.
  - `theories-flocq/HobbyTheorem_b64.v:hobby_lemma_4_2`
    -- structure in `docs/hobby-theorem-proof-structure.md` §3,§7.
    The monotone-coordinate lemma over Hobby's snap region R^-.
  - `theories-flocq/HobbyTheorem_b64.v:hobby_lemma_4_3`
    -- structure in `docs/hobby-theorem-proof-structure.md` §4,§7.
    The endpoint-only-intersection preservation lemma; this is the
    one whose discharge converts Link 1 from conditional to
    unconditional.

### Counterexample registry (3 entries, Phase 1 Stage D lineage)

  - `theories-flocq/B64_FastExpansionSum.v:b64_grow_expansion_nonoverlap`
  - `theories-flocq/B64_FastExpansionSum.v:round_eq_under_strict_dominance`
  - `theories-flocq/B64_FastExpansionSum.v:b64_grow_expansion_nonoverlap_dominated`

---

## 3. What's missing -- the genuine Phase 3 scope

Six items, in milestone order, with session estimates.

### 3.1 `point_in_polygon` correctness (deferred refinement)

The crossing-number algorithm in `theories/Overlay.v` defines
`point_in_ring` as the parity of the number of edges crossed by a
horizontal rightward ray from `p`.  The geometric correctness
theorem -- "this parity is `true` iff `p` is in the topological
interior of the bounded region enclosed by `r`" -- is the deferred
piece.  Standard formalisation: case-analyse the ray's interaction
with the ring's edges, using a Jordan-curve argument on simple
closed curves.  **Estimated: 3-5 sessions.**

### 3.2 `TopologyGraph` (this milestone)

Vertices = list of `Point`.  Edges = list of `Point * Point *
EdgeLabel`.  Well-formedness predicate `valid_topology_graph`:
every edge's endpoints appear in the vertex list.  Construction
helpers: `empty_graph`, `add_vertex`, `add_edge`.  **Estimated:
this session.**

### 3.3 `build_graph` (Milestone 3)

The function `build_graph : list Segment -> TopologyGraph`
constructing a graph from a noded segment list.  The
noding-to-graph bridge theorem:

    fully_intersected segs ->
    valid_topology_graph (build_graph segs)

Cites Link 1's `hobby_theorem_4_1_conditional`.  **Estimated:
2-3 sessions.**  Prerequisite: decidable `Point` equality
(deferred from this milestone -- see §3.7) to support a
`has_vertex` lookup helper.

### 3.4 `valid_topology_graph` (this milestone)

A graph is valid iff every edge has both endpoints in the vertex
list.  The bare minimum for Milestone 3 to construct a useful
graph.  **Estimated: this session.**

### 3.5 `correct_labels` (Milestone 4)

Per-operation labelling rules.  For each boolean op, a predicate
specifying which edges of the graph appear in the output:

  - Union:        in_left \/ in_right
  - Intersection: in_left /\ in_right
  - Difference:   in_left /\ ~in_right
  - SymDiff:      in_left  xor in_right

Plus structural lemmas tying the rules to `boolean_op`'s point-set
definition.  **Estimated: 2-3 sessions.**

### 3.6 Set-theoretic correctness -- Link 4 (Milestone 5)

The headline equality:

    point_set (extract op g) = boolean_op op A B

This is the thesis-shaped piece.  See §5 for option choice.
**Estimated: 6-10 sessions.**

### 3.7 Decidable `Point` equality (deferred from Milestone 2)

`Point` is `{ px : R ; py : R }`.  Decidable equality follows
from `Stdlib`'s `Req_EM_T` (which pulls
`ClassicalDedekindReals.sig_not_dec`, already on the allowlist).
~10 lines.  Needed by `has_vertex` in Milestone 3; deferred from
Milestone 2 because none of this milestone's structural lemmas
requires it.  Recommended placement: `theories/Overlay.v` (Point
is a foundation-layer concept; the decidability instance belongs
near `Distance.Point`'s definition site, but adding it in
`Overlay.v` keeps the foundation layer untouched).

---

## 4. The thesis-shaped piece (Link 4)

Two strategic options:

**Option A -- exact equality.**

    point_set (extract op g) = boolean_op op A B

Prove the extracted geometry's point-set equals the exact
set-theoretic boolean operation.  Requires showing the planar
graph traversal captures *all and only* the correct points.
Hardest; strongest correctness guarantee.

**Option B -- bounded displacement.**

    forall p,
      point_set (extract op g) p -> exists q,
        boolean_op op A B q /\ dist p q <= snap_radius
    AND vice versa.

Prove the extracted geometry's point-set is within one hot-pixel
radius of the exact boolean operation.  Weaker; directly connected
to Phase 2's snap-rounding error bound (Hobby's `radius = 1/(2 *
scale)`).  More tractable; better-aligned with the corpus's
existing displacement-based bounds.

**Project target: TBD before Milestone 4.**  Recommended default
is Option B, since (i) it composes mechanically with Phase 2's
snap-rounding displacement guarantees, (ii) Option A would require
re-proving `point_in_polygon` correctness up to exact set equality
(re-opening §3.1), and (iii) the .Curve consumer that drives this
work tolerates bounded displacement (linearisation introduces a
larger tolerance anyway).

---

## 5. Milestone structure

    M1: valid_geometry + boolean_op             complete (338 lines)
    M2: TopologyGraph + audit doc                this session
    M3: build_graph + noding bridge              2-3 sessions
    M4: correct_labels                           2-3 sessions
    M5: set-theoretic correctness (Link 4)       6-10 sessions
    -------------------------------------------- ----------------
    Phase 3 remaining (post-M2):                 10-16 sessions

The remaining-session estimate brackets `point_in_polygon`
correctness (§3.1) as a parallel multi-session refinement; it does
not block M3-M4 because their statements treat `point_in_ring`
opaquely.  It does feed Option A in M5 (if chosen).

---

## 6. Bibliography

Primary sources, verified against the project's existing audit
trail:

  - **Shewchuk (1997)** -- "Adaptive Precision Floating-Point
    Arithmetic and Fast Robust Geometric Predicates."  *Discrete
    & Computational Geometry* 18:305-363.  Theorem 13 (orient2d
    expansion).  Foundation for Phase 0 Stage D.

  - **Hobby (1999)** -- "Practical Segment Intersection with Finite
    Precision Output."  *Computational Geometry: Theory and
    Applications* 13:199-214.  Theorem 4.1 p.210 (snap-rounded
    arrangement remains fully-intersected), Lemma 4.2 p.211
    (monotone coordinate), Lemma 4.3 pp.211-212 (endpoint
    preservation).  Snap region R^- definition p.210.

  - **Fortune and Van Wyk (1996)** -- "Static Analysis Yields
    Efficient Exact Integer Arithmetic for Computational Geometry."
    *ACM TOG* 15(3):223-248.  §4.1 maxerr formula, Figure 3
    operation counts.  Foundation for Phase 0 Stage A filter
    bounds.

  - **Ozaki, Ogita, Rump, Oishi (2012)** -- "Tight and Efficient
    Enclosure of Matrix Multiplication by Using Optimized BLAS."
    *Numerical Linear Algebra with Applications*.  The gamma_2
    filter formulation reused in Phase 0 Stage A.

  - **OGC 06-103r4** -- "OpenGIS Implementation Standard for
    Geographic information -- Simple feature access -- Part 1:
    Common architecture", version 1.2.1.  §6 polygon validity
    rules: closed rings, simple rings, holes interior to outer
    ring, minimum vertex count.  This document does NOT carry the
    explicit per-clause sub-numbering used in some derivative
    standards (specific sub-clauses are a documentation gap
    flagged for Phase 3 completion).

    **Attribution correction (carried from project owner's
    reading):** CIRCULARSTRING, COMPOUNDCURVE, and CURVEPOLYGON are
    in SQL/MM Spatial (ISO/IEC 13249-3), NOT in OGC SFA.
    TRIANGLE, MULTICURVE, and MULTISURFACE are in OGC SFA itself.
    Phase 4's curve-bearing extension cites SQL/MM, not SFA, for
    arc-bearing geometry types.

---

## 7. Resumption checklist

  - [x] Compile `theories/Overlay.v` locally -- green
        (Milestone 1, verified end of session 1).
  - [ ] Compile `theories/OverlayGraph.v` locally -- this session.
  - [ ] Read Hobby (1999) §4 before Milestone 3 (build_graph's
        noding-to-graph bridge cites Theorem 4.1).
  - [ ] Pin specific OGC 06-103r4 §6 sub-clauses to each
        `valid_polygon` conjunct before Milestone 4 (documentation
        gap flagged in §6 above).
  - [ ] Decide Option A vs Option B for Milestone 5 before starting
        Milestone 4 -- the labelling rules in M4 differ slightly
        between the two targets.
  - [ ] Consider closing `hobby_lemma_4_2` (estimated 2-3 sessions
        per `docs/hobby-theorem-proof-structure.md`) before
        Milestone 3 to strengthen Link 1.  Not strictly required;
        M3 can cite Link 1 in conditional form.
  - [ ] Add decidable `Point` equality in Milestone 3 (see §3.7).

---

## 8. Audit summary

| Concept                              | Source            | Status        |
| ------------------------------------ | ----------------- | ------------- |
| `Geometry`, `BooleanOp`, `point_set` | Overlay.v (M1)    | shipped       |
| `valid_geometry`                     | Overlay.v (M1)    | shipped       |
| `point_in_ring` (algorithm)          | Overlay.v (M1)    | shipped       |
| `point_in_ring` correctness          | future            | 3-5 sessions  |
| `fully_intersected`                  | Phase 2           | reused        |
| `snap_round_segments`                | Phase 2           | reused        |
| `hobby_theorem_4_1_conditional`      | Phase 2           | reused (cond) |
| `hobby_lemma_4_3`                    | Phase 2 deferred  | gates Link 1  |
| `TopologyGraph`                      | OverlayGraph.v M2 | this session  |
| `valid_topology_graph`               | OverlayGraph.v M2 | this session  |
| `build_graph`                        | future M3         | 2-3 sessions  |
| `correct_labels`                     | future M4         | 2-3 sessions  |
| Link 4 (Option A/B)                  | future M5         | 6-10 sessions |
| `point_eq_dec`                       | future M3         | ~10 lines     |

  - **Reuse from Phase 2:** `fully_intersected`,
    `snap_round_segments`, `hobby_theorem_4_1_conditional`.
  - **Build in Phase 3:** `TopologyGraph`, `build_graph`,
    `correct_labels`, `extract`.
  - **Thesis-shaped:** Link 4 (Milestone 5), 6-10 sessions.
  - **Critical-path conditional blocker:** `hobby_lemma_4_3`
    (currently deferred-proof; estimated 4-6 weeks per
    `docs/hobby-theorem-proof-structure.md`) gates the
    unconditional form of Link 1.
