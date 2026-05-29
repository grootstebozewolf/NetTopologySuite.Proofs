# Audit: Phase 3 Milestone 5 — overlay correctness theorem

**Question.** What does the headline correctness theorem
`overlay_ng_correct` look like in Coq, what proof obligations does it
break into, what's already in the corpus, and what is the
remaining-session plan that closes it (or, more honestly, closes it
*conditionally* on the thesis-shaped sub-problems)?

**Decision driver.** Milestones 1–4 landed the geometry types
(`Geometry`, `boolean_op`, `point_set`, `valid_geometry`), the
topology graph (`TopologyGraph`, `valid_topology_graph`,
`build_graph`, `build_labeled_graph`), the labelling rules
(`edge_in_result`), and the noding-to-graph bridge
(`snap_noding_bridge`).  What remains is the headline equation tying
the assembled-and-labelled graph back to the point-set semantics —
the *thesis-shaped piece* of Phase 3, flagged at 6-10 sessions in
`docs/audit-phase3-overlay.md` §3.6.

This audit honestly accounts for the gap between that 6-10 estimate
and what the corpus actually has.  Two of the sub-problems are
multi-month works in their own right (Jordan Curve Theorem for simple
polygons; DCEL-style face traversal for the labelled planar
subdivision).  The conditional strategy in §6 is the escape valve.

---

## 1. The headline theorem

The exact Coq statement targeted by Sessions 2–10:

```coq
Theorem overlay_ng_correct :
  forall (A B : Geometry) (op : BooleanOp) (p : Point),
    valid_geometry A ->
    valid_geometry B ->
    fully_intersected (noded_segments A B) ->
    point_set (extract op (build_labeled_graph_full A B)) p <->
    boolean_op op A B p.
```

Where:
- `extract : BooleanOp -> TopologyGraph -> Geometry` is the new
  function defined in Session 2 (edge filtering + ring assembly).
- `build_labeled_graph_full : Geometry -> Geometry -> TopologyGraph`
  is the Flocq-layer composition
  `build_labeled_graph (snap_round_segments (extract_segments A))
                       (snap_round_segments (extract_segments B))`
  i.e., `noded_labeled_graph A B` from M4's
  `theories-flocq/OverlayBridge.v`.

**Option A (this headline) — exact iff.**  Matches
`docs/audit-phase3-overlay.md` §4's Option A.

**Option B corollary (2-line derivation).**  Once Option A closes,
the bounded-displacement formulation is immediate:

```coq
Corollary overlay_ng_correct_bounded :
  forall A B op p,
    valid_geometry A -> valid_geometry B ->
    fully_intersected (noded_segments A B) ->
    point_set (extract op (build_labeled_graph_full A B)) p ->
    exists q, boolean_op op A B q /\ dist p q = 0.
Proof.
  intros A B op p HA HB Hfi Hp.
  exists p. split.
  - apply (proj1 (overlay_ng_correct A B op p HA HB Hfi)). exact Hp.
  - unfold dist. simpl. lra.  (* dist p p = 0 *)
Qed.
```

The displacement bound is trivially zero because Option A gives exact
iff.  The Option-B form is what the audit doc §4 recommends *as the
default if Option A is too hard* — but a tight Option A trivially
implies a strict Option B, so we go for Option A and derive Option B
as a corollary.

**The `fully_intersected` precondition** is the connection point for
`hobby_theorem_4_1_conditional` (theories-flocq/HobbyTheorem_b64.v).
It is currently discharged by hypothesis at every call site; closing
`hobby_lemma_4_3_no_proper` (currently deferred-proof, registry
entry; 4-6 weeks estimate per the proof-structure doc) makes the
precondition unconditional and the corollary
`overlay_ng_correct_unconditional` becomes available.

---

## 2. The proof chain

The full Link 1 → Link 4 chain, with each arrow's discharge site:

```
valid_geometry A                                             [M1]
valid_geometry B                                             [M1]
   │
   │  extract_segments  : Geometry → list (Point × Point)    [M4]
   │
   ▼
extract_segments A ++ extract_segments B
   │
   │  snap_round_segments : list (P × P) → list (P × P)      [Phase 2]
   │
   ▼
noded_segments A B                                           [M4]
   │
   │  hobby_theorem_4_1_conditional  (conditional on         [Phase 2,
   │    hobby_lemma_4_3_no_proper, deferred)                  cond]
   │
   ▼
fully_intersected (noded_segments A B)
   │
   │  snap_noding_bridge                                     [M4]
   │  valid_topology_graph_noded_labeled_graph               [M4]
   │
   ▼
valid_topology_graph (build_labeled_graph_full A B)
   │
   │  extract op             : TopologyGraph → Geometry      [Session 2]
   │    composed of:
   │      filter edges where edge_in_result op l = true      [M4 rule]
   │      assemble filtered edges into rings (DCEL)          [Session 4]
   │      package rings into polygons                        [Session 4]
   │
   ▼
extract op (build_labeled_graph_full A B) : Geometry
   │
   │  point_set                                              [M1]
   │
   ▼
point_set (extract op (build_labeled_graph_full A B)) : Point → Prop
   │
   │  Link 4 (the headline iff):                             [Sessions 5-10]
   │   point_set ∘ extract = boolean_op
   │     │ via correct_labels (Sessions 5-7)
   │     │     edge_in_result op l = true
   │     │     ↔ edge (p,q) belongs to boolean_op op A B
   │     │ via point_in_ring_correct (Session 3, JCT-dep)
   │     │     crossing-number parity ↔ geometric interior
   │     └ via ring assembly correctness (Session 4)
   │
   ▼
boolean_op op A B : Point → Prop                             [M1]
```

Each named arrow gates a specific session.  The chain is
**structurally** linear, but two of its arrows (Session 3, Session 4)
are thesis-shaped pieces individually.

---

## 3. Current corpus inventory

Citations at file:line as of this audit:

```
Foundation layer (theories/):

  Point                  theories/Distance.v:27
  Segment                theories/Segment.v:31         (unused by M2-M4)
  Ring                   theories/Overlay.v:84
  Polygon                theories/Overlay.v:87
  Geometry               theories/Overlay.v:93
  Edge                   theories/Overlay.v:102
  ring_edges             theories/Overlay.v:110
  segments_intersect_properly
                         theories/Overlay.v:125
  edge_crosses_ray       theories/Overlay.v:149
  ray_parity_odd/even    theories/Overlay.v:161
  point_in_ring          theories/Overlay.v:183
    Status: DEFINED via crossing-number parity.
            CORRECTNESS NOT PROVED.
            No relation to geometric interior is in the corpus.
  point_in_polygon       theories/Overlay.v:194
  point_set              theories/Overlay.v:202
  BooleanOp              theories/Overlay.v:212
  boolean_op             theories/Overlay.v:220
  ring_closed            theories/Overlay.v:232
  ring_simple            theories/Overlay.v:244
  hole_inside_outer      theories/Overlay.v:255
  ring_has_minimum_points
                         theories/Overlay.v:262
  valid_polygon          theories/Overlay.v:268
  valid_geometry         theories/Overlay.v:279

  M1 structural lemmas (6, all Qed-closed; two-axiom footprint):
    valid_geometry_nil, valid_geometry_cons,
    point_set_nil,
    boolean_op_union_comm, boolean_op_intersection_comm,
    boolean_op_symdiff_comm

Topology graph layer (theories/OverlayGraph.v):

  EdgeLabel              theories/OverlayGraph.v:85
  TopologyGraph          theories/OverlayGraph.v:97
  valid_topology_graph   theories/OverlayGraph.v:108
  empty_graph            theories/OverlayGraph.v:119
  add_vertex             theories/OverlayGraph.v:127
  add_edge               theories/OverlayGraph.v:136
  point_eq_dec           theories/OverlayGraph.v:232
  segment_endpoints      theories/OverlayGraph.v:243
  dedup_vertices         theories/OverlayGraph.v:247
  default_label          theories/OverlayGraph.v:251
  build_graph            theories/OverlayGraph.v:258
  polygon_to_pairs       theories/OverlayGraph.v:356
  extract_segments       theories/OverlayGraph.v:362
    (Geometry → list (Point × Point); FORWARD direction.
     Reverse direction `extract : ... → Geometry` is what
     Session 2 builds.)
  edge_in_result         theories/OverlayGraph.v:375
  label_from_A           theories/OverlayGraph.v:385
  label_from_B           theories/OverlayGraph.v:390
  build_labeled_graph    theories/OverlayGraph.v:400

  M2-M4 structural lemmas + Qed-closed theorems:
    valid_topology_graph_empty / _add_vertex / _add_edge
    tg_edge_endpoints_in_vertices
    empty_graph_no_edges
    segment_endpoints_fst / _snd
    build_graph_nil
    valid_topology_graph_build_graph
    label_from_A_endpoints_in_pairs / B_...
    segment_endpoints_app
    valid_topology_graph_build_labeled_graph
    build_labeled_graph_nil
    edge_in_result_union_true / _intersection_true /
      _difference_iff / _symdiff_iff

Bridge layer (theories-flocq/OverlayBridge.v):

  noded_segments         theories-flocq/OverlayBridge.v:61
  snap_noding_bridge     theories-flocq/OverlayBridge.v:78
  noded_labeled_graph    theories-flocq/OverlayBridge.v:97
  valid_topology_graph_noded_labeled_graph
                         theories-flocq/OverlayBridge.v:104

  Audit-exceptions footprint: Classical_Prop.classic via
  Flocq's Binary.B*_correct closure (snap_round_segments).
  File is listed in docs/audit-exceptions.txt.

Phase 2 conditional input (theories-flocq/HobbyTheorem_b64.v):

  segments_intersect_only_at_endpoints
                         theories-flocq/HobbyTheorem_b64.v:67
  fully_intersected      theories-flocq/HobbyTheorem_b64.v:75
  snap_round_segments    theories-flocq/HobbyTheorem_b64.v:83
  hobby_lemma_4_2        theories-flocq/HobbyTheorem_b64.v:124
    (Qed-closed; only the two README-allowlisted axioms)
  hobby_lemma_4_3_shared_endpoint
                         theories-flocq/HobbyTheorem_b64.v:355
    (Qed-closed)
  hobby_lemma_4_3_no_proper
                         theories-flocq/HobbyTheorem_b64.v:347
    (Admitted, deferred-proof; the thesis-shaped piece)
  hobby_lemma_4_3        (composed; Qed-closed)
  hobby_theorem_4_1_conditional
                         theories-flocq/HobbyTheorem_b64.v:422
    (Qed-closed; conditional on the Lemma 4.3-shaped hypothesis,
     which `hobby_lemma_4_3_no_proper` would discharge)

Missing — Session 2-10 deliverables:

  extract                : BooleanOp → TopologyGraph → Geometry
                           DOES NOT EXIST.  Session 2.
  correct_labels         : BooleanOp → TopologyGraph
                                       → Geometry → Geometry → Prop
                           DOES NOT EXIST.  Sessions 5-7.
  point_in_ring_correct  : point_in_ring p r ↔ geometric interior
                           DOES NOT EXIST.  Session 3 (JCT-dep).
  valid_geometry_extract : extract is a valid Geometry
                           DOES NOT EXIST.  Session 8.
  overlay_ng_correct     : the headline iff
                           DOES NOT EXIST.  Sessions 9-10.
  overlay_ng_correct_bounded
                         : Option B corollary
                           DOES NOT EXIST.  Session 10 tail.

Deferred-proof registry (current):

  theories-flocq/B64_FastExpansionSum_Shewchuk.v:
    fast_expansion_sum_nonoverlap_shewchuk  (Stage D)
  theories-flocq/HobbyTheorem_b64.v:
    hobby_lemma_4_3_no_proper  (Phase 2, gates Link 1)
```

---

## 4. Sub-proof obligations

Six items, in topological order:

### 4.1 `extract op g` — Session 2

The function: takes a labelled topology graph and a boolean operation,
filters edges where `edge_in_result op l = true`, and assembles them
into a `Geometry`.

The filter step is trivial (one `List.filter` call).  The **assembly
step** is the hard sub-problem: turn an unordered set of edges into an
ordered list of rings, each ring being a closed walk through the
edges.

For a connected planar subdivision, the rings are exactly the face
boundaries.  Computing them requires either:
  (a) a DCEL (doubly-connected edge list) traversal: O(n) per face.
  (b) Euler-path-style chain assembly: traverse edges in cyclic
      order around each vertex.

Both are *known algorithms* but neither is in the Coq stdlib.  The M4
type `TopologyGraph` stores edges as an unordered list — no per-vertex
ordering, no face information.  Either we extend `TopologyGraph` with
DCEL structure (cleaner but requires re-doing M2's lemmas) or define
the assembly entirely inside `extract` (more local but the assembly
function becomes large).

**Scope estimate.**  Defining `extract` *without* assembly correctness
is one session (Session 2).  Proving its correctness — that the
output rings are well-formed — is **Session 4** (separate, harder).

### 4.2 `point_in_ring_correct` — Session 3 (JCT-dep)

The statement:

```coq
Theorem point_in_ring_correct :
  forall (p : Point) (r : Ring),
    ring_closed r ->
    ring_simple r ->
    point_in_ring p r <-> geometric_interior p r.
```

Where `geometric_interior p r` is the topological interior of the
bounded region enclosed by `r` — the standard Jordan-curve-theorem
notion.

**This requires the Jordan Curve Theorem for simple polygons.**
Pre-existing Coq formalizations of JCT:
  - **mathcomp-analysis** has continuous-curve JCT but not in a form
    that directly applies to polygonal rings without translation.
  - **coq-community/jordan-curve-theorem** (search needed) — if it
    exists, it's the right import.
  - **Bauer & Stone (2007)** — formalized JCT in Mizar/Isabelle; no
    Coq port known.

**If no usable JCT formalization exists**, this becomes a
multi-month thesis-shaped piece on its own.  The realistic plan is:
state `point_in_ring_correct` as a Lemma with `Admitted`, register it
in the deferred-proof registry, and proceed with overlay_ng_correct
**conditional** on it.  This matches the pattern of
`hobby_lemma_4_3_no_proper`.

**Scope estimate (conditional path).**  Session 3 ~= 1 day:
  - 2 hours: search for usable JCT formalization.
  - 2 hours: state `point_in_ring_correct` (with `Admitted` if needed).
  - 2 hours: state `overlay_ng_correct` conditional on it.
  - 1 hour: register deferred entry.

**Scope estimate (full proof from scratch).**  3-5 months.  Not
attempted in this 10-session plan.

### 4.3 Edge → ring assembly correctness — Session 4

If Session 2 ships `extract` without assembly correctness, Session 4
adds it.  The theorem to prove:

```coq
Theorem extract_rings_valid :
  forall op A B,
    valid_geometry A -> valid_geometry B ->
    fully_intersected (noded_segments A B) ->
    forall poly,
      In poly (extract op (build_labeled_graph_full A B)) ->
      valid_polygon poly.
```

This is the second thesis-shaped piece.  Showing that DCEL traversal
on a valid labelled topology graph produces rings that satisfy all
four `valid_polygon` conditions (closure, simplicity, hole
containment, min vertex count) is genuine combinatorial-geometric
work.

**Scope estimate.**  3-4 sessions if a clean DCEL representation is
adopted in M4-revision.  6-8 sessions if reconstructed from the
unordered M4 edge list.  Bigger than the 10-session budget allows —
likely deferred.

### 4.4 `correct_labels` per operation — Sessions 5-7

For each `BooleanOp`, a Prop tying `edge_in_result` to membership in
the source geometries:

```coq
Definition correct_labels (op : BooleanOp)
    (g : TopologyGraph) (A B : Geometry) : Prop :=
  forall p q l,
    In (p, q, l) (tg_edges g) ->
    edge_in_result op l = true <->
      (* the edge (p, q) geometrically belongs to *)
      (* boolean_op op A B *)
      [...].
```

The RHS for each `op`, given `in_left l = true ↔ edge came from A`
and `in_right l = true ↔ edge came from B`:

  - Union:        `In (p,q) (extract_segments A) \/ In (p,q) (extract_segments B)`
  - Intersection: `In (p,q) (extract_segments A) /\ In (p,q) (extract_segments B)`
  - Difference:   `In (p,q) (extract_segments A) /\ ~ In (p,q) (extract_segments B)`
  - SymDiff:      symmetric pair.

But wait — these say "edge comes from this source geometry," not
"this edge is in the boolean-op result point-set."  The full
correctness needs to go further: an edge belonging to A's segments
isn't the same as "the edge's midpoint is in A's point-set."  Bridging
the two requires `point_in_ring_correct` (§4.2).

**Realistic scoping.**
  - Session 5: define `correct_labels` and prove it for Union (the
    easiest disjunctive case).
  - Session 6: Intersection (conjunctive).
  - Session 7: Difference + SymDiff (one with negation, one with
    exclusive-or; share most structure).

Each session ~1-3 days depending on how `point_in_ring_correct` is
handled (full vs conditional).

### 4.5 `valid_geometry (extract op g)` — Session 8

Show that `extract op g` returns a `Geometry` satisfying
`valid_geometry`.  Composes the M1 `valid_polygon` conditions with the
M4 `valid_topology_graph_build_labeled_graph` invariant via `extract`'s
ring-assembly output.

**Scope.**  ~1-2 sessions.  Mostly mechanical if §4.3 (`extract_rings_valid`)
is in scope; harder if §4.3 is deferred (then this theorem is also
conditional).

### 4.6 `point_set = boolean_op` — Sessions 9-10

The final equivalence.  Both directions:

  **Forward (Session 9).** `point_set (extract op g) p → boolean_op op A B p`.
    "Every point in the extracted geometry's interior is in the
    boolean-op set."  Uses `correct_labels` to lift edge-level
    membership to point-set membership via `point_in_ring_correct`.

  **Backward (Session 10).** `boolean_op op A B p → point_set (extract op g) p`.
    "Every point in the boolean-op set is in the extracted geometry's
    interior."  Harder — requires that the boundary-extraction
    procedure doesn't miss any points.

Both directions assume `point_in_ring_correct`.  If that's conditional,
both directions inherit the condition.

**Scope.**  2-3 sessions for both directions, given all prior
infrastructure.

---

## 5. The hard sub-problems

Two genuinely thesis-shaped pieces, both candidates for deferral via
the conditional strategy:

### 5.1 `point_in_ring_correct` — Jordan Curve Theorem dependency

The crossing-number characterisation is what `point_in_ring` *computes*.
Proving it matches the topological interior of a simple closed polygon
requires the polygonal Jordan Curve Theorem.

**Action item.**  Before Session 3, search the Coq ecosystem for an
existing JCT formalization:

  - Check opam: `opam list --installable | grep -i jordan`.
  - Check mathcomp-analysis: `mathcomp.analysis.topology` and
    `mathcomp.analysis.classical_sets` for relevant lemmas.
  - Check coq-community: <https://github.com/coq-community>.
  - Check coqdocjs / coq-projects-search: keyword "jordan curve".

If found: add to `_CoqProject.full` if compatible with the Rocq 9.1.1 +
Flocq 4.2.2 toolchain.  If not compatible: defer.

If not found: defer.  State `point_in_ring_correct` as `Admitted` with
a deferred-proof registry entry.  The headline becomes conditional —
see §6.

### 5.2 Edge → ring assembly — DCEL formalisation

Reconstructing ordered rings from M4's unordered edge list is the
classic doubly-connected-edge-list (DCEL) face-traversal problem.  An
unformalised algorithm fits in 50 lines of pseudocode; a verified
Coq implementation with all the invariants is thesis-sized work
(several months).

**Mitigation option: extend M4.**  Revise `build_labeled_graph` to
output a DCEL-shaped record instead of a flat edge list.  This makes
ring assembly local to the data structure rather than a global
inversion problem.

  - Cost: re-prove M4's structural lemmas against the new record.
    ~1-2 sessions of rework.
  - Benefit: Sessions 2 and 4 become tractable inside the budget.

**Recommendation.**  Adopt DCEL in a brief M4-revision session
(call it Session 1.5).  Without DCEL, the 10-session plan cannot
realistically close §4.3.

### 5.3 Open question — does build_labeled_graph's output form valid rings?

M4 emits edges in two flat lists (`label_from_A`, `label_from_B`)
without any per-vertex ordering or face-incidence information.  Two
adjacent edges sharing an endpoint in the graph are NOT obviously
adjacent in any ring traversal — that requires sorting by angle at
the shared vertex (the DCEL twin-edge invariant).

**Concrete action item before Session 2.**  Read M4's `build_labeled_graph`
output (theories/OverlayGraph.v:400) and decide:
  - Option (i): treat each edge as its own "degenerate ring"
    (closed walk of length 2 — illegal under
    `ring_has_minimum_points`).  Geometry is then a list of edge-rings;
    correctness becomes "every input segment is in the output"
    — much weaker than Option A's iff.
  - Option (ii): adopt DCEL (§5.2 mitigation) and produce real
    face-bounding rings.
  - Option (iii): output a `list Segment` instead of a `Geometry` —
    change the type signature of `extract`.  This sidesteps the
    assembly problem but breaks the audit doc's chain (which says
    extract produces a Geometry).

Each option has different implications for the rest of the 10-session
plan.  **Decide before Session 2.**

---

## 6. The conditional strategy

If §5.1 and/or §5.2 cannot close in the available budget, state the
headline conditionally:

```coq
Theorem overlay_ng_correct_conditional :
  forall (A B : Geometry) (op : BooleanOp) (p : Point),
    valid_geometry A ->
    valid_geometry B ->
    fully_intersected (noded_segments A B) ->
    (* Hypothesis 1: point_in_ring corresponds to geometric interior. *)
    (forall (q : Point) (r : Ring),
       ring_closed r -> ring_simple r ->
       point_in_ring q r <-> geometric_interior q r) ->
    (* Hypothesis 2: extract assembles into valid polygons. *)
    (forall poly,
       In poly (extract op (build_labeled_graph_full A B)) ->
       valid_polygon poly) ->
    point_set (extract op (build_labeled_graph_full A B)) p <->
    boolean_op op A B p.
```

Same pattern as `hobby_theorem_4_1_conditional` (Phase 2): the
headline is Qed-closed and the gaps are named, registered, and
honest.  The two hypotheses are individually deferred-proof entries
(estimated 3-5 months and 3-8 sessions respectively); discharging
either of them strengthens the headline.

**This is the pragmatic landing point.**  Closing
`overlay_ng_correct` unconditionally in 10 sessions requires the
JCT and DCEL pieces to materialize from an external source.
Realistically, sessions 9-10 close the conditional form;
discharging the conditions becomes future Phase 3.X work.

---

## 7. 10-session plan

Two variants depending on the §5.3 decision.

### Variant A: DCEL adopted in Session 1.5 (recommended)

```
S1   (this):  audit doc.
S1.5:         M4 revision -- extend build_labeled_graph output to
              DCEL-shaped record.  Re-prove the M4 structural lemmas.
S2:           Define `extract : BooleanOp -> TopologyGraph -> Geometry`
              via filter + DCEL face traversal.
S3:           Search JCT.  If found: import and use.
              If not: state `point_in_ring_correct` as Admitted with
              registry entry.  State
              `overlay_ng_correct_conditional`.
S4:           `extract_rings_valid` -- show the assembled rings
              satisfy `valid_polygon`.  Conditional on `point_in_ring_correct`
              if §4.3 needs it for ring simplicity.
S5:           `correct_labels` for Union.
S6:           `correct_labels` for Intersection.
S7:           `correct_labels` for Difference + SymDiff.
S8:           `valid_geometry (extract op g)`.
S9:           `point_set ∘ extract → boolean_op` (forward).
S10:          `boolean_op → point_set ∘ extract` (backward) +
              `overlay_ng_correct_bounded` corollary.
```

### Variant B: keep flat edge list, weaken the headline

```
S1   (this):  audit doc.
S2:           Define `extract` returning `list (Point * Point)`
              instead of `Geometry`.  Headline weakens to:
                extract_correct: edge is in extract iff its label
                  matches edge_in_result op.
S3:           `point_in_ring_correct` (same options as Variant A).
S4-S10:       Weaker correctness theorems chained on top.
              Final theorem is point-set equivalence at the edge
              level, not at the assembled-Geometry level.
```

Variant B is honest about the assembly problem but loses the
"full overlay correctness" goal.  Variant A is what `overlay_ng_correct`
*should* mean — DCEL is the cost of getting there.

**Strong recommendation: Variant A.**  Take the Session 1.5 hit;
the 10-session plan then closes the conditional theorem honestly.

### Likely landing point

  - Unconditional `overlay_ng_correct` is out of reach in 10 sessions.
  - `overlay_ng_correct_conditional` (conditional on JCT + DCEL ring
    validity, both deferred-proof) is the realistic closure.  Like
    `hobby_theorem_4_1_conditional`, it makes the corpus's
    correctness story complete in conditional form, with the
    remaining gaps named and registered.

---

## 8. Resumption checklist

  - [ ] Read this doc fully before Session 2.
  - [ ] **Decide §5.3** (DCEL adoption vs flat edges vs list-Segment
        return type) — this gates Session 2's design.
  - [ ] **Check mathcomp-analysis / coq-community for JCT** before
        Session 3.  Specific checks:
        - `opam search jordan`.
        - <https://github.com/coq-community/awesome-coq>.
        - <https://github.com/math-comp/analysis> issues with "jordan".
  - [ ] If JCT not found: prepare to state
        `point_in_ring_correct` as Admitted in Session 3, with
        registry entry.
  - [ ] Read DCEL algorithm (Berg, Cheong, van Kreveld, Overmars,
        "Computational Geometry: Algorithms and Applications" §2.2)
        before Session 1.5 / S2.
  - [ ] **Decide conditional vs unconditional headline** before
        Session 9.  If DCEL ring validity (§4.3) didn't close in
        Session 4, the headline must be conditional.
  - [ ] Confirm `build_labeled_graph`'s output type (decision from
        §5.3) is locked-in before Session 2's `extract` definition.
  - [ ] Option B corollary: 2-line derivation after S10 closes
        Option A (or its conditional form).
  - [ ] Update `docs/audit-phase3-overlay.md`'s §3.6 and §4 as
        Sessions land — keep the milestone-tracking doc in sync.

---

## 9. Audit summary

| Concept                              | Status                       | Estimate     |
| ------------------------------------ | ---------------------------- | ------------ |
| `overlay_ng_correct` (Option A)      | targeted                     | S9-S10       |
| `overlay_ng_correct_bounded`         | corollary                    | S10 tail     |
| `extract : BooleanOp → G → Geometry` | new, S2 def                  | 1 session    |
| Edge → ring assembly correctness     | new, S4 — thesis-shaped      | 3-8 sessions |
| `point_in_ring_correct`              | new, JCT-dep                 | conditional  |
| `correct_labels` × 4 ops             | new, S5-S7                   | 3 sessions   |
| `valid_geometry (extract op g)`      | new, S8                      | 1-2 sessions |
| `point_set = boolean_op` (forward)   | new, S9                      | 1 session    |
| `point_set = boolean_op` (backward)  | new, S10                     | 1 session    |
| DCEL data structure (S1.5)           | M4 revision                  | 1-2 sessions |

  - **Reuse from M1-M4:** all geometry types, the topology graph,
    M4's labelling rules, the noding-to-graph bridge.
  - **Build in M5:** `extract`, `correct_labels`,
    `overlay_ng_correct` (likely conditional).
  - **Thesis-shaped sub-problems:** JCT for polygons (§5.1), DCEL
    formalisation (§5.2).  Both candidates for deferral with
    conditional headline.
  - **Critical decisions:** §5.3 (output type) before S2; conditional
    vs unconditional before S9.
  - **Realistic landing:** `overlay_ng_correct_conditional` —
    Qed-closed with two named hypotheses, both registered as
    deferred-proof entries, mirroring
    `hobby_theorem_4_1_conditional`'s Phase 2 pattern.
