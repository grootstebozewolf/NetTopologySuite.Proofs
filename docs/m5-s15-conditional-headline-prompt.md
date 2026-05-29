# Phase 3 Milestone 5 Session 15 — `overlay_ng_correct_conditional`

## Purpose

Close the **Phase 3 headline theorem** as a Qed-closed conditional
theorem.  Same epistemic shape as `hobby_theorem_4_1_conditional`
(Phase 2): both load-bearing thesis-scale gaps (JCT for polygons + DCEL
ring assembly) are carried as named hypotheses; the structural
composition is fully Qed-closed.

Self-contained.  Does not require prior conversation context.

## Environment setup — do this first

```sh
source .claude/startup-rocq.sh   # Rocq 9.1.1 + Flocq 4.2.2, build clean.
./scripts/check_admitted.sh      # baseline: 5 Admitted, all registered.
./scripts/audit_axioms.sh        # baseline: allowlist clean.
```

Confirm clean baseline before writing any Coq.

## Background — what the previous sessions established

Phase 3 M5 Sessions 2–8 (PRs #31–#36, all merged to main) landed:

  - **S2**: `extract op g` (theories/OverlayGraph.v) — filters edges
    by `edge_in_result op l`, then emits a `Geometry` that is either
    `[]` (no surviving edge) or a *single* degenerate polygon whose
    `outer_ring` is the `flat_map` concatenation of the endpoints
    (`fst`/`snd`) of all surviving edges, with `hole_rings := []`.
    Edge labels are dropped at this step.  No DCEL.  Naive carrier
    (`Geometry`).
  - **S2.5**: M4 refactor — `merge_labeled_edges` collapses duplicate
    `(p, q)` pairs into single edges with OR-combined labels.
    `build_labeled_graph` rewritten to use it.
  - **S3 + S3.5**: full bidirectional `merge_in_left_iff`,
    `merge_in_right_iff` (theories/OverlayGraph.v).  Forward and
    backward directions both Qed-closed.
  - **S4–S7** (consolidated): `correct_labels_{union, intersection,
    difference, symdiff}` (theories-flocq/OverlayBridge.v).  All four
    Qed-closed via the same proof pattern (helper iff lemmas
    `in_left_iff_in_A` / `in_right_iff_in_B` composed with Boolean
    algebra).
  - **S8**: JCT search complete (Path B).  No JCT formalisation
    found in the available opam ecosystem; gap recorded in audit
    doc §4.2, no Admitted added to Coq.  Coq deliverable:
    `correct_labels_all_ops` (case-on-op uniform composition).

NOT yet done (depends on this session's decisions):

  - **S9**: `extract_rings_valid` — structural correctness of
    `extract`'s output rings (thesis-shaped under flat-list `extract`;
    Admitted + registry entry the realistic landing).
  - **S10**: `valid_geometry (extract op g)` — conditional on S9.
  - **S11–S14**: split or compress per S15's framing decision below.

## Framing decision — pick before any Coq

Two ways to land S15:

**Path A: Bottom-up (S9 → S10 → S13 → S14 → S15)**.  Land each piece
separately.  Total: 4-5 sessions.  Each piece smaller and reviewable.
S15 itself becomes a clean composition session (~50 lines).

**Path B: Top-down (single S15 = conditional headline + named gaps)**.
State `overlay_ng_correct_conditional` directly with `extract_rings_valid`
and `point_in_ring_correct` (or its restatement) as explicit
hypotheses.  Discharge structurally.  Total: 1 session for the
headline + 1 more if intermediate lemmas surface.

**Recommendation: Path B.**  Both gaps are thesis-scale (audit doc
§5.1 + §5.2); landing S9/S10 standalone duplicates the conditional
shape without buying structural ground.  Path B's conditional headline
is the same epistemic state as `hobby_theorem_4_1_conditional`.

If Path B's structural unwinding surfaces an intermediate lemma that
benefits from its own session, stop and write a follow-up prompt for
it — do not try to inline it in this session.

## The theorem to prove

```coq
Theorem overlay_ng_correct_conditional :
  forall (A B : Geometry) (op : BooleanOp) (p : Point),
    valid_geometry A ->
    valid_geometry B ->
    fully_intersected (noded_segments A B) ->
    (* Hypothesis 1 (DCEL gap): extract assembles valid polygons.    *)
    (forall poly,
       In poly (extract op (noded_labeled_graph A B)) ->
       valid_polygon poly) ->
    (* Hypothesis 2 (JCT gap): point_in_ring iff topological interior. *)
    (* See note below on the exact statable form.                    *)
    (forall (q : Point) (r : Ring),
       ring_closed r -> ring_simple r ->
       point_in_ring q r <-> some_interior_predicate q r) ->
    point_set (extract op (noded_labeled_graph A B)) p <->
    boolean_op op A B p.
```

**Note on Hypothesis 2.**  `geometric_interior` is not defined in the
corpus (no JCT toolkit).  Options:

  - **Option H2a**: state Hypothesis 2 as a Coq-internal equivalence
    between two `Prop`s expressible without external topology --
    e.g. `point_in_ring q r <-> point_in_ring q (canonical r)` (a
    self-bridge).  This is provable for the cases where it matters
    (extract's rings vs A/B's rings under correct_labels) without
    referencing topological interior.
  - **Option H2b**: introduce a `Parameter geometric_interior :
    Point -> Ring -> Prop` (FORBIDDEN by corpus invariant -- do not
    take this path).
  - **Option H2c**: introduce an opaque `Variable` inside the
    theorem statement (Section-scoped).  Discharged by consumers
    providing the concrete predicate.

**Pick H2a or H2c during the red phase.**  The audit doc §6's
formulation uses `geometric_interior` as a stand-in; the concrete
statable form is the load-bearing design decision for S15.

## Red phase — before any Coq

State Hypothesis 2 precisely as a Coq Prop.  Write the full Theorem
statement at the top of a stub file in the workspace (do NOT add to
OverlayBridge.v yet -- keep the file scratch-local until the proof
closes).  Verify it type-checks.

Then: write down the proof shape on paper.

**Forward direction** (`point_set ... p -> boolean_op op A B p`):

  1. Unfold `point_set (extract op g) p`: there exists a polygon
     `poly` in the extracted geometry such that `point_in_polygon p
     poly`.
  2. Unfold `point_in_polygon`: `point_in_ring p (outer_ring poly) /\
     not (any hole contains p)`.
  3. Use Hypothesis 1 to get `valid_polygon poly`.
  4. Use Hypothesis 2 to convert `point_in_ring p r` to the
     topological-interior form.
  5. NOTE: `extract` drops labels — the polygon's `outer_ring` is the
     endpoint concatenation of the *filtered labelled edges* of
     `noded_labeled_graph A B` (those `e` with
     `edge_in_result op (snd e) = true`), NOT a labelled-edge list.
     So step 6 cannot read labels off the ring directly; it must work
     from the filtered labelled edges in the graph and relate the ring
     boundary back to them.  This relation is an *extra hypothesis*
     (call it `ring_edges_from_filtered`: each boundary segment of
     `outer_ring poly` is the `(fst, snd)` of some surviving labelled
     edge, and the ring introduces no spurious adjacency segments) —
     it must be stated explicitly, as it does not follow from
     `extract` alone for the flat-list carrier.
  6. Use `correct_labels_all_ops` on those *filtered labelled edges*:
     each surviving edge `(p, q, l)` with `edge_in_result op l = true`
     satisfies `edge_geometrically_in_result op p q A B`.  Combined
     with the step-5 hypothesis, every boundary segment of the
     extracted polygon is geometrically in the result.
  7. The boundary edges geometrically come from A's or B's snapped
     segments (combined per `op`'s combinator).  This is the bridge
     from per-edge geometric membership to per-region containment.
  8. Conclude `boolean_op op A B p`.

Step 7 is the load-bearing point in the forward direction.  Likely
sub-lemma: `point_in_polygon_implies_in_source_geometry`.

**Backward direction** (`boolean_op op A B p -> point_set ... p`):

  1. From `boolean_op op A B p`: `p` is in A's point-set, or B's, or
     both, per `op`'s combinator.
  2. By A's `valid_geometry` + `point_in_polygon` definitions, `p`
     is inside some polygon of A (or B).  Call this `poly_AB`.
  3. The extracted geometry's rings come from edges labelled `op`-true
     on `noded_labeled_graph A B`.  Those edges include
     `poly_AB`'s boundary (snapped via `noded_segments`).
  4. Hypothesis 1 ensures the extracted polygon containing those
     edges is valid.
  5. Hypothesis 2 converts `p`'s containment in `poly_AB` (via
     `point_in_ring`) to containment in the extracted polygon (via
     the same `point_in_ring` on the extracted ring).
  6. Conclude `point_set (extract op g) p`.

Step 3 is the load-bearing point in the backward direction.  Likely
sub-lemma: `source_polygon_boundary_in_extracted_edges`.

If either step 3 (backward) or step 7 (forward) doesn't admit a
direct Coq proof from the existing infrastructure, STOP and write a
follow-up prompt rather than trying to bash through inline.

## Deliverables (in order, stop after first one that doesn't close)

### Deliverable 1: state Hypothesis 2 in Coq, type-check the theorem.

  - In a scratch file or directly in OverlayBridge.v at the bottom.
  - Pick H2a or H2c.  Document the choice in a `(* DESIGN: ... *)`
    comment immediately above the Theorem.
  - Verify the Theorem statement type-checks (do NOT start `Proof.`
    yet -- just compile the stub).

Stop if H2 can't be cleanly stated -- raise as a design question.

### Deliverable 2: forward direction (`point_set -> boolean_op`).

  - Aim: ~80-150 lines.
  - Land as a separate Lemma `overlay_correct_forward` immediately
    above the headline.
  - Print Assumptions at the end -- should show only allowlisted
    axioms + the two hypotheses (carried through as opaque
    quantifications).

Stop if the load-bearing step 7 surfaces an unanticipated sub-lemma.

### Deliverable 3: backward direction (`boolean_op -> point_set`).

  - Aim: ~80-150 lines.
  - Land as Lemma `overlay_correct_backward`.
  - Print Assumptions check as above.

Stop if step 3 surfaces an unanticipated sub-lemma.

### Deliverable 4: compose into `overlay_ng_correct_conditional`.

  - ~5-10 lines.  Just `split; [apply overlay_correct_forward |
    apply overlay_correct_backward]`.
  - Print Assumptions: should show only the two hypotheses +
    classical-reals allowlist.

### Deliverable 5 (cleanup): audit-doc update.

  - Update `docs/audit-phase3-milestone5.md` §9's table: mark
    `overlay_ng_correct_conditional` as DONE in S15.
  - Note in §6 that the conditional landed; document the H2
    framing choice.
  - No new deferred-proof entries unless H2 turns out non-statable
    without an opaque `Variable` and you take Path H2c with a
    documented gap.

## Stopping conditions

  - **Hard stop**: any deliverable fails to close in <300 lines.
    Write the goal state to a follow-up prompt and stop.
  - **Hard stop**: any sub-lemma surfaces that needs its own multi-
    session work (e.g. ring-traversal correctness, planar-graph
    Euler).  Document and stop.
  - **Hard stop**: H2 cannot be stated without a Parameter/Axiom.
    Stop and ask for design guidance.
  - **Soft stop**: deliverable closes but with assumption pull beyond
    the README allowlist.  Investigate; if the leak is from a snap-
    layer transitive (`Classical_Prop.classic` via Flocq's round),
    this is expected -- add to audit-exceptions.txt with rationale.
    If the leak is from elsewhere, stop.

## Repository state at session start

  - Branch: create `claude/phase3-m5-s15-conditional-headline`
    from main.
  - Main contains S2-S8 (commits up to 368ceb3 + 9c8b2ba registry
    update).
  - `theories/OverlayGraph.v` (1169 lines): all merge-iff lemmas
    Qed-closed.
  - `theories-flocq/OverlayBridge.v` (458 lines): `correct_labels_all_ops`
    Qed-closed.
  - `docs/audit-phase3-milestone5.md`: tracks the 16-session plan;
    §9 audit table shows S15 as pending Qed-target.
  - Deferred-proof registry: 2 entries (Shewchuk + hobby_lemma_4_3_no_proper).

## Cost estimate

  - 1 session if both directions admit direct composition under
    Path B's H2a framing.
  - 2 sessions if the backward direction's step 3 surfaces a
    sub-lemma needing its own work.
  - Beyond 2 sessions: pivot back to Path A and land S9-S14
    individually.

## Discipline

  - Do not add Admitteds in this session.  Either close cleanly or
    stop and document.
  - Do not extend `extract`, `point_set`, `point_in_ring`,
    `boolean_op` definitions in this session.  All structural
    progress must compose existing definitions.
  - Do not pull in new axioms.  README allowlist is the contract.
  - Commit message convention: `feat: overlay_ng_correct_conditional
    -- Phase 3 M5 S15`.

## References

  - `docs/audit-phase3-milestone5.md` §6 (conditional strategy),
    §7 (16-session plan), §9 (audit table).
  - `theories/Overlay.v`: `point_set`, `point_in_polygon`,
    `point_in_ring`, `boolean_op`, `valid_geometry`, `valid_polygon`.
  - `theories/OverlayGraph.v`: `extract`, `edge_in_result`,
    `build_labeled_graph`, `merge_labeled_edges`.
  - `theories-flocq/OverlayBridge.v`: `noded_segments`,
    `noded_labeled_graph`, `correct_labels`, `correct_labels_all_ops`.
  - `theories-flocq/HobbyTheorem_b64.v` §6: `hobby_theorem_4_1_conditional`
    as the structural template (same conditional-headline pattern).
