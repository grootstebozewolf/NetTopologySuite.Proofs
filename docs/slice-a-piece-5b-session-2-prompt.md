# Slice A Piece 5b Session 2 prompt — cascade_step_preserves_invariant

**Target.** `cascade_step_preserves_invariant` in (or adjacent to)
`theories-flocq/B64_FastExpansionSum_Shewchuk_Route2.v`.  Estimated
200-300 lines.

**Predecessor.** Session 1 (commit `a67c982`) landed the Route 2
framework: `provenance`, `tagged_sort_by_abs`, structural lemmas
(`untag_tagged_input`), and the `cascade_invariant` predicate with
clause (c) as a `True` placeholder.  Session 1 is the foundation; this
prompt is the next milestone.

**Successor.** Session 3-4 will bootstrap the invariant from the
headline preconditions and compose into
`fast_expansion_sum_nonoverlap_shewchuk` (the deferred-proof Admitted
theorem in `B64_FastExpansionSum_Shewchuk.v`).

## Red phase — before writing any Coq

The red phase has three tasks.  Complete all three before the green
phase begins.

### Task 1.  State candidate clause (c) precisely.

Clause (c) is currently `True` in
`B64_FastExpansionSum_Shewchuk_Route2.v`.  Its content is what the
mixed-provenance inductive step of `cascade_step_preserves_invariant`
needs.

The candidate should capture: the relationship between the cascade's
current accumulator `q` and the next tagged input `(x, p)` that allows
the next TwoSum step `b64_TwoSum x q = (qnew, h)` to preserve the
output's `nonoverlap_shewchuk` property.

Concretely, write a candidate like:

```coq
Definition cascade_invariant_handover
  (q : binary64) (remaining : list tagged_b64) : Prop :=
  match remaining with
  | nil => True
  | (x, p) :: _ =>
      (* Some relationship between q and x, possibly conditioned on    *)
      (* whether p matches the provenance of the previously processed *)
      (* input.                                                         *)
      ...
  end.
```

The candidate should NOT be derived bottom-up from what feels natural;
it should be derived top-down from what
`cascade_step_preserves_invariant` requires at the inductive step.  In
practice: sketch the proof's mixed-provenance case on paper, identify
what hypothesis on `(q, x)` would close the step, and that's clause (c).

### Task 2.  Test clause (c) against the §6.5 risk.

The proof structure doc's §6.5 risk analysis names the pivot condition:
if clause (c) collapses back to requiring the full `strict_succ_b64`
chain on the input list (the property
`docs/shewchuk-theorem-13-proof-structure.md` §2.1 already showed is
NOT satisfied by `sort_by_abs (e ++ f)`), Route 2 has collapsed and
Route 1 (cascade-state augmentation) is the next direction.

To test the candidate:
  1. Look at the source preconditions: `nonoverlap_shewchuk e` and
     `nonoverlap_shewchuk f`.
  2. Look at the tagged sort's guarantees: `sorted_asc` on the
     untagged list, and same-provenance pairs come from the same input
     list (so they satisfy that input's `nonoverlap_shewchuk`).
  3. Check: does the candidate clause (c) follow from these, plus the
     already-Qed-closed `b64_TwoSum_step_dominates_*` lemmas, when the
     cascade is at the relevant position?

If yes (clause (c) is derivable from the source + building blocks):
the preservation proof is tractable.  Proceed to Task 3, then the
green phase.

If no (clause (c) requires the full strict_succ_b64 chain on the
input, or some other property that doesn't follow from
nonoverlap_shewchuk-per-list): Route 2 has collapsed.  Stop.  Write a
short "Route 2 collapse" doc capturing the candidate clause (c) and
the missing property, and open a fresh design session for Route 1.

### Task 3.  Re-check `cascade_invariant_empty` after clause (c) refinement.

Session 1's `cascade_invariant_empty` proved the initial state
(`q = head of tagged_input`, `hs = nil`, `remaining = tail of tagged_input`)
satisfies the invariant when clause (c) is `True`.  Once clause (c) is
refined to its candidate form, re-prove `cascade_invariant_empty`.

If the initial state DOESN'T satisfy the refined clause (c), either:
  - The clause is too strong for the bootstrap case (refine further).
  - The bootstrap needs additional preconditions (likely from
    `nonoverlap_shewchuk e + nonoverlap_shewchuk f` — pass them
    through).

The re-check is a forcing function: it surfaces whether the candidate
clause (c) is compatible with the initial state before the preservation
proof attempts a 200-300 line case analysis.

## Green phase — cascade_step_preserves_invariant

With clause (c) refined, attempt:

```coq
Lemma cascade_step_preserves_invariant :
  forall (q : binary64) (hs : list binary64)
         (x : binary64) (p : provenance)
         (xs' : list tagged_b64)
         (processed : list binary64),
    cascade_invariant (q, hs) processed ((x, p) :: xs') ->
    b64_TwoSum_safe x q ->
    let '(qnew, h) := b64_TwoSum x q in
    cascade_invariant (qnew, h :: hs) (x :: processed) xs'.
```

(Exact statement may vary based on what clause (c) ends up needing;
the signature here is illustrative.)

Case analysis structure:
  - **Same-provenance with previous input**.  `(x, p)` and the last
    processed element share provenance.  Use the source list's
    `nonoverlap_shewchuk` (transported through the tagged sort) to
    derive the strict_succ_b64 chain.  Apply
    `b64_TwoSum_step_dominates_pos` / `_neg` / `_same_sign` /
    `_q_zero` / `_strict_pos` / `_strict_neg` per sign sub-case.
  - **Mixed-provenance with previous input**.  Apply clause (c)'s
    guarantee directly.  If clause (c) was well-chosen, this case
    closes with the existing building blocks + the clause itself.
  - **First step** (`hs = nil`, `processed = nil`).  Bootstrap from
    the initial state's clause (c).

## Stopping conditions

  1. **Success**: all three clauses preserved through one step.
     Commit, update the proof structure doc's resumption checklist,
     proceed to Session 3.
  2. **Mixed-provenance case opens**: the case analysis surfaces a
     subgoal that clause (c) doesn't discharge, but a refined clause
     (c') would.  Refine clause (c), re-prove
     `cascade_invariant_empty`, retry.  Bound the refinement loop at
     2-3 iterations -- if clause (c) keeps getting more elaborate,
     the design has a problem and Route 2 may be collapsing.
  3. **Route 2 collapse**: clause (c) requires the full
     strict_succ_b64 chain on the input (the documented impossibility)
     or some other property that doesn't follow from per-list
     nonoverlap_shewchuk.  Stop.  Write the collapse doc, frame Route
     1 session.

## Out of scope for this session

  - Session 3-4 work: bootstrapping the cascade through the full input
    list by induction, composing into the headline theorem, removing
    the entry from `docs/admitted-deferred-proofs.txt`.
  - Refactoring `b64_grow_expansion_aux` to take tagged inputs
    (Route 1).  Only consider if the Route 2 collapse condition fires.
  - Optimizing the same-provenance proof to share structure (the
    pos/neg/zero sub-cases) — straight-line repetition is fine for
    a first pass.

## Resumption note

When this session starts, the assistant should:
  1. Read this prompt in full.
  2. Read
     `docs/shewchuk-theorem-13-proof-structure.md` §6.1-§6.5
     (the Route 2 design).
  3. Confirm Session 1 is still Qed-closed in the corpus.
  4. Begin Task 1 of the red phase.  Do NOT skip to the green phase
     even if a candidate clause (c) feels obvious.

The red phase's first-class artifact is the candidate clause (c) +
risk-analysis test.  Without those, the green phase is exposed to the
documented multi-session risk.
