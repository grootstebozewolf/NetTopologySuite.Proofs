# Slice A Piece 5b Route 1 Session 2 prompt — cascade_step_preserves_invariant + bootstrap

**Target theorems.**
1. `cascade_step_preserves_invariant` — preservation lemma for the
   inductive cascade step under the upgraded `cascade_state` record.
   Estimated 150-300 lines of Coq (depends on case-split outcome).
2. `cascade_invariant_bootstrap` — the call-site bridge: shows that
   `fast_expansion_sum`'s initial cascade state satisfies
   `cascade_invariant` given the headline's preconditions
   (`nonoverlap_shewchuk e`, `nonoverlap_shewchuk f`,
   `fast_expansion_sum_safe e f`).  Estimated 30-80 lines.

The pair is what unblocks the headline composition (Session 3-4 work).

## Predecessor chain

- `a67c982` — Session 1 (Route 2 framework): `provenance`,
  `tagged_sort_by_abs`, structural bridges, `cascade_invariant` with
  `True` clause (c), `cascade_invariant_empty`.
- `6a2f988` — Session 2 of Route 2 (collapsed): three candidate
  clauses (c) all fail Task 2.
  `docs/slice-a-piece-5b-session-2-collapse.md`.
- `a7604f6` — Route 1 design session (red phase only):
  `cascade_state` choice (Form B record), Task 3 finds missing
  property (sign vs provenance gap),
  recommendation = h-chain as separate lemma.
  `docs/slice-a-piece-5b-route1-design-session.md`.
- `14012ef` / PR #8 — Route 1 green phase (this session's parent):
  `cascade_state` upgraded to record with `cs_carry` / `cs_prov` /
  `cs_output`, `cascade_invariant_empty` re-proved.

The previous Session 2 prompt
(`docs/slice-a-piece-5b-session-2-prompt.md`) was written for the
Route 2 framework and is **stale** — its red-phase tasks reference
the untagged `cascade_state` that no longer exists.  Reference it
only for the proof-structure intuition (§6.1-§6.5 of the
proof-structure doc), not the literal task list.

## Repository state at session start

- Branch off `main` (PRs #8 and #9 expected merged by start).
- Key files:
  - `theories-flocq/B64_FastExpansionSum_Shewchuk_Route2.v` —
    Form B record `cascade_state` with `cs_prov` field;
    `cascade_invariant` reads via accessors; clause (c) is `True`.
  - `theories-flocq/B64_FastExpansionSum_Shewchuk.v` —
    `fast_expansion_sum`, the untouched algorithm.  Note the call
    site for the cascade does NOT use `cascade_state` (Route 1 is
    "alongside" the algorithm); the bootstrap maps the algorithm's
    initial state to a `cascade_state` record in proof context only.
  - `theories-flocq/B64_FastExpansionSum.v` — the four
    `b64_TwoSum_step_dominates_*` lemmas (Qed-closed), the four
    arms' building blocks.
- Corpus: 4 Admitteds, all registered.  No new Admitteds expected
  from this session (success path).
- Toolchain: container path remains canonical for CI; host fallback
  documented in `docs/development-environment.md` (PR #9) for
  network-policy-blocked environments.

## Red phase — verify the case-split structure before any Coq

**The Route 1 design session (`a7604f6`) raised a structural
question that this session must answer before attempting the
proof.**  Do not skip the red phase — even though `cs_prov` is now
available, the design session's Task 3 documented a gap that needs
explicit resolution.

### Task 1.  Settle the case-split axis (sign vs provenance vs both).

The natural candidate, restated from the design session's analysis
of what the cascade needs:

```text
Case split on (cs_prov state, prov_x) -- four arms:
  (from_e, from_e) -> use b64_TwoSum_step_dominates_pos ?
  (from_f, from_f) -> use b64_TwoSum_step_dominates_neg ?
  (from_e, from_f) -> use b64_TwoSum_step_dominates_strict_pos ?
  (from_f, from_e) -> use b64_TwoSum_step_dominates_strict_neg ?
```

**The design session's Task 3 found this candidate has a structural
issue**: the four lemmas case-split on the **sign** of `B2R` values,
not on **provenance**.  `from_e` does not imply `0 < B2R x` — input
expansions to `fast_expansion_sum` can be signed (negative
components are routine in orient2d-derived expansions).

Resolve this before proceeding.  Three sub-options to evaluate:

**Sub-option 1A.** Augment the case-split to be a **product** of
sign × provenance: 4 sign-pair arms × 4 provenance-pair arms = 16
sub-cases.  Provenance arms supply magnitude bounds (via per-source
strict_succ chain) that discharge the strict_* preconditions; sign
arms select the lemma family.

**Sub-option 1B.** Restate the case-split as sign-only: 4 arms on
`(sign B2R cs_carry, sign B2R x)`.  Provenance does not pick a
lemma but is used to derive the magnitude bound on `|cs_carry|`
inside the proof.  Closer to what the lemmas actually require.

**Sub-option 1C.** Drop the explicit case-split entirely and prove a
generalised dominance lemma first (`b64_TwoSum_step_dominates_*`
unification), then derive `cascade_step_preserves_invariant` from
that.  Cleaner but requires new mathematical content.

Pick one.  State your choice with one paragraph of reasoning before
proceeding.

**Stopping condition for Task 1**: if none of 1A/1B/1C looks
tractable from the available corpus, name what's missing (as a Coq
Prop type, like the design session's Task 3 did) and stop.

### Task 2.  Check the strict_* precondition is dischargeable in the relevant arms.

Whichever case-split you chose in Task 1, identify the arms that
need `|cs_carry| < ulp(pred|succ B2R x)/2` (the strict_pos /
strict_neg precondition).  For each such arm, check whether
`cascade_invariant`'s clauses (a) and (b) plus the sorted/tagged
input's ordering guarantee plus `nonoverlap_shewchuk e` and
`nonoverlap_shewchuk f` provide enough to discharge the precondition.

**The design session's analysis predicts**:

- **Same-prov consecutive in the sorted merge** (i.e. no
  other-source element between the previous and current
  same-source element): strict precondition holds with a tight
  factor.  Tight enough that the **round-to-even boundary case**
  (`|q| = ulp(e)/2`, documented in
  `docs/stage-d-grow-expansion-nonoverlap-tangent.md`) may fail by
  a factor of 2.  Document this explicitly if it surfaces; it is
  not a new tangent, it is the known boundary.

- **Mixed-prov consecutive**: strict precondition can fail because
  `|q|` may be ≈ `|x|`.  Same-sign cases save via pos/neg.
  Mixed-sign mixed-prov similar-magnitude is the gap the design
  session named.

If your case-split (Task 1) cleanly handles same-prov but punts the
mixed-prov mixed-sign similar-magnitude case to a separate lemma,
that is **acceptable** — that lemma is the `cascade_h_chain`
follow-up.  Note explicitly which arms are tractable in this
session and which are not.

### Task 3.  Decide the h-chain scope for this session.

The design session's load-bearing recommendation: the h-chain
(`|h_{k-1}| <= ulp(h_k)/2` for consecutive cascade errors) is
**not** an invariant clause; it is a separate `cascade_h_chain`
lemma.

This session has two options:

**Option 3A.** Prove `cascade_step_preserves_invariant` for the
`True` clause (c), establishing the magnitude bounds (clause b) and
output well-formedness (clause a) only.  The h-chain (the actual
nonoverlap content of clause a's `nonoverlap_shewchuk`) is left to
a follow-up `cascade_h_chain` lemma that takes the preservation
result as a hypothesis.

**Option 3B.** Prove `cascade_step_preserves_invariant` **and** the
h-chain in one go, in this session.  Higher payoff but greater
risk: if the h-chain itself hits an obstacle (the design session's
Task 3 prediction), the session bails partway.

Recommended: **Option 3A** for risk-management.  Stop the moment
the h-chain content becomes an obstacle and produce a clean
`cascade_step_preserves_invariant` lemma.  Then a follow-up session
attempts the h-chain as a separate well-scoped target.

State your choice before proceeding.

## Green phase — proof structure

### Theorem statement (sketch — adjust to the chosen case-split)

```coq
Lemma cascade_step_preserves_invariant :
  forall (state : cascade_state)
         (processed : list binary64)
         (remaining : list tagged_b64)
         (x : binary64)
         (p : provenance)
         (remaining' : list tagged_b64),
    remaining = (x, p) :: remaining' ->
    cascade_invariant state processed remaining ->
    b64_TwoSum_safe x (cs_carry state) ->
    (* Plus any sort/nonoverlap hypotheses needed by your case-split. *)
    let '(qnew, h) := b64_TwoSum x (cs_carry state) in
    cascade_invariant
      (mk_cascade_state qnew p (h :: cs_output state))
      (x :: processed)
      remaining'.
```

`p` from the consumed tagged element becomes the new `cs_prov` — the
last-input-absorbed-into-carry provenance is `p` by construction.

### Bootstrap statement

```coq
Lemma cascade_invariant_bootstrap :
  forall (e f : list binary64),
    nonoverlap_shewchuk e ->
    nonoverlap_shewchuk f ->
    fast_expansion_sum_safe e f ->
    forall (head : tagged_b64) (rest : list tagged_b64),
      tagged_input e f = head :: rest ->
      cascade_invariant
        (mk_cascade_state (tagged_val head) (tagged_prov head) nil)
        nil
        rest.
```

The bootstrap maps the algorithm's untagged initial cascade state
(`b64_grow_expansion_aux head_untagged rest_untagged`) to a tagged
proof-context state, using `untag_tagged_input` (Qed-closed in
Session 1) to bridge.

### Composition

With both lemmas Qed-closed:

```coq
(* Iterate cascade_step_preserves_invariant through the tagged input,
   starting from cascade_invariant_bootstrap, to produce the final
   state's cascade_invariant.  Then read off clause (a)'s
   nonoverlap_shewchuk on the output. *)
```

The composition is Session 3 work, **not** this session.  This
session lands the per-step preservation and the bootstrap; Session
3 wires them together with the algorithm's actual output.

## Stopping conditions

**Success — preservation Qed-closed (Option 3A path)**:
`cascade_step_preserves_invariant` Qed-closed under the chosen
case-split.  Bootstrap Qed-closed.  CI gauntlet green.  Commit with
case-split structure named in the message.  Follow-up session
targets `cascade_h_chain`.

**Success — preservation + h-chain Qed-closed (Option 3B path)**:
Both proved.  Bootstrap Qed-closed.  Session 3 composition becomes
the next session's target.

**Refinement** (≤ 2-3 iterations): inductive case surfaces an
obligation that requires the case-split structure to be revised, or
a missing magnitude-bound hypothesis to be added to clause (c) or to
the lemma's preconditions.  Refine and retry.  At most 2-3 cycles
before treating as a collapse.

**Collapse**: the chosen case-split structure (Task 1's pick) hits an
obstacle the corpus doesn't resolve.  Produce a collapse artifact
modeled on `docs/slice-a-piece-5b-session-2-collapse.md`:

```
ROUTE 1 SESSION 2 COLLAPSE

Case-split chosen (Task 1): [sub-option 1A / 1B / 1C]
H-chain scope (Task 3): [3A or 3B]
Goal state at bail point: [verbatim Coq, full context]
Missing property: [Coq Prop type that would close the goal]
Is the missing property derivable from corpus + sort/nonoverlap?
  [yes -> add as conjunct in clause (c) and retry]
  [no  -> recommend successor design session]
```

Commit the artifact.  Do not attempt a redesign in this session — a
fresh session with this artifact as input is the correct procedure.

## Discipline notes

- The design session's Task 3 finding is the **load-bearing risk**:
  sign vs provenance.  Red phase Task 1 must explicitly resolve it
  before the green phase begins.  Skipping Task 1 risks a third
  round of the same structural mistake.
- **No new Admitteds** in the success path.  The `cascade_h_chain`
  follow-up does not get an Admitted-placeholder in this session; it
  is named in the commit message as the next target.  A new
  Admitted only lands when its proof structure is documented (per
  the three-tier system).
- The Route 2 framework
  (`B64_FastExpansionSum_Shewchuk_Route2.v` lines 55-220:
  `provenance`, `tagged_sort_by_abs`, `untag_tagged_input`, length
  lemmas) is reused as-is.  No edits to those lines.
- The Form B record choice is settled — do not revisit it in this
  session.  Adding fields to `cascade_state` requires its own
  design pass with the same rigor PR #7 applied.

## Session count remaining (post this session)

Assuming success on this session:

- **Session 3**: composition — wire `cascade_invariant_bootstrap` +
  `cascade_step_preserves_invariant` (iterated) through the actual
  cascade to derive `fast_expansion_sum_nonoverlap_shewchuk`.  Pull
  the deferred-proof registry entry.  Estimated 100 lines.
- **Session 4 (only if Option 3A)**: `cascade_h_chain` as a separate
  lemma.  Estimated 200-300 lines depending on whether
  mixed-prov mixed-sign similar-magnitude requires the
  documented-boundary-case escape valve (compress).
- **Session 5 (cleanup)**: any deferred audits, README update,
  documentation pass.

One session, one principled stop, one artifact.
