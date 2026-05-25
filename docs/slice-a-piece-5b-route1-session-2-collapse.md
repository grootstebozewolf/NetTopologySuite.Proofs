# Slice A Piece 5b Route 1 Session 2 — collapse artifact

**Session.** Route 1 Session 2 attempt to close
`cascade_step_preserves_invariant` + `fast_expansion_sum_bootstrap`.
Branch `claude/cascade-invariant-bootstrap-8oSDv`.

**Outcome.** ROUTE 1 SESSION 2 COLLAPSE.

This document is the collapse artifact required by the session prompt's
stopping condition.  It records:

  - The Task-1 option chosen (red phase).
  - The refined clause (c) in Coq form (Task 2).
  - The Qed-closed `cascade_invariant_empty` re-proof under the refined
    clause (c) (Task 3).
  - The Coq attempt at `cascade_step_preserves_invariant` (green phase).
  - The verbatim goal state at the bail point.
  - The missing property as a Coq Prop type.

Unlike the prior Route 1 design session (which was paper-only because
the container was unavailable), this session ran against a working host
toolchain (Rocq 9.1.1 + Flocq 4.2.2 installed per
`docs/development-environment.md`) and reached a green-phase bail in Coq.
The goal state below is extracted from a live `rocq c` session, not
paper analysis.

## Environment

Host toolchain (Ubuntu 24.04, no Docker access required):

  - `opam 2.1.5-1` + `ocaml 4.14.1` from `archive.ubuntu.com`.
  - `rocq-core.9.1.1` + `rocq-stdlib.9.0.0` from `opam.ocaml.org`.
  - Flocq `4.2.2` built from `gitlab.inria.fr/flocq/flocq` (tag
    `flocq-4.2.2`) against the opam-installed Rocq.
  - Corpus baseline (`make -f Makefile.gen -j4`) passes.
  - CI gauntlet (`check_admitted`, `audit_axioms`, `check_readme_axioms`)
    passes.

## Task 1 — option chosen

**Option 1B (sign-only, 4-arm) extended to 5-arm with zero-carry and
strict-magnitude cases.**

Reading the `b64_TwoSum_step_dominates_*` family in
`theories-flocq/B64_FastExpansionSum_Shewchuk.v:327-481`, the
preconditions case-split on **sign of `B2R x`** and **sign of `B2R q`**,
plus a strict-magnitude bound `|q| < ulp(pred|succ x) / 2` for the
mixed-sign cases.  The lemmas do **not** mention provenance.

Why not 1A (16-arm provenance × sign): the 16-arm form has redundant
arms — provenance is hypothesis context for *deriving* the strict
magnitude bound, not for the case split that picks the lemma.  Same
underlying disjunction with extra unused destructs.

Why not 1C (generalised dominance): provably false in mixed-sign
cancellation per the Route 1 design artifact's concrete counterexample
(`B2R e = 1.0`, `B2R q ≈ -0.999...` gives `|qnew| ≈ 10^-9 << |q|`).

## Task 2 — refined clause (c)

Lives at
`theories-flocq/B64_FastExpansionSum_Shewchuk_Route2.v` (committed in
this session).  Verbatim:

```coq
Definition cascade_invariant_handover
  (state : cascade_state) (remaining : list tagged_b64) : Prop :=
  match remaining with
  | nil => True
  | (x, _) :: _ =>
      let q  := cs_carry state in
      let qR := Binary.B2R prec emax q in
      let xR := Binary.B2R prec emax x in
      b64_TwoSum_safe x q /\
      ( (0 < qR /\ 0 < xR)
        \/ (qR < 0 /\ xR < 0)
        \/ qR = 0
        \/ (0 < xR /\ Rabs qR <
              ulp radix2 (SpecFloat.fexp prec emax)
                (pred radix2 (SpecFloat.fexp prec emax) xR) / 2)
        \/ (xR < 0 /\ Rabs qR <
              ulp radix2 (SpecFloat.fexp prec emax)
                (succ radix2 (SpecFloat.fexp prec emax) xR) / 2) )
  end.
```

The strongest clause (c) provable from the `dominates_*` family alone:
the next TwoSum step's dominance can be discharged by one of the five
existing building blocks.

## Task 3 — `cascade_invariant_empty` re-proved

Qed-closed in the file with the handover as a hypothesis:

```coq
Lemma cascade_invariant_empty :
  forall q p remaining,
    cascade_invariant_handover (mk_cascade_state q p nil) remaining ->
    cascade_invariant (mk_cascade_state q p nil) nil remaining.
```

The hypothesis is what the bootstrap (`fast_expansion_sum_bootstrap`,
not in scope for this session) would discharge from the input
preconditions.

## Green phase — `cascade_step_preserves_invariant` attempted

Lemma statement (in the file, terminated with `Abort.`):

```coq
Lemma cascade_step_preserves_invariant :
  forall (state : cascade_state)
         (processed : list binary64)
         (x : binary64) (prov : provenance)
         (rest : list tagged_b64),
    cascade_invariant state processed ((x, prov) :: rest) ->
    cascade_invariant
      (mk_cascade_state
         (fst (b64_TwoSum x (cs_carry state)))
         prov
         (cs_output state ++ [snd (b64_TwoSum x (cs_carry state))]))
      (processed ++ [x])
      rest.
```

(The new `h` is **appended** to `cs_output` rather than prepended, so
the oldest-first convention is preserved; the session-prompt's
prepend version requires changing `cascade_invariant_output` from
`q :: rev hs` to `q :: hs`, which is an equivalent reformulation.)

Proof was driven to the clause-(a) sub-obligation by destructuring the
hypothesis into Ha (output), Hb (magnitude), Hsafe + Hcases (the
handover's two conjuncts), then `rewrite rev_app_distr` to expose the
output's shape.

### Verbatim goal state at the bail point

Extracted from `rocq c` (Rocq 9.1.1, Flocq 4.2.2):

```text
1 goal

  state : cascade_state
  processed : list binary64
  x : binary64
  prov : provenance
  rest : list tagged_b64
  Ha : nonoverlap_shewchuk (cs_carry state :: rev (cs_output state))
  Hb : cascade_invariant_magnitude (cs_carry state) processed
  Hsafe : b64_TwoSum_safe x (cs_carry state)
  Hcases :
    0 < Binary.B2R prec emax (cs_carry state) /\ 0 < Binary.B2R prec emax x \/
    Binary.B2R prec emax (cs_carry state) < 0 /\ Binary.B2R prec emax x < 0 \/
    Binary.B2R prec emax (cs_carry state) = 0 \/
    0 < Binary.B2R prec emax x /\
    Rabs (Binary.B2R prec emax (cs_carry state)) <
    b64_ulp (pred radix2 b64_fexp (Binary.B2R prec emax x)) / 2 \/
    Binary.B2R prec emax x < 0 /\
    Rabs (Binary.B2R prec emax (cs_carry state)) <
    b64_ulp (succ radix2 b64_fexp (Binary.B2R prec emax x)) / 2
  ============================
  nonoverlap_shewchuk
    (fst (b64_TwoSum x (cs_carry state))
     :: snd (b64_TwoSum x (cs_carry state)) :: rev (cs_output state))
```

### Decomposition of the goal

Let `qnew := fst (b64_TwoSum x q_old)` and `h := snd (b64_TwoSum x q_old)`
where `q_old := cs_carry state`.  Writing
`rev (cs_output state) = [h_prev; h_{prev-1}; ...]` (newest h_prev
first, oldest h last), `nonoverlap_shewchuk (qnew :: h :: rev hs)`
decomposes (after compress) into three chains:

  1. `strict_succ_b64 qnew h`         — `|h| <= ulp(qnew)/2`.  This is
     a structural property of `b64_TwoSum` (TwoSum's "low-bits of the
     sum") and is **provable**, though not directly stated in the
     existing corpus.
  2. `strict_succ_b64 h h_prev`       — `|h_prev| <= ulp(h)/2`.  **This
     is the H-CHAIN.**  Consecutive cascade errors must satisfy a
     half-ulp domination.  **NOT in clause (c), NOT in Ha, NOT
     derivable from the dominates_* family.**
  3. Rest of chain over `rev (cs_output state)` — inherited from Ha.

Link (2) is Shewchuk Theorem 13's load-bearing magnitude claim.  It
relates `h_prev` (produced at step `k`) to `h` (produced at step
`k+1`) and requires:

  - `|h_prev|` is small (bounded by what was absorbed at step `k`).
  - `|h|` is large enough that `|h_prev| <= ulp(h)/2` — i.e., `|h|`'s
    binade is far enough above `|h_prev|`'s binade.

In the same-source-consecutive case (no f-element between the two e
elements), nonoverlap_shewchuk on `e` gives `|x_curr|/|x_prev| >= 2^53`
roughly, so `|h_prev| ≈ ulp(x_prev)/2` and `|h| ≈ ulp(x_curr)/2`,
yielding the required ratio.  In the mixed-source consecutive case
(elements alternate between `e` and `f`), the sort only guarantees
`|x_curr| >= |x_prev|` — a constant factor, not 2^53.  Then
`|h_prev|` and `|h|` can be at the same binade and link (2) fails.

This is exactly the Route 1 design artifact's "mixed-prov consecutive"
case (`docs/slice-a-piece-5b-route1-design-session.md` §Task 3),
re-encountered as a live Coq subgoal.

### Why this doesn't close

The refined clause (c) talks about the relationship between `q_old`
and the **next** input `x` (the cascade's *next* step).  It says
nothing about how the **previous** step's error `h_prev` (now at the
head of `rev (cs_output state)`) will relate to the **new** error `h`.
But the inductive preservation of clause (a) needs exactly that —
link (2) above — to keep the half-ulp chain intact when prepending
`h` to the descending chain of stored h's.

The h-chain is a property of the cascade's *step transition*, not of
the state.  `cs_prov` and `Hcases` give the right context to *derive*
the h-chain for specific same-source-consecutive transitions, but no
shape of clause (c) over `(state, remaining)` propagates link (2)
inductively, because the new `h_prev` after step `k+1` is the
just-produced `h` — different from the `h_prev` available at step
`k`.  The invariant cannot "remember" properties about a value that
keeps being replaced by the most recent step.

### Clause (b) also has a structural gap

For completeness: the clause (b) sub-obligation
`Rabs (B2R qnew) <= max_abs_b64 (processed ++ [x])` is **also**
non-trivial under the current invariant.  `|qnew| <= |x| + |q_old|`
(triangle bound) gives at best `|qnew| <= 2 * max_abs_b64 (processed ++ [x])`,
not the exact `max_abs_b64` bound.  Tightening clause (b) to use a
`2x` slack would require re-proving its consumers; it would not by
itself unblock clause (a)'s h-chain.

## Missing property — Coq Prop type

The h-chain claim, stated as a Coq Prop the next session would need
to establish (NOT as an invariant clause, but as a separate
cascade-step lemma per the Route 1 design artifact's recommendation):

```coq
Lemma cascade_h_chain :
  forall (state : cascade_state)
         (processed : list binary64)
         (x : binary64) (prov_x : provenance)
         (rest : list tagged_b64)
         (h_prev : binary64) (hs_tail : list binary64),
    (* The invariant before this step. *)
    cascade_invariant state processed ((x, prov_x) :: rest) ->
    (* The previous step's h is at the head of (rev cs_output). *)
    cs_output state = hs_tail ++ [h_prev] ->
    (* Per-source nonoverlap on e and f. *)
    forall (e f : list binary64),
      nonoverlap_shewchuk e ->
      nonoverlap_shewchuk f ->
      (* sort_by_abs_sorted on the merge gives ascending magnitudes. *)
      sorted_asc (untag (tagged_input e f)) ->
      (* h_prev was produced at step k consuming the previous tagged   *)
      (* element with provenance (cs_prov state); x is the next      *)
      (* element with provenance prov_x.                              *)
      (* CONCLUSION: the new h dominates h_prev in the half-ulp       *)
      (* sense.                                                       *)
      Rabs (Binary.B2R prec emax h_prev) <=
        ulp radix2 (SpecFloat.fexp prec emax)
          (Binary.B2R prec emax
             (snd (b64_TwoSum x (cs_carry state)))) / 2.
```

The hypotheses include the input preconditions
(`nonoverlap_shewchuk e/f`, sorted merge) so that the same-source case
can use the 2^53 gap and the mixed-source case can be argued via
Shewchuk Theorem 13's deep magnitude bookkeeping.  This is the
**~200-400 line core** of Theorem 13, restated in cascade form.

Note: this missing property is **identical in substance** to the one
identified by the Route 2 collapse artifact
(`docs/slice-a-piece-5b-session-2-collapse.md`) and the Route 1 design
artifact (`docs/slice-a-piece-5b-route1-design-session.md`).  All three
sessions converge on the same conclusion: the h-chain is Shewchuk
Theorem 13's load-bearing content and cannot be elided by a clever
state predicate.

## Collapse summary (prompt format)

```
ROUTE 1 SESSION 2 COLLAPSE

Option chosen: 1B (sign-only, extended to 5-arm with q_zero and the
two strict-magnitude cases).  This is the strongest form provable
from the existing dominates_* family alone.

Refined clause (c): (verbatim above in Task 2)

Goal state at bail point: (verbatim above; clause (a) preservation
sub-obligation; head sub-link is `strict_succ_b64 h h_prev` where
`h := snd (b64_TwoSum x (cs_carry state))` and `h_prev :=` last of
`cs_output state`)

Why this doesn't close: the h-chain link between consecutive cascade
errors is a property of the algorithm's STEP transition, not of the
state.  No shape of clause (c) over `(state, remaining)` propagates
the link inductively, because the "previous error" changes at every
step.  cs_prov is hypothesis context that helps derive the h-chain
for specific cases, but does not turn the h-chain into a state
predicate.

Missing property: cascade_h_chain (signature above).  Identical in
substance to the property named by the Route 2 collapse and the
Route 1 design session.  Estimated 200-400 lines of Coq, requires
deep magnitude case analysis on provenance + sign + binade position.
```

## Recommendation for a successor session — Option B with run-bound conjunct

> **Updated 2026-05-25 after the §4 run-bound analysis** (see commit
> log of this branch).  The earlier "third design" pointer (separate
> `cascade_h_chain` lemma with only `cs_prov` + per-source nonoverlap
> hypotheses) is **superseded** by the analysis below.  The previous
> pointer was insufficient: it would fail at the cross-prov boundary
> because the cascade history cannot be reconstructed from
> `(state, remaining)` alone.

### The 2^53 gap (Route 1 Session 3 finding)

After this collapse landed, a follow-on precondition test
(`test_invariant_implies_h_prev_bound`, Qed-closed in
`theories-flocq/B64_FastExpansionSum_Shewchuk_Route2.v`) extracted what
the existing invariant actually provides about `h_prev`:

  - **Invariant provides**: `|h_prev| <= ulp(cs_carry state) / 2`
    (when `cs_carry` and `h_prev` are nonzero, from clause (a)'s
    `nonoverlap_shewchuk` chain peeled off via `compress`).
  - **`cascade_h_chain_statement` needs**:
    `|h_prev| <= ulp(snd (b64_TwoSum x (cs_carry state))) / 2`.

Since `snd (b64_TwoSum x q) =: h` lives in `b64_plus x q`'s low binade,
`ulp(h) ≈ ulp(q) * 2^-53` in the generic no-cancellation case.  The
invariant's bound is therefore **roughly 2^53 too loose**.

This is a mathematical gap, not a tactic issue or a missing Flocq
lemma.  Closing it requires a strictly tighter bound on `h_prev`
than `cascade_invariant`'s clause (a) exposes.

### Shewchuk §4's argument — what it actually uses

Re-reading
`docs/shewchuk-theorem-13-proof-structure.md` §4 (lines 193-228) plus
the design artifact's case-analysis (lines 246-277 of
`docs/slice-a-piece-5b-route1-design-session.md`), §4's tightening
decomposes into two regimes:

  - **Same-prov consecutive (within a same-provenance run)**.  When
    `cs_prov = prov_x` and the two elements are adjacent in the
    sorted merge, they must be adjacent in their source.  Then
    `nonoverlap_shewchuk e` (or `f`) gives `|x_curr|/|x_prev| >=
    2^53`, which directly yields the required factor-of-2^53
    tightening.  This part **is a one-time derivation** from the
    input preconditions + sort order; detectable from `cs_prov` +
    next `prov` alone, no history required.

  - **Cross-prov (run boundary)**.  When `cs_prov <> prov_x`,
    sorted-ascending only gives `|x_curr| >= |x_prev|` — a constant
    factor, not 2^53.  §4's argument here is *not* a one-time bound
    from inputs; it is the cumulative claim that
    > "the cascade's accumulator after processing a run of
    > same-provenance elements ends up with magnitude bounded by the
    > last element processed, which combines with the
    > next-provenance element's magnitude via TwoSum's bound."

    That "after processing a run … bounded by the last element
    processed" is **cascade history**: a property maintained
    step-by-step about the current run's structure.  It is not
    derivable from the immediate `(state, remaining)` because the
    bound depends on what previous steps absorbed.

### Why Option A and Option C alone are insufficient

  - **Option A (richer precondition only)** — pass
    `nonoverlap_shewchuk e`, `nonoverlap_shewchuk f`, and the sorted
    merge as hypotheses to `cascade_h_chain` without changing the
    invariant.  Handles the same-prov case (the within-run 2^53 gap
    is in the inputs).  **Fails the cross-prov case** because the
    run-boundary bound on `cs_carry` cannot be reconstructed from
    immediate hypotheses.

  - **Option C (intermediate lemma over inputs)** — prove
    `cascade_bound_from_sorted_merge` as a one-time result about the
    inputs, then use it in `cascade_h_chain`.  Same defect as A:
    no input-only lemma characterises the cascade's mid-run state.

### Option B with run-bound conjunct — the load-bearing recommendation

Augment `cascade_invariant` with a **clause (d)** that tracks the
current same-provenance run's maximum-magnitude element
`cs_run_max`.  Two specific design decisions must be made before any
Coq is written:

  - **Decision 1 — field vs parameter.**  Add `cs_run_max` as a field
    of the `cascade_state` record, OR thread it as a parameter to
    `cascade_invariant`.  The blast-radius criterion (grep for
    `cascade_state | cs_carry | cs_prov | cs_output | mk_cascade`)
    decides: small radius -> field; large radius -> parameter.
  - **Decision 2 — initial value.**  At the cascade's first step,
    `cs_run_max` is the first absorbed element (so `|cs_carry| <=
    2 |cs_run_max|` holds trivially with the first element equal to
    both).

Clause (d), as content:

```coq
Rabs (Binary.B2R prec emax (cs_carry state))
  <= 2 * Rabs (Binary.B2R prec emax (cs_run_max state)).
```

The constant `2` covers the geometric-sum factor within a run
(a half-ulp chain's partial sums are bounded by `2 * largest`).

**Preservation under cascade step splits on continuity:**

  - **Continue run** (new step has `prov = cs_prov state`):
    `cs_run_max` stays the same; the within-source nonoverlap
    closes the 2^53 gap for `h_prev` algebraically; clause (d) is
    maintained.
  - **Start new run** (new step has `prov <> cs_prov state`):
    `cs_run_max` resets to the new `x`; the TwoSum bound on the
    run-boundary step gives `|h_new| <= ulp(x) / 2`; clause (d)'s
    new instance follows from `|cs_carry| <= 2 |x_prev_run_max| <=
    2 |x|` (sorted) plus TwoSum.

The two preservation cases lift the Option C "intermediate lemma"
machinery into Option B's framework:

  - `run_bound_propagates_under_same_prov` (within-run, ~50-80
    lines): the within-run portion derived from per-source
    `nonoverlap_shewchuk` + sort.
  - `run_bound_resets_under_prov_flip` (cross-prov, ~80-120 lines):
    the cumulative cross-prov claim that §4 establishes through
    deep magnitude bookkeeping.

`cascade_h_chain` then composes the two via a case split on
`provenance_eq_dec p (cs_prov state)`, in ~10 lines.

### Mapping to Shewchuk's paper structure

  - Clause (a) of `cascade_invariant` = Shewchuk §2.1's
    "running output is non-overlapping" (the chain itself).
  - Clause (d) of `cascade_invariant` = Shewchuk §4's run-bound
    bookkeeping (the deeper magnitude argument).
  - `run_bound_propagates_under_same_prov` = the within-run
    portion of §4.
  - `run_bound_resets_under_prov_flip` = the cross-prov portion of §4.

This matches the paper's own decomposition, with the run-boundary as
the locus of the non-trivial reasoning.

### Cost estimate

| Deliverable                                  | Lines       |
|----------------------------------------------|-------------|
| Clause (d) definition + `cs_run_max` tracking| ~30         |
| `cascade_invariant_empty` re-proof           | ~10         |
| `run_bound_propagates_under_same_prov`       | ~50-80      |
| `run_bound_resets_under_prov_flip`           | ~80-120     |
| `cascade_h_chain` composition                | ~50         |
| **Total**                                    | **~220-300**|

One focused session if the run-bound formulation is right.  Two if
the cross-prov lemma surfaces a sub-obligation (the design doc
warns about the round-to-even boundary as a possible sub-tangent).

The successor prompt landing this plan is
`docs/slice-a-piece-5b-route1-session-4-prompt.md`.

## What this session leaves committed

  - `theories-flocq/B64_FastExpansionSum_Shewchuk_Route2.v`:
      - Refined `cascade_invariant_handover` (5-arm disjunction).
      - `cascade_invariant_empty` re-proved as a Qed-closed lemma
        taking the handover as a hypothesis.
      - `cascade_step_preserves_invariant` stated and partially
        attempted; the body ends with `Abort.` after `rewrite
        rev_app_distr` exposed the h-chain sub-obligation.  The
        in-file comment block above the `Abort.` documents the
        collapse with pointers to this artifact.
  - `docs/slice-a-piece-5b-route1-session-2-collapse.md` (this file).
  - `docs/development-environment.md` — already in tree, unchanged;
    cited above as the host-install path.

No new `Admitted` markers, no axioms introduced, registry unchanged at
4 entries (3 counterexample + 1 deferred-proof).  The corpus invariants
hold.

## CI gauntlet (this session)

```
$ bash scripts/check_admitted.sh
All Admitted theorems registered (4 total: 3 counterexample, 1 deferred-proof).

$ bash scripts/audit_axioms.sh /tmp/build.log
[axioms-audit] OK: all per-theorem PA blocks satisfy the allowlist (or are exempted).

$ bash scripts/check_readme_axioms.sh
[readme-axioms] OK: README and docs/axiom-allowlist.txt agree.
```

All green.
