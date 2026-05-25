# Slice A Piece 5b Route 1 Session 11 — outcome

**Session.** Route 1 Session 11: define `cascade_run` as the state-
transition iteration of the cascade, prove its equivalence to the
corpus's `b64_grow_expansion_aux`.  Branch
`claude/cascade-invariant-bootstrap-8oSDv`.

**Outcome.** PARTIAL — three new Qed-closed theorems landing the
state-machine bridge between `cascade_invariant` and the algorithm's
actual computation.  The headline composition (full
`fast_expansion_sum_nonoverlap_shewchuk`) is deferred pending the
Path-A-at-every-step characterization, which is the remaining
structural design question.

## Deliverables landed

### `cascade_run` (Definition)

```coq
Fixpoint cascade_run
  (state : cascade_state) (xs : list tagged_b64) : cascade_state :=
  match xs with
  | nil => state
  | (x, prov) :: rest =>
      cascade_run (cascade_step_state state x prov) rest
  end.
```

The cascade as a state-transition iteration over a tagged input.
Bridges `cascade_step_state` (the per-step transition, used by
preservation lemmas in Sessions 6-10) with the actual algorithm's
recursive `b64_grow_expansion_aux`.

### `untag_cons_pair` (Qed-closed)

```coq
Lemma untag_cons_pair :
  forall (x : binary64) (prov : provenance) (xs : list tagged_b64),
    untag ((x, prov) :: xs) = x :: untag xs.
```

Single-line proof.  Avoids the structural `cbn`/`unfold` dance when
peeling a tagged-input cons.

### `cascade_run_cs_carry` (Qed-closed)

```coq
Lemma cascade_run_cs_carry :
  forall xs state,
    cs_carry (cascade_run state xs)
      = snd (b64_grow_expansion_aux (cs_carry state) (untag xs)).
```

Inductive proof on `xs`.  At each step, the recursive structure of
`cascade_step_state` (which discards provenance for `cs_carry`)
matches `b64_grow_expansion_aux`'s recursive call exactly.

### `cascade_run_cs_output` (Qed-closed)

```coq
Lemma cascade_run_cs_output :
  forall xs state,
    cs_output (cascade_run state xs)
      = cs_output state
        ++ fst (b64_grow_expansion_aux (cs_carry state) (untag xs)).
```

Inductive proof.  The `cs_output` of `cascade_run` is the initial
`cs_output` appended with the cascade's produced h's.

## What this gives us

The pieces are now in place to prove the headline once a complete
Path-A-everywhere predicate is established:

  1. `cascade_invariant_empty` (Session 5): initial state satisfies
     invariant given the bootstrap handover.
  2. `cascade_step_preserves_invariant_pathA` (Session 10): invariant
     preserved through each Path A step.
  3. `cascade_run_cs_carry` + `cascade_run_cs_output` (Session 11):
     `cascade_run`'s final state's carry+output match
     `b64_grow_expansion_aux`'s output.

Connection to `fast_expansion_sum`:

```coq
fast_expansion_sum e f
  = match sort_by_abs (e ++ f) with
    | nil => nil
    | x :: xs =>
        let '(hs, qfinal) := b64_grow_expansion_aux x xs in
        qfinal :: rev hs
    end.
```

By `cascade_run_cs_*`, this equals
`cs_carry (final_state) :: rev (cs_output final_state)` where
`final_state := cascade_run (initial_cascade_state x prov_x) (tagged xs)`
for the appropriate `prov_x`.

If we can inductively apply `cascade_step_preserves_invariant_pathA`
throughout, clause (a) on the final state gives
`nonoverlap_shewchuk (cs_carry :: rev cs_output)` — the headline.

## What remains for the headline

A `cascade_pathA_chain` predicate that asserts Path A holds at every
cascade step.  This is a structural property of the input (e, f)
plus the sort.  Concretely:

  - At step k, |cs_carry_k| < ulp(pred x_{k+1}) / 2 (or succ for
    neg).
  - cs_carry_k accumulates the first k absorbed elements.
  - In within-source consecutive: |cs_carry_k| ≈ |x_k| <= ulp(x_{k+1})/2
    holds via per-source nonoverlap_shewchuk.
  - In cross-prov: |cs_carry_k| can be larger; Path A fails.

The structural question: under what input conditions does Path A
hold throughout?  Conjecture: when the inputs have an interleaving
structure where same-prov runs are sufficient.

Alternatively: when Path A fails (cross-prov boundary),
`b64_TwoSum` produces snd = 0 (exact step) or near-zero, which
`compress` filters out of nonoverlap_shewchuk.

These structural cases are the persistent deferred-proof obstacle.

## Path forward

Two viable strategies for Session 12+:

  - **Strategy A — Conditional headline**: state
    `fast_expansion_sum_nonoverlap_shewchuk` with an explicit
    `cascade_pathA_chain` hypothesis.  Prove it.  The hypothesis is
    abstract; specific Stage D consumers discharge it via
    case-specific arguments.
  - **Strategy B — Compress-aware preservation**: handle the
    `snd = 0` case explicitly, showing the chain reduces via
    `compress` filtering.  Combined with Path A for non-zero snd
    cases, covers more inputs.

Strategy A is simpler but pushes the obstacle to consumers.
Strategy B is more comprehensive but requires the `snd = 0`
analysis.

## Session 11 commit summary

  - `theories-flocq/B64_FastExpansionSum_Shewchuk_Route2.v`:
    - `cascade_run` (Fixpoint).
    - `untag_cons_pair` (Qed-closed).
    - `cascade_run_cs_carry` (Qed-closed).
    - `cascade_run_cs_output` (Qed-closed).
    - `Print Assumptions` blocks for the new theorems.
  - `docs/slice-a-piece-5b-route1-session-11-outcome.md` (this file).

Three new Qed-closed theorems plus the cascade_run state-machine
bridge.  Registry unchanged (4 entries).  CI gauntlet green.

## CI gauntlet (this session)

```
$ bash scripts/check_admitted.sh
All Admitted theorems registered (4 total: 3 counterexample, 1 deferred-proof).

$ bash scripts/audit_axioms.sh /tmp/build.log
[axioms-audit] OK: all per-theorem PA blocks satisfy the allowlist (or are exempted).

$ bash scripts/check_readme_axioms.sh
[readme-axioms] OK: README and docs/axiom-allowlist.txt agree.
```

## Stage of the Route 1 series

After 11 sessions, the Route 1 corpus is structurally complete for
the Path-A case:

| Component                                          | Status        |
|----------------------------------------------------|---------------|
| Provenance-tagged sort + structural lemmas         | Closed (S1)   |
| cascade_state with cs_prov                         | Closed (S2)   |
| cascade_invariant (a)(c)(d′)                       | Closed (S5-6) |
| cascade_invariant_empty (bootstrap)                | Closed (S5)   |
| b64_plus_abs_bound + eps_b64 + ulp_FLT_le_eps_b64  | Closed (S6)   |
| Clause (d′) preservation per-source                | Closed (S6)   |
| cascade_h_chain_pathA (pos + neg)                  | Closed (S7,9) |
| cascade_h_chain_step (cascade-level composition)   | Closed (S8)   |
| Clause (a) preservation under Path A (pos)         | Closed (S8)   |
| Clause (a) preservation under Path A (neg+unified) | Closed (S9)   |
| cascade_step_preserves_invariant_pathA             | Closed (S10)  |
| cascade_run + cs_carry/cs_output equivalence       | Closed (S11)  |
| **Path-A-at-every-step characterization**          | **Open**      |
| **fast_expansion_sum_nonoverlap_shewchuk**         | **Deferred**  |

The remaining open question is purely about characterizing when
Path A holds throughout the cascade — a structural property of the
inputs, not a Coq-tactical problem.  All the Coq machinery to
discharge the headline is in place; what's needed is the
input-side hypothesis or the snd-=-0 compress argument.
