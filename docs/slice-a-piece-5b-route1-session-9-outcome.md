# Slice A Piece 5b Route 1 Session 9 — outcome

**Session.** Route 1 Session 9: extend clause (a) preservation under
Path A to negative-x case; combine into a unified Path A lemma.
Branch `claude/cascade-invariant-bootstrap-8oSDv`.

**Outcome.** PARTIAL — negative case landed cleanly.  Four new
Qed-closed theorems.  Remaining Session 9 deliverables (cross-prov
case with snd = 0, clause (b)/(c) preservation, full
`cascade_step_preserves_invariant` composition) deferred to Session
10.

## Deliverables landed

### `b64_TwoSum_pathA_exact_step_negative` (Qed-closed)

Mirrors `b64_TwoSum_pathA_exact_step` from `B64_FastExpansionSum.v` for
negative x.  Uses `round_eq_pathA_negative` + `b64_plus_correct` +
`b64_TwoSum_correct` (all already Qed-closed in the corpus).

```coq
Lemma b64_TwoSum_pathA_exact_step_negative :
  forall e q : binary64,
    B2R e < 0 ->
    Rabs (B2R q) < ulp ... (succ ... (B2R e)) / 2 ->
    b64_TwoSum_safe e q ->
    B2R (fst (b64_TwoSum e q)) = B2R e /\
    B2R (snd (b64_TwoSum e q)) = B2R q.
```

About 20 lines, structurally identical to the positive case.

### `cascade_h_chain_pathA_neg` (Qed-closed)

```coq
Lemma cascade_h_chain_pathA_neg :
  forall (x q h_prev : binary64),
    B2R x < 0 ->
    Rabs (B2R q) < ulp ... (succ ... (B2R x)) / 2 ->
    Rabs (B2R h_prev) <= b64_ulp (B2R q) / 2 ->
    b64_TwoSum_safe x q ->
    Rabs (B2R h_prev) <= b64_ulp (B2R (snd (b64_TwoSum x q))) / 2.
```

Five-line proof via `b64_TwoSum_pathA_exact_step_negative`, mirroring
`cascade_h_chain_pathA_pos` from Session 7.

### `cascade_step_clause_a_pathA_neg` (Qed-closed)

The clause (a) preservation under Path A, negative case:

```coq
Lemma cascade_step_clause_a_pathA_neg :
  forall (state : cascade_state) (processed : list binary64)
         (x : binary64) (prov : provenance) (rest : list tagged_b64),
    cascade_invariant state processed ((x, prov) :: rest) ->
    B2R x < 0 ->
    Rabs (B2R (cs_carry state)) <
      ulp ... (succ ... (B2R x)) / 2 ->
    B2R (cs_carry state) <> 0 ->
    cascade_invariant_output
      (fst (b64_TwoSum x (cs_carry state)))
      (cs_output state ++ [snd (b64_TwoSum x (cs_carry state))]).
```

~80 lines.  Mirrors Session 8's positive case but derives
`ulp(succ x) <= ulp(x)` for x < 0 via the chain:

  1. `succ x = -pred(-x)` (Flocq's `succ_opp` applied with rewriting).
  2. `ulp(succ x) = ulp(-pred(-x)) = ulp(pred(-x))` (via `ulp_opp`).
  3. For -x > 0: `pred(-x) <= -x` (`pred_le_id`) and `0 <= pred(-x)`
     (`pred_ge_0`).  Hence `ulp(pred(-x)) <= ulp(-x)` (`ulp_le_pos`).
  4. `ulp(-x) = ulp(x)` (via `ulp_opp` again).

This is the corpus-standard pattern from
`b64_TwoSum_step_dominates_strict_neg` (Qed-closed in
`B64_FastExpansionSum_Shewchuk.v:435`), reused here for the cascade
clause (a) variant.

### `cascade_step_clause_a_pathA` (Qed-closed)

Unified positive+negative Path A clause (a) preservation:

```coq
Lemma cascade_step_clause_a_pathA :
  forall (state : cascade_state) (processed : list binary64)
         (x : binary64) (prov : provenance) (rest : list tagged_b64),
    cascade_invariant state processed ((x, prov) :: rest) ->
    B2R x <> 0 ->
    B2R (cs_carry state) <> 0 ->
    ((0 < B2R x /\ strict_succ_pathA_R (B2R x) (B2R (cs_carry state)))
     \/
     (B2R x < 0 /\ Rabs (B2R (cs_carry state)) <
                     ulp ... (succ ... (B2R x)) / 2)) ->
    cascade_invariant_output
      (fst (b64_TwoSum x (cs_carry state)))
      (cs_output state ++ [snd (b64_TwoSum x (cs_carry state))]).
```

Three-line proof: destruct the disjunction, apply pos or neg case.

This is the **final form of clause (a) preservation under Path A**:
covers both signs of x, requires nonzero x and cs_carry plus the
appropriate Path A magnitude bound.

## What remains (deferred to Session 10)

### Cross-prov case (snd = 0 handling)

When `cs_prov` ≠ `prov` (cross-prov transition), Path A's hypothesis
typically fails because `|cs_carry|` can be comparable to `|x|`.  In
this case:

  - If `snd(b64_TwoSum x cs_carry) = 0` exactly: `compress` filters
    it out, and the chain link goes directly from `fst` (the new
    carry) to the next-most-recent h_prev.  The chain reduces to
    `nonoverlap_shewchuk (fst :: compress (rev cs_output))`, which
    can be proven from old clause (a) plus a magnitude bound on `fst`.
  - If `snd ≠ 0` and Path A fails: structural complication; may
    require additional invariant clauses or the
    round-to-even-boundary deferred-proof.

The first sub-case is tractable; the second is the long-standing
deferred-proof obstacle.

### Clauses (b), (c) preservation

  - **Clause (b)**: `|cs_carry| <= max_abs_b64 processed`.  Needs the
    triangle bound on b64_plus, similar to Session 6's clause (d′)
    work.  Mechanical.  ~50 lines.
  - **Clause (c)**: handover for the next step.  Requires the cascade
    driver to supply the per-step safety + sign hypotheses for the
    NEXT input.  Threading from input preconditions.  ~30 lines.

### `cascade_step_preserves_invariant` composition

Combines clause (a)/(b)/(c)/(d') preservation lemmas into the master
preservation result.  ~40 lines.

Estimated 200-250 lines for Session 10, with the cross-prov case
being the load-bearing remaining design question.

## Session 9 commit summary

  - `theories-flocq/B64_FastExpansionSum_Shewchuk_Route2.v`:
    - `b64_TwoSum_pathA_exact_step_negative` (Qed-closed).
    - `cascade_h_chain_pathA_neg` (Qed-closed).
    - `cascade_step_clause_a_pathA_neg` (Qed-closed, ~80 lines).
    - `cascade_step_clause_a_pathA` (Qed-closed, unified pos+neg).
    - `Print Assumptions` blocks for the new theorems.
  - `docs/slice-a-piece-5b-route1-session-9-outcome.md` (this file).

Four new Qed-closed theorems.  Registry unchanged (4 entries).  CI
gauntlet green.

## CI gauntlet (this session)

```
$ bash scripts/check_admitted.sh
All Admitted theorems registered (4 total: 3 counterexample, 1 deferred-proof).

$ bash scripts/audit_axioms.sh /tmp/build.log
[axioms-audit] OK: all per-theorem PA blocks satisfy the allowlist (or are exempted).

$ bash scripts/check_readme_axioms.sh
[readme-axioms] OK: README and docs/axiom-allowlist.txt agree.
```

## Significance

Clause (a) preservation now closed for both signs of x under Path A.
Combined with Session 6's universal clause (d′) preservation, the
cascade's invariant maintenance is closed for the Path A scenarios
that cover the typical Stage D usage path (consecutive within-source
absorptions before any cross-prov transition).

Cross-prov is the structural remaining work.  The path forward
involves either:

  - Proving the snd = 0 case directly (likely tractable).
  - Or generalizing clause (a) preservation to non-Path-A cases
    (likely requires the deferred-proof boundary work).

The Route 1 series' design milestones:

  - Sessions 1-3: identify the h-chain as the load-bearing claim.
  - Sessions 4-6: design clause (d') with per-source maxes; close
    preservation.
  - Session 7: cascade_h_chain in 5 lines via Path A exact-step.
  - Session 8: clause (a) preservation under Path A (positive).
  - Session 9: extend to negative; unified lemma.
  - Session 10: cross-prov + clause (b), (c) + composition.
  - Session 11: bootstrap + `fast_expansion_sum_nonoverlap_shewchuk`.
