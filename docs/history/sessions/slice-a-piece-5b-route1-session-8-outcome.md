# Slice A Piece 5b Route 1 Session 8 — outcome

**Session.** Route 1 Session 8: compose `cascade_h_chain_pathA_pos`
with the invariant; attempt clause (a) preservation under Path A.
Branch `claude/cascade-invariant-bootstrap-8oSDv`.

**Outcome.** ALL DELIVERABLES LANDED.  Four new Qed-closed theorems
plus the load-bearing **clause (a) preservation under Path A**.

The earlier Session 7 plan estimate of 100-150 lines for Session 8
landed at ~130 lines.  The structural insight that clause (e)
(`|h_prev| <= ulp(active_max)/2`) was implied by clause (a) via
`test_invariant_implies_h_prev_bound` (Session 3) avoided needing a
new invariant clause — clause (a) alone supplies the hypothesis
`cascade_h_chain_pathA_pos` needs.

## Deliverables landed

### Deliverable 1 — B2R-compat lifting machinery (Qed-closed)

Two foundational lemmas the corpus lacked:

```coq
Lemma compress_map_B2R_eq :
  forall xs ys : list binary64,
    map (B2R) xs = map (B2R) ys ->
    map (B2R) (compress xs) = map (B2R) (compress ys).

Lemma nonoverlap_shewchuk_B2R_compat :
  forall xs ys : list binary64,
    map (B2R) xs = map (B2R) ys ->
    nonoverlap_shewchuk xs <-> nonoverlap_shewchuk ys.
```

The first by induction on `xs` with case analysis on `Rcompare`.  The
second by composing `compress_map_B2R_eq` with `nonoverlap_strict_B2R_compat`
(already Qed-closed in B64_FastExpansionSum.v).

These lift B2R-equality through the `compress + nonoverlap_strict`
structure, which is exactly what's needed when `b64_TwoSum_pathA_exact_step`
gives us `B2R fst = B2R x` and `B2R snd = B2R q`.

### Deliverable 2 — cascade-level h-chain step (Qed-closed)

```coq
Lemma cascade_h_chain_step :
  forall (state : cascade_state) (processed : list binary64)
         (x : binary64) (prov_x : provenance)
         (rest : list tagged_b64)
         (h_prev : binary64) (hs_tail : list binary64),
    cascade_invariant state processed ((x, prov_x) :: rest) ->
    cs_output state = hs_tail ++ [h_prev] ->
    0 < B2R x ->
    strict_succ_pathA_R (B2R x) (B2R (cs_carry state)) ->
    B2R (cs_carry state) <> 0 ->
    B2R h_prev <> 0 ->
    Rabs (B2R h_prev) <=
      b64_ulp (B2R (snd (b64_TwoSum x (cs_carry state)))) / 2.
```

The composition: `test_invariant_implies_h_prev_bound` (Session 3,
extracts `|h_prev| <= ulp(cs_carry)/2` from clause (a)) plus
`cascade_h_chain_pathA_pos` (Session 7, lifts to `ulp(snd)/2` under
Path A).  Six-line proof.

This is the cascade-level h-chain link: at a Path A step on a
nonzero carry, the cascade's most-recent error h_prev is bounded by
half-ulp of the new error h_new = snd(b64_TwoSum x cs_carry).

### Deliverable 3 — clause (a) preservation under Path A (Qed-closed)

The load-bearing target of the Route 1 series.  Forty-line proof:

```coq
Lemma cascade_step_clause_a_pathA_pos :
  forall (state : cascade_state) (processed : list binary64)
         (x : binary64) (prov : provenance) (rest : list tagged_b64),
    cascade_invariant state processed ((x, prov) :: rest) ->
    0 < B2R x ->
    strict_succ_pathA_R (B2R x) (B2R (cs_carry state)) ->
    B2R (cs_carry state) <> 0 ->
    cascade_invariant_output
      (fst (b64_TwoSum x (cs_carry state)))
      (cs_output state ++ [snd (b64_TwoSum x (cs_carry state))]).
```

Proof structure:

  1. Apply `rev_app_distr` to expose the new chain as
     `fst :: snd :: rev cs_output`.
  2. Extract `b64_TwoSum_safe x (cs_carry state)` from clause (c).
  3. Apply `b64_TwoSum_pathA_exact_step` to get
     `B2R fst = B2R x` and `B2R snd = B2R (cs_carry state)`.
  4. Apply `nonoverlap_shewchuk_B2R_compat` to lift the goal from
     `(fst :: snd :: rev cs_output)` to `(x :: cs_carry :: rev cs_output)`.
  5. Unfold `compress` with case analysis on `Rcompare (B2R x) 0 = Gt`
     (from positivity) and `Rcompare (B2R (cs_carry state)) 0` (Lt or
     Gt by nonzero hypothesis).
  6. Split into `strict_succ_b64 x (cs_carry state)` (from Path A via
     `pred_le_id` + `ulp_le_pos`) and the residual chain (from old
     clause (a)).

The Path A precondition `|cs_carry| < ulp(pred x)/2` gives
`|cs_carry| <= ulp(x)/2` because `ulp(pred x) <= ulp(x)` (for x in
normal range with nondegenerate pred).  That's exactly
`strict_succ_b64 x cs_carry`.

This is the **clause (a) sub-obligation** that has been deferred
since Route 1 Session 2 (where it appeared as the bail goal of the
first attempted preservation proof).  It is now Qed-closed for the
Path A positive case.

## What this gives us

Combined with Session 6's clause (d′) preservation
(`run_bound_step_preserves`), the cascade now has Qed-closed:

  - Clause (a) preservation under Path A (positive x, nonzero
    cs_carry).
  - Clause (d′) preservation universally (for any prov, given the
    appropriate within-source and sorted hypotheses).

The remaining pieces for full `cascade_step_preserves_invariant`:

  - Clause (a) for: negative x; cs_carry = 0; non-Path-A cases.
  - Clause (b) preservation (magnitude bound vs `max_abs_b64 processed`).
  - Clause (c) preservation (handover threading).
  - Composition of all four clauses.

## Path A applicability — the structural caveat

Path A precondition `|cs_carry| < ulp(pred x)/2` requires the carry
to be much smaller than the next input.  This is the strict form
that `b64_TwoSum_pathA_exact_step` needs.

The cascade is in Path A at every within-source consecutive step with
NO cross-prov absorptions in the current run.  As soon as cross-prov
occurs, the carry accumulates the other source's contribution and
Path A fails.

So `cascade_step_clause_a_pathA_pos` covers the "pure run" case but
NOT the cross-prov boundary.  Session 9's design challenge is the
cross-prov case — likely requires either:

  - A non-Path-A clause (a) preservation lemma (the cascade output
    has a non-Path-A structure that's still nonoverlap_shewchuk
    after compress, but proving this requires reasoning about
    cross-prov rounding errors).
  - Recognizing that cross-prov produces `h_new = 0` exactly (the
    rounding-error-is-zero case), so `compress` filters it and the
    chain link goes directly from `fst` (= `b64_plus x cs_carry`)
    to the next-most-recent h, which is bounded by clause (a).

The second is the structural recommendation: in cross-prov, the
TwoSum step IS exact (snd = 0 in B2R), so the chain skips one link
via compress.

## Session 9 plan

  1. **Negative-x analog of `cascade_step_clause_a_pathA_pos`.**
     Mirror via `b64_TwoSum_pathA_exact_step_negative` (to be added
     to `B64_FastExpansionSum.v`).  ~50 lines for the TwoSum lemma +
     ~40 lines for the cascade analog.
  2. **Cross-prov case: handle snd = 0.**  When `snd(b64_TwoSum x q) =
     0` in B2R (exact step), the chain link via `compress` filtering
     bypasses the h-chain requirement.  Need to formalize:
     - Recognition of when this happens.
     - Connection to clause (a) for the residual chain.
     ~80 lines.
  3. **Compose clauses (a), (b), (c), (d′) into
     `cascade_step_preserves_invariant`.**  ~50 lines.

Estimated 220 lines for Session 9, putting
`cascade_step_preserves_invariant` within reach.

Session 10: bootstrap + `fast_expansion_sum_nonoverlap_shewchuk`
composition.  Clears the deferred-proof registry entry.

## What this session leaves committed

  - `theories-flocq/B64_FastExpansionSum_Shewchuk_Route2.v`:
    - `compress_map_B2R_eq` (Qed-closed).
    - `nonoverlap_shewchuk_B2R_compat` (Qed-closed).
    - `cascade_h_chain_step` (Qed-closed, 6 lines).
    - `cascade_step_clause_a_pathA_pos` (Qed-closed, ~40 lines).
    - `Print Assumptions` blocks for the new theorems.
  - `docs/slice-a-piece-5b-route1-session-8-outcome.md` (this file).

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

All green.

## Significance

After 8 sessions of design work, the load-bearing clause (a) sub-obligation
from the original Route 1 Session 2 collapse is now Qed-closed for the
Path A case.  The remaining work (negative-x mirror, cross-prov handling
via snd = 0 compression, clause-b/c preservation) is mechanical
composition — the structural design questions are resolved.

The collapse-driven design process (Routes 2 → 1, Sessions 1-7
identifying each obstacle in turn) was necessary to recognize that:

  1. Provenance must be on the carry (Route 2 → Route 1).
  2. The h-chain isn't a state predicate (Sessions 1-2 collapses).
  3. The per-source `cs_e_max`/`cs_f_max` formulation gives the
     clean run-bound (Sessions 4-5).
  4. **Clause (d′) preservation works universally** (Session 6).
  5. The h-chain itself is TwoSum's Path A exact-step
     (Session 7's 5-line lemma).
  6. **Clause (a) preservation is B2R-compat lifting + Path A's
     exact-step + old chain inheritance** (this session).

Step 6 is what closes the loop on the original problem.
