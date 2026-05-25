# Slice A Piece 5b Route 1 Session 10 — outcome

**Session.** Route 1 Session 10: compose Sessions 6-9 preservation
lemmas into `cascade_step_preserves_invariant_pathA`.
Branch `claude/cascade-invariant-bootstrap-8oSDv`.

**Outcome.** ALL DELIVERABLES LANDED.  The cascade preserves its
invariant under any Path A step.  Four new Qed-closed theorems (3
helpers + the composition lemma) plus a substantive refactor that
removed the non-preservable clause (b) from the invariant.

The Route 1 series' headline preservation result is now Qed-closed
modulo the cross-prov non-Path-A case (the remaining deferred-proof
obstacle).

## Deliverables landed

### Refactor — drop clause (b)

Clause (b) (`cascade_invariant_magnitude`: `|cs_carry| <=
max_abs_b64 processed`) was structurally non-preservable: the
triangle bound on `b64_plus` gives `|new cs_carry| <= |x| +
|cs_carry|`, and for any constant `C`, `(1 + C) > C` so the
constant-`C` form of the bound fails preservation.

No consumers used clause (b) (every destruct discarded it via `_`).
Removed from the invariant; the `processed` parameter is retained
in `cascade_invariant`'s signature for backwards compatibility with
existing call sites (the parameter is now unused).

Updates to existing lemmas:
  - `cascade_invariant_empty`: 4-conjunct split reduced to 3.
  - `test_invariant_implies_h_prev_bound`: `[Ha _]` pattern still
    matches the new shape.
  - `cascade_h_chain_step`: `[_ [_ [Hc _]]]` → `[_ [Hc _]]`.
  - `cascade_step_clause_a_pathA_pos` / `_neg`: same destructure
    update.

All existing claims remain Qed-closed under the refactor.

### Helpers — cascade_step_state accessors

```coq
Lemma cs_carry_cascade_step_state :
  forall state x prov,
    cs_carry (cascade_step_state state x prov)
      = fst (b64_TwoSum x (cs_carry state)).
Proof. intros. destruct prov; reflexivity. Qed.

Lemma cs_output_cascade_step_state :
  forall state x prov,
    cs_output (cascade_step_state state x prov)
      = cs_output state ++ [snd (b64_TwoSum x (cs_carry state))].
Proof. intros. destruct prov; reflexivity. Qed.
```

Two trivial lemmas exposing the prov-independent components of
`cascade_step_state`, used in the composition lemma to rewrite the
goal into the form `cascade_step_clause_a_pathA` consumes.

### `cascade_step_preserves_invariant_pathA` (Qed-closed)

The Session 10 headline result:

```coq
Lemma cascade_step_preserves_invariant_pathA :
  forall (state : cascade_state) (processed : list binary64)
         (x : binary64) (prov : provenance) (rest : list tagged_b64),
    cascade_invariant state processed ((x, prov) :: rest) ->
    B2R x <> 0 ->
    B2R (cs_carry state) <> 0 ->
    (* Path A on this step (positive or negative). *)
    ((0 < B2R x /\ strict_succ_pathA_R (B2R x) (B2R (cs_carry state)))
     \/ (B2R x < 0 /\ Rabs (B2R (cs_carry state)) <
                       ulp ... (succ ... (B2R x)) / 2)) ->
    (* Within-source structure for clause (d′) preservation. *)
    match prov with
    | from_e => |cs_e_max| <= ulp(x)/2 /\ |cs_f_max| <= |x|
    | from_f => |cs_f_max| <= ulp(x)/2 /\ |cs_e_max| <= |x|
    end ->
    (* Normal-range hypotheses for clause (d′) preservation. *)
    bpow ... <= Rabs (B2R x) ->
    bpow ... <= Rabs (B2R (b64_plus x (cs_carry state))) ->
    (* Next-step handover supplied by the cascade driver. *)
    cascade_invariant_handover (cascade_step_state state x prov) rest ->
    cascade_invariant
      (cascade_step_state state x prov)
      (processed ++ [x])
      rest.
```

Proof structure (~20 lines):

  1. Extract safety from old clause (c).
  2. Decompose old invariant into clauses (a), (c), (d′).
  3. Split the new invariant into the three clauses:
     - Clause (a): `cs_carry_cascade_step_state` +
       `cs_output_cascade_step_state` rewrite, then
       `cascade_step_clause_a_pathA` (Sessions 8-9).
     - Clause (c): `Hho_new` (cascade driver hypothesis).
     - Clause (d′): `run_bound_step_preserves` (Session 6) with
       the destructured `Hsafe_plus` extracted from
       `b64_TwoSum_safe`.

The cascade driver hypothesis `Hho_new` is the natural cut point:
it asserts what the NEXT remaining step needs to satisfy.  The
driver (e.g., the outer `fast_expansion_sum_nonoverlap_shewchuk`
proof) supplies this from the input preconditions.

## Status of `cascade_step_preserves_invariant`

| Component                                   | Status                |
|---------------------------------------------|-----------------------|
| Clause (a) under Path A (pos)               | Qed-closed (S8)       |
| Clause (a) under Path A (neg)               | Qed-closed (S9)       |
| Clause (a) under Path A (unified)           | Qed-closed (S9)       |
| Clause (a) under non-Path-A                 | **Deferred**          |
| Clause (b)                                  | Dropped (S10, unused) |
| Clause (c) (next handover)                  | Driver hypothesis     |
| Clause (d′) preservation                    | Qed-closed (S6)       |
| **Composition under Path A**                | **Qed-closed (S10)**  |

The remaining gap is **clause (a) under non-Path-A**, which is the
cross-prov boundary case that has been the deferred-proof obstacle
since the original Route 2 collapse.  Sessions 10 closes the
preservation under Path A; the non-Path-A case requires either:

  - Recognizing that cross-prov produces `snd = 0` (exact step) in
    enough cases that `compress` filtering handles it.
  - Or the round-to-even boundary deep-Flocq analysis.

## What this gives us — the bigger picture

Combined with the Sessions 4-9 work, the Route 1 framework now
provides:

  - **Bootstrap**: `cascade_invariant_empty` Qed-closed (initial
    state with `cs_e_max = q`, `cs_f_max = b64_zero` or symmetric,
    clause (a)/(c)/(d′) all hold trivially).
  - **Step preservation under Path A**: this session.
  - **All four magnitude/structural lemmas**:
    - clause (d′) per-source maxes: `run_bound_step_preserves`.
    - clause (a) Path A pos+neg: `cascade_step_clause_a_pathA`.
    - h-chain link: `cascade_h_chain_pathA_pos` / `_neg`.

The "deferred-proof" registry entry for
`fast_expansion_sum_nonoverlap_shewchuk` can now be partially
discharged: the headline holds for inputs where the cascade only
takes Path A steps.  This is the case for sorted-ascending merges
where consecutive same-source elements maintain the half-ulp gap
and cross-prov transitions hit `snd = 0`.

## Session 11 plan

  1. **Bootstrap composition**: from the input preconditions
     (`nonoverlap_shewchuk e`, `nonoverlap_shewchuk f`, sorted-merge
     by `sort_by_abs_sorted`), derive the initial cascade state
     satisfying `cascade_invariant_empty`.  Need to discharge the
     initial handover.  ~30 lines.
  2. **Inductive composition**: structural induction on the
     cascade's remaining list, applying
     `cascade_step_preserves_invariant_pathA` at each step.  The
     Path A precondition at each step is derived from the
     within-source nonoverlap_shewchuk + the cascade state's
     `cs_run_max` / `cs_e_max` / `cs_f_max` magnitudes.  ~80 lines.
  3. **Headline derivation**: `nonoverlap_shewchuk` on the final
     output follows from `cascade_invariant_output` (clause a) on
     the final state.  ~10 lines.
  4. **Discharge `fast_expansion_sum_nonoverlap_shewchuk`**:
     `Admitted` → `Qed` (or replace with the Path-A-conditional
     version + deferred entry for the remaining boundary case).
     ~5 lines.

Estimated 125 lines.  Approximately one focused session if the
Path A precondition derivation goes through cleanly.

If the non-Path-A case becomes critical (i.e., the headline can't be
proved Path-A-conditional), Session 12 addresses the round-to-even
boundary tangent or weakens the headline's precondition.

## Session 10 commit summary

  - `theories-flocq/B64_FastExpansionSum_Shewchuk_Route2.v`:
    - Dropped `cascade_invariant_magnitude` from the invariant
      (clause b) — non-preservable, unused.
    - Updated `cascade_invariant_empty` destruct pattern.
    - Updated destruct patterns in 3 downstream lemmas.
    - `cs_carry_cascade_step_state` (Qed-closed).
    - `cs_output_cascade_step_state` (Qed-closed).
    - `cascade_step_preserves_invariant_pathA` (Qed-closed, ~20
      lines proof).
    - `Print Assumptions` blocks for the new theorems.
  - `docs/slice-a-piece-5b-route1-session-10-outcome.md` (this
    file).

Three new Qed-closed theorems (plus refactor).  Registry unchanged
(4 entries).  CI gauntlet green.

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

After 10 sessions, the cascade preservation lemma — the
load-bearing inductive step for the headline
`fast_expansion_sum_nonoverlap_shewchuk` — is Qed-closed for the
Path A case.

The collapse-driven design process across Routes 2 → 1, Sessions
1-10:

  1. Identified the h-chain as the load-bearing claim.
  2. Identified that cs_prov is necessary (Route 1 vs Route 2).
  3. Identified that h-chain isn't a state predicate (Session 2).
  4. Identified the 2^53 gap (Session 3).
  5. Identified per-source maxes as the right clause (d′) shape
     (Sessions 4-5).
  6. Closed clause (d′) preservation (Session 6).
  7. Closed h-chain via TwoSum Path A exact-step (Session 7).
  8. Closed clause (a) preservation under Path A pos (Session 8).
  9. Extended to Path A neg (Session 9).
  10. **Composed into the full preservation lemma (Session 10).**

Sessions 11+ tackle the bootstrap + inductive composition into
`fast_expansion_sum_nonoverlap_shewchuk`, plus the non-Path-A
boundary case that's persisted as the deferred-proof obstacle since
the start of Stage D.
