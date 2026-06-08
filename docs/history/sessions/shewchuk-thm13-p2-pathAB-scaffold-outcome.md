# Shewchuk Theorem 13 — P2 pathAB scaffolding outcome

**Branch.** `feat/p2-pathAB-scaffold`

**Outcome.** LANDED — DEFS compile-clean; O3/O5/O6 Qed; O4 registered deferred.

## Deliverables

### DEFS (`theories-flocq/B64_Shewchuk_Thm13_pathAB.v`)

- `cascade_step_pathB`
- `cascade_invariant_handover_pathA_disj` / `cascade_invariant_handover_AB`
- `cascade_step_pathA_conditions` (Route2 L1519–1545 extract)
- `cascade_invariant_AB`
- `cascade_pathAB_chain`

### O3 — `cascade_step_pathB_preserves_run_bound` (Qed)

COPY `run_bound_step_preserves` (Route2 L769). pathB supplies
`b64_TwoSum_exact_of_format_sum` at use sites; geometric hypotheses match
`cascade_pathAB_chain` (normal-range + within-source + sorted).

### O4 — `cascade_step_preserves_invariant_AB` (Admitted)

COPY tactic documented in-file: pathA → `cascade_step_preserves_invariant_pathA`
(L1360); pathB → O1 ∧ O2 ∧ O3. Registered in `admitted-deferred-proofs.txt`.

### O5 — `cascade_run_preserves_invariant_under_pathAB` (Qed)

COPY `cascade_run_preserves_invariant_under_pathA` (L1552); calls O4.

### O6 — `cascade_run_output_nonoverlap_AB` (Qed)

COPY `cascade_run_output_nonoverlap` (L1584); applies O5.

## Next

- O1 (`cascade_step_pathB_preserves_output`) — §4.A resolution-1-extended
- O2 (`cascade_step_pathB_preserves_handover`)
- Discharge O4 → O7 → O8