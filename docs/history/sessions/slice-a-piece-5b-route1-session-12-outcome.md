# Slice A Piece 5b Route 1 Session 12 — outcome

**Session.** Route 1 Session 12: define `cascade_pathA_chain`, prove
the inductive composition (`cascade_run_preserves_invariant_under_pathA`),
prove the cascade output is `nonoverlap_shewchuk` under Path A
throughout.  Branch `claude/cascade-invariant-bootstrap-8oSDv`.

**Outcome.** ALL DELIVERABLES LANDED.  Two new Qed-closed theorems
(plus the `cascade_pathA_chain` definition).  The cascade output's
nonoverlap is now a Qed-closed consequence of the invariant + the
Path-A-chain hypothesis.

This is the **conditional headline** for `fast_expansion_sum_nonoverlap_shewchuk`:
given Path A holds at every cascade step, the output is non-overlapping.
The headline becomes unconditional once Path-A-everywhere is
discharged from input properties (the remaining open question).

## Deliverables landed

### `cascade_pathA_chain` (Fixpoint)

```coq
Fixpoint cascade_pathA_chain
  (state : cascade_state) (xs : list tagged_b64) : Prop :=
  match xs with
  | nil => True
  | (x, prov) :: rest =>
      B2R x <> 0
      /\ B2R (cs_carry state) <> 0
      /\ (* Path A: positive sign + strict_succ OR negative sign condition *)
         (...)
      /\ (* Within-source structure per prov *)
         (...)
      /\ bpow ... <= |B2R x|        (* x normal range *)
      /\ bpow ... <= |B2R (b64_plus x (cs_carry state))|  (* result normal *)
      /\ cascade_invariant_handover (cascade_step_state state x prov) rest
      /\ cascade_pathA_chain (cascade_step_state state x prov) rest
  end.
```

Bundles all the per-step Path-A hypotheses needed by
`cascade_step_preserves_invariant_pathA` (Session 10) into a single
recursive predicate.  At each step:

  - Path A: sign + strict_succ_pathA_R bound on the carry.
  - Within-source: the active source's max bounded by ulp(x)/2, the
    other source's max bounded by |x|.
  - Normal range on both x and the resulting b64_plus.
  - Handover for the next step (cascade driver's bookkeeping).
  - Recursive chain on the rest after this step.

### `cascade_run_preserves_invariant_under_pathA` (Qed-closed)

```coq
Lemma cascade_run_preserves_invariant_under_pathA :
  forall xs state processed,
    cascade_invariant state processed xs ->
    cascade_pathA_chain state xs ->
    cascade_invariant (cascade_run state xs)
                      (processed ++ untag xs) nil.
```

Inductive proof on `xs`:

  - Base: `xs = nil`.  `cascade_run state nil = state`,
    `processed ++ untag nil = processed`.  Conclusion = Hinv.
  - Step: `xs = (x, prov) :: rest`.  Apply
    `cascade_step_preserves_invariant_pathA` (Session 10) for one
    step; IH for the rest.

The `processed` accumulation uses `app_assoc` to convert `processed
++ (x :: untag rest)` to `(processed ++ [x]) ++ untag rest`.

### `cascade_run_output_nonoverlap` (Qed-closed)

```coq
Lemma cascade_run_output_nonoverlap :
  forall init_state tagged_rest,
    cascade_invariant init_state nil tagged_rest ->
    cascade_pathA_chain init_state tagged_rest ->
    nonoverlap_shewchuk
      (cs_carry (cascade_run init_state tagged_rest)
       :: rev (cs_output (cascade_run init_state tagged_rest))).
```

Four-line proof: apply `cascade_run_preserves_invariant_under_pathA`
to get the invariant on the final state, then clause (a) gives the
output shape's nonoverlap_shewchuk.

This is the **conditional headline** in its cleanest form: the cascade
output is non-overlapping, given Path A throughout.

## What this gives us — the full picture

Combined with the Sessions 1-11 work, the Route 1 corpus now closes
the `fast_expansion_sum_nonoverlap_shewchuk` theorem **modulo the
Path-A-chain discharge**.

For any specific input (e, f), to prove the headline:

  1. Compute the sorted merge `sort_by_abs (e ++ f)`.
  2. Let `x_0` be the head, `tagged_rest` be the tagged tail.
  3. Choose `prov_0` based on whether `x_0` comes from e or f.
  4. Define `init_state := initial_cascade_state x_0 prov_0`.
  5. Discharge the initial handover hypothesis for
     `cascade_invariant_empty`: this is Stage D's per-input bookkeeping.
  6. Discharge `cascade_pathA_chain init_state tagged_rest`: the
     **load-bearing remaining obligation**, structural in nature.
  7. Apply `cascade_run_output_nonoverlap` to get
     `nonoverlap_shewchuk` on the cascade's output (which equals
     `fast_expansion_sum e f` via `cascade_run_cs_carry/output` from
     Session 11).

Steps 1-5 and 7 are mechanical.  Step 6 is where the round-to-even
boundary obstacle persists.

## Cross-prov cases and Path A: a more refined view

`cascade_pathA_chain` is a sufficient condition.  It REQUIRES Path A
at every step.  For real cascade behaviors:

  - **Within-source consecutive (the dominant case)**: Path A holds
    naturally via within-source nonoverlap_shewchuk's 2^53 gap.
  - **Cross-prov (less common)**: Path A typically FAILS.  But
    `b64_TwoSum` may produce `snd = 0` (exact step), in which case
    `compress` filters the chain link and the residual structure is
    still nonoverlap.

`cascade_pathA_chain` doesn't capture the `snd = 0` cross-prov
shortcut.  A more refined predicate would handle this.

For Stage D consumers:
  - **Strict Path A inputs** (rare but cleanly verifiable): chain
    discharges directly.
  - **Cross-prov with `snd = 0`** (likely the typical case): would
    need a `cascade_pathA_or_exact_chain` predicate.

Session 13's open question: define this refined predicate and
re-prove preservation against it.

## Session 12 commit summary

  - `theories-flocq/B64_FastExpansionSum_Shewchuk_Route2.v`:
    - `cascade_pathA_chain` (Fixpoint).
    - `cascade_run_preserves_invariant_under_pathA` (Qed-closed).
    - `cascade_run_output_nonoverlap` (Qed-closed).
    - `Print Assumptions` blocks for the new theorems.
  - `docs/slice-a-piece-5b-route1-session-12-outcome.md` (this file).

Two new Qed-closed theorems plus the `cascade_pathA_chain`
predicate.  Registry unchanged (4 entries).  CI gauntlet green.

## CI gauntlet (this session)

```
$ bash scripts/check_admitted.sh
All Admitted theorems registered (4 total: 3 counterexample, 1 deferred-proof).

$ bash scripts/audit_axioms.sh /tmp/build.log
[axioms-audit] OK: all per-theorem PA blocks satisfy the allowlist (or are exempted).

$ bash scripts/check_readme_axioms.sh
[readme-axioms] OK: README and docs/axiom-allowlist.txt agree.
```

## Status after Session 12

The Route 1 corpus is **structurally complete** modulo the
Path-A-chain discharge:

| Component                                          | Status        |
|----------------------------------------------------|---------------|
| Provenance + sort                                  | Closed (S1)   |
| cascade_state with cs_prov                         | Closed (S2)   |
| cascade_invariant (a)(c)(d′)                       | Closed (S5-6) |
| cascade_invariant_empty (bootstrap)                | Closed (S5)   |
| Run-bound machinery (eps_b64, ulp_FLT_le_eps_b64)  | Closed (S6)   |
| Clause (d′) preservation per-source                | Closed (S6)   |
| cascade_h_chain (pos + neg + composition)          | Closed (S7-9) |
| Clause (a) preservation under Path A               | Closed (S8-9) |
| cascade_step_preserves_invariant_pathA             | Closed (S10)  |
| cascade_run + equivalence with b64_grow_expansion  | Closed (S11)  |
| **cascade_pathA_chain inductive composition**      | **Closed (S12)** |
| **cascade output nonoverlap_shewchuk (cond.)**     | **Closed (S12)** |
| Path-A-everywhere characterization                 | Open          |
| fast_expansion_sum_nonoverlap_shewchuk             | Deferred      |

The remaining open question is purely about characterizing inputs
where Path A holds throughout, or about extending the chain
predicate to handle cross-prov `snd = 0` cases.  All cascade-level
Coq machinery is Qed-closed.

Session 13 path: extend `cascade_pathA_chain` to a
`cascade_pathA_or_exact_chain` that allows `snd = 0` cross-prov
shortcuts, OR connect the predicate to specific input classes that
Stage D needs.
