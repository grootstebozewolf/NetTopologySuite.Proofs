# Route 1 Session 4 — `cascade_invariant` clause (d) + `cascade_h_chain`

## Purpose

Self-contained.  Does not require previous conversation context.
Everything needed is in this file and the referenced docs.

Three deliverables in order.  Stop after the first one that doesn't
close cleanly.

## Environment setup — do this first

```sh
rocq --version        # 9.1.1
ocamlfind list | grep flocq   # 4.2.2
# If not installed: docs/development-environment.md

cd /path/to/NetTopologySuite.Proofs
rocq makefile -f _CoqProject.full -o Makefile.gen
make -f Makefile.gen -j$(nproc) 2>&1 | tail -20
```

Confirm clean baseline before writing any code.

## Background — what the previous sessions established

Four collapse artifacts, each narrowing the design space:

1. **Route 2** — `q` untagged, case split impossible.  Fixed by
   Route 1's `cs_prov`.
2. **Route 1 Session 2** — h-chain needs "previous error" which isn't
   stateful.  Fixed by making `cascade_h_chain` a separate step lemma.
3. **Route 1 Session 3** — invariant's bound is 2^53 too loose.  The
   invariant provides `|h_prev| <= ulp(cs_carry) / 2` but the h-chain
   needs `|h_prev| <= ulp(cs_carry) / 2 * 2^-53`.
4. **Route 1 Session 3 analysis** — Shewchuk §4's run-bound structure
   closes the 2^53 gap.  The tighter bound comes from tracking the
   current run's maximum element (`x_run_max`) through the cascade.
   A new clause (d) in `cascade_invariant` carries this.

The §4 decomposition:

  - **Continue-run case** (same `cs_prov`): `x_run_max` stays the
    same.  Within-source nonoverlap of the source gives the 2^53 gap
    for same-prov consecutive steps.  Clause (d) maintained
    algebraically.
  - **Start-new-run case** (different `cs_prov`): `x_run_max` resets
    to the new `x`.  TwoSum bound gives `|h_new| <= ulp(x) / 2`.
    Clause (d)'s new instance follows from `|cs_carry| <=
    2 |x_prev_run_max| <= 2 |x|` (sorted) plus TwoSum.

Cost breakdown from the analysis:

```
clause (d) definition + x_run_max tracking    ~30 lines
cascade_invariant_empty re-proof              ~10 lines
run_bound_propagates_under_same_prov          ~50-80 lines
run_bound_resets_under_prov_flip              ~80-120 lines
cascade_h_chain composition                   ~50 lines
Total                                         ~220-300 lines
```

Known sub-tangent risk: the cross-prov transition lemma
(`run_bound_resets_under_prov_flip`) may surface the round-to-even
boundary as a sub-obligation.  If it does, **stop and document the
goal state — do not attempt to resolve it inline**.

## Repository state at session start

  - Branch: `claude/cascade-invariant-bootstrap-8oSDv` (or successor).
  - Key files:
      - `theories-flocq/B64_FastExpansionSum_Shewchuk_Route2.v` —
        Route 1 framework, `cascade_state` record,
        `cascade_invariant` with clauses (a)(b)(c=5-arm
        disjunction), `cascade_invariant_empty` Qed-closed (with
        handover hypothesis), `cascade_h_chain_statement` defined as
        a `Prop`, `test_invariant_implies_h_prev_bound` Qed-closed.
      - `theories-flocq/B64_FastExpansionSum.v` —
        `b64_TwoSum_step_dominates_xxx` building blocks (`_pos`,
        `_neg`, `_same_sign`, `_q_zero`, `_strict_pos`,
        `_strict_neg`), all Qed-closed.
      - `docs/slice-a-piece-5b-route1-session-2-collapse.md` —
        updated to point at Option B + run-bound plan as successor.
      - `docs/shewchuk-theorem-13-proof-structure.md` — §4
        run-bound analysis.
      - `docs/admitted-deferred-proofs.txt` — 4 entries (3
        counterexample, 1 deferred-proof).
  - Corpus state: 32+ Qed-closed, 4 registered entries, CI gauntlet
    green.

## Red phase — one task before any Coq

**State clause (d) precisely as a Coq Prop before touching any
file.**

Clause (d) tracks `x_run_max` — the largest element (by magnitude) in
the current provenance run through the cascade.  The candidate:

```coq
(* Clause (d): run-bound on the carry relative to current run's max. *)
(* x_run_max is the largest element seen from cs_prov's source list  *)
(* since the last provenance flip.                                   *)
cs_run_max : binary64  (* new field in cascade_state, or separate    *)

(* clause (d) content: *)
Rabs (Binary.B2R prec emax (cs_carry state))
  <= 2 * Rabs (Binary.B2R prec emax (cs_run_max state)).
```

**Two design decisions to make explicitly before writing code:**

### Decision 1 — `x_run_max` as field vs parameter

  - **Field in `cascade_state`**: cleaner invariant, `x_run_max`
    travels with the state automatically.  Costs updating every
    function that constructs or pattern-matches on `cascade_state`
    — similar blast radius to the `cs_prov` addition in PR #8.
  - **Parameter to `cascade_invariant`**: no state change, but
    `cascade_step_preserves_invariant` needs to thread `x_run_max`
    explicitly.  The preservation proof gets an extra hypothesis
    but the algorithm is untouched.

Check the blast radius before deciding:

```sh
grep -rn "cascade_state\|cs_carry\|cs_prov\|cs_output\|mk_cascade" \
  theories-flocq/ --include="*.v" | grep -v "\.vo"
```

If the blast radius is small (few files), add to `cascade_state`.
If large, use as a parameter to `cascade_invariant`.

### Decision 2 — what is `x_run_max` at the initial state?

At cascade start, the first element processed is `x_run_max`.
`cascade_invariant_empty` needs `x_run_max` to satisfy clause (d)
trivially — the initial carry is the first element, so `|cs_carry|
<= 2 |x_run_max|` should hold with `x_run_max = cs_carry` (or the
first element of the sorted input).

**State both decisions in one sentence each before proceeding.**

## Green phase — three deliverables in order

### Deliverable 1: `cascade_invariant` with clause (d) + `cascade_invariant_empty`

Add `x_run_max` to `cascade_state` (or as a parameter, per Decision
1).  Add clause (d) to `cascade_invariant`.  Re-prove
`cascade_invariant_empty`.  Compile and confirm no regressions in
existing Qed-closed theorems.

```coq
(* Augmented cascade_state if Decision 1 = field. *)
Record cascade_state := {
  cs_carry   : binary64;
  cs_prov    : provenance;
  cs_output  : list binary64;
  cs_run_max : binary64        (* new *)
}.

(* cascade_invariant gains clause (d). *)
Definition cascade_invariant
    (state : cascade_state)
    (processed : list binary64)
    (remaining : list tagged_b64) : Prop :=
  cascade_invariant_output (cs_carry state) (cs_output state)      (* clause a *)
  /\ cascade_invariant_magnitude (cs_carry state) processed         (* clause b *)
  /\ cascade_invariant_handover state remaining                     (* clause c *)
  /\ Rabs (Binary.B2R prec emax (cs_carry state)) <=
       2 * Rabs (Binary.B2R prec emax (cs_run_max state)).          (* clause d *)
```

`test_invariant_implies_h_prev_bound` (already Qed-closed) must
continue to compile after the signature change — that's the
regression check.

If existing theorems break from the signature change, **add
deferred-proof registry entries before committing**.  Do not leave
unregistered Admitteds.

### Deliverable 2: `run_bound_propagates_under_same_prov` and `run_bound_resets_under_prov_flip`

Two intermediate lemmas that the `cascade_h_chain` proof composes.

```coq
(* Within-run: same cs_prov, x_run_max unchanged.  This is where the *)
(* 2^53 gap is closed via per-source nonoverlap_shewchuk.            *)
Lemma run_bound_propagates_under_same_prov :
  forall (state : cascade_state)
         (x : binary64) (remaining : list tagged_b64)
         (e f : list binary64),
    cs_prov state = (* prov of x, e.g. from_e *) ... ->
    cascade_invariant state ... ((x, cs_prov state) :: remaining) ->
    nonoverlap_shewchuk e ->
    nonoverlap_shewchuk f ->
    sorted_asc (untag (tagged_input e f)) ->
    (* Conclusion: h_chain bound holds. *)
    Rabs (Binary.B2R prec emax (snd (b64_TwoSum x (cs_carry state)))) <=
      ulp radix2 (SpecFloat.fexp prec emax)
        (Binary.B2R prec emax (fst (b64_TwoSum x (cs_carry state)))) / 2.

(* Cross-prov: different cs_prov, x_run_max resets.  TwoSum bound  *)
(* on the new step plus clause (d) of the OLD state.               *)
Lemma run_bound_resets_under_prov_flip :
  forall (state : cascade_state)
         (x : binary64) (prov_x : provenance) (remaining : list tagged_b64)
         (e f : list binary64),
    prov_x <> cs_prov state ->
    cascade_invariant state ... ((x, prov_x) :: remaining) ->
    nonoverlap_shewchuk e ->
    nonoverlap_shewchuk f ->
    sorted_asc (untag (tagged_input e f)) ->
    Rabs (Binary.B2R prec emax (snd (b64_TwoSum x (cs_carry state)))) <=
      ulp radix2 (SpecFloat.fexp prec emax)
        (Binary.B2R prec emax (fst (b64_TwoSum x (cs_carry state)))) / 2.
```

Adjust statements to match actual type signatures.  The within-run
lemma uses `nonoverlap_shewchuk` on the source list directly — this
is where the 2^53 gap is closed.  The cross-prov lemma uses
`|cs_carry| <= 2 |x_run_max| <= 2 |x|` (from clause (d) plus sorted
order).

Grep before attempting the within-run lemma:

```sh
grep -n "nonoverlap_shewchuk\|nonoverlap_strict\|compress" \
  theories-flocq/B64_FastExpansionSum_Shewchuk_Route2.v | head -20

grep -n "ulp.*2\b\|half_ulp\|error_le_half" \
  theories-flocq/B64_FastExpansionSum.v | head -20
```

**Known sub-tangent risk on `run_bound_resets_under_prov_flip`**: the
round-to-even boundary may surface as a sub-obligation.  If the goal
contains `round_N_le_midp` or `strict_succ_b64` with an obligation
that sign or magnitude analysis can't close, **stop and document the
goal state verbatim**.  Do not attempt to resolve it inline.

### Deliverable 3: `cascade_h_chain`

```coq
Lemma cascade_h_chain :
  forall (state : cascade_state)
         (x : binary64) (prov_x : provenance)
         (remaining : list tagged_b64)
         (e f : list binary64),
    cascade_invariant state ... ((x, prov_x) :: remaining) ->
    nonoverlap_shewchuk e ->
    nonoverlap_shewchuk f ->
    sorted_asc (untag (tagged_input e f)) ->
    Rabs (Binary.B2R prec emax (snd (b64_TwoSum x (cs_carry state)))) <=
      ulp radix2 (SpecFloat.fexp prec emax)
        (Binary.B2R prec emax (fst (b64_TwoSum x (cs_carry state)))) / 2.
Proof.
  intros.
  destruct (provenance_eq_dec prov_x (cs_prov state)).
  - (* Continue run — same prov *)
    eapply run_bound_propagates_under_same_prov; eauto.
  - (* Start new run — prov flip *)
    eapply run_bound_resets_under_prov_flip; eauto.
Qed.
```

If both intermediate lemmas are Qed-closed, `cascade_h_chain` should
be ~10 lines.  If this structure doesn't close, the intermediate
lemmas' statements need adjustment — not `cascade_h_chain` itself.

## Refactor phase

```sh
./scripts/audit_axioms.sh
./scripts/check_admitted.sh
./scripts/check_readme_axioms.sh
make -f Makefile.gen -j1 2>&1 | grep -E "Error|error" | head -20
```

**Expected CI state after this session.**

Between 3 and 5 new Qed-closed theorems (clause d definition, empty
re-proof, two intermediate lemmas, `cascade_h_chain`).  Registry
unchanged at 4 entries if no signature breakage, or 4+N if downstream
lemmas need deferred-proof entries from the `cascade_state` change.

## Commit message structure

```
feat: cascade_invariant clause (d) + cascade_h_chain [Route 1 Session 4]

Closes the 2^53 gap identified in Route 1 Session 3 via run-bound
tracking (x_run_max in cascade_state).

Deliverable 1: clause (d) = |cs_carry| <= 2|cs_run_max|.
  cascade_invariant_empty re-proved: [note if trivial or non-trivial].
  cascade_state change: [field added / parameter approach].

Deliverable 2: two intermediate lemmas.
  run_bound_propagates_under_same_prov: [note key Flocq lemma used].
  run_bound_resets_under_prov_flip: [note or flag sub-tangent if hit].

Deliverable 3: cascade_h_chain by case split on provenance continuity.
  Proof: ~10 lines composing the two intermediate lemmas.

[If sub-tangent hit on run_bound_resets: note goal state, stop,
 Session 5 addresses round-to-even boundary before composition.]

Category C: inherits classic via b64_TwoSum / Flocq binary arithmetic.
Session 5: cascade_step_preserves_invariant using cascade_h_chain.
Session 6: fast_expansion_sum_nonoverlap_shewchuk composition.
```

## Stopping conditions

  - **Success — all three deliverables Qed-closed**: commit, push,
    Session 5 is `cascade_step_preserves_invariant`.

  - **Stop after Deliverable 1 — signature change too large**: the
    blast radius from adding `cs_run_max` to `cascade_state` breaks
    too many downstream theorems.  Switch to the parameter approach
    for `cascade_invariant`, re-attempt Deliverable 1.  If the
    parameter approach also breaks things, document the specific
    breakage and stop.

  - **Stop after Deliverable 2 — sub-tangent on
    `run_bound_resets_under_prov_flip`**: goal state verbatim, what
    was tried, what the round-to-even boundary requires.  Commit
    the two lemmas that did close (Deliverable 1 and
    `run_bound_propagates_under_same_prov` if closed).  The
    sub-tangent becomes Session 5's first task.

  - **Collapse — clause (d) insufficient**: after implementing
    clause (d), the intermediate lemmas surface an obligation that
    clause (d) plus the sorted-input guarantee can't close.
    Produce:

    ```
    SESSION 4 COLLAPSE

    Clause (d) as implemented: [Coq Prop verbatim]
    Deliverable reached before collapse: [1 / 2 partial]
    Goal state at bail point: [verbatim]
    Missing property: [Coq Prop type]
    ```

    Commit the collapse artifact.  The deferred-proof registry
    entry for `fast_expansion_sum_nonoverlap_shewchuk` remains.
    Stop.

## Session 5 scope (out of scope for this session)

`cascade_step_preserves_invariant` using `cascade_h_chain` at each
inductive step, plus the bootstrap.  With `cascade_h_chain` closed
and the provenance case split available, the preservation proof's
structure is the same four-arm split from Route 1 Session 2 — but
now each arm invokes `cascade_h_chain` rather than trying to derive
the h-chain from the invariant directly.

Session 6: `fast_expansion_sum_nonoverlap_shewchuk` composition.
Clears the deferred-proof registry entry.  Stage D headline becomes
unconditional.

## Discipline notes

The run-bound formulation is the load-bearing design decision in
this session.  Decision 1 (field vs parameter) and Decision 2
(initial `x_run_max` value) must be stated before any code is
written.  The forcing function is `cascade_invariant_empty` — if
the initial state doesn't satisfy clause (d), the invariant is
wrong and must be revised before the intermediate lemmas are
attempted.

The within-run lemma (`run_bound_propagates_under_same_prov`) is
where the 2^53 gap is finally closed.  It should use
`nonoverlap_shewchuk` on the source list directly.  If it requires
something beyond `nonoverlap_shewchuk`, that something needs to be
named before the proof attempt.

The cross-prov lemma has a documented sub-tangent risk.  If the
round-to-even boundary appears, stop immediately and document the
goal state.  It's better to stop with two clean intermediate
lemmas and a precise sub-tangent than to push through and produce
a shaky proof.

220-300 lines.  One session if the run-bound formulation is right.
Two if the cross-prov lemma surfaces a sub-obligation.  The design
analysis has been thorough.  The formulation is as well-grounded
as any in this engagement.  Now prove it.
