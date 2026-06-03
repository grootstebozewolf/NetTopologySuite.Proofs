# Slice A Piece 5b Route 1 Session 6 — outcome

**Session.** Route 1 Session 6: land clause (d′) preservation lemmas.
Branch `claude/cascade-invariant-bootstrap-8oSDv`.

**Outcome.** ALL DELIVERABLES LANDED.  Three new Qed-closed lemmas
plus a compositional case-split lemma close the clause (d′)
preservation problem entirely.  The four-case decomposition the
Session 5 outcome predicted collapsed to two cases via a structural
observation (same-source consecutive holds regardless of cross-prov
status because of how `sort_by_abs` interleaves merged sources).

The original 350-400 line estimate was generous: actual code added
~150 lines for the four new Qed-closed results.

## Deliverables landed

### Step 1 — `eps_b64` definition + bound lemmas

```coq
Definition eps_b64 : R := / IZR (Z.pow_pos 2 52).

Lemma eps_b64_pos : 0 < eps_b64.
Lemma eps_b64_le_quarter : eps_b64 <= /4.
Lemma eps_b64_eq_bpow : eps_b64 = bpow radix2 (1 - prec).
```

`eps_b64_eq_bpow` closes by `reflexivity` — `bpow radix2 (1 - prec)`
evaluates to exactly `/IZR (Z.pow_pos 2 52)` for `prec = 53`.  The
positivity and tight-bound lemmas are 2-line each via `IZR_lt` /
`IZR_le` + `Rinv` properties.

### Step 2 — `ulp_FLT_le_eps_b64` corollary

```coq
Lemma ulp_FLT_le_eps_b64 :
  forall x : R,
    bpow radix2 (b64_emin + prec - 1) <= Rabs x ->
    b64_ulp x <= Rabs x * eps_b64.
```

Two-line proof: rewrite by `eps_b64_eq_bpow`, apply
`ulp_FLT_le radix2 b64_emin prec`.

This is the normal-range tight ulp bound that the Session 5 outcome
identified as the missing ingredient.  `b64_ulp_le_abs` alone (which
gives only `ulp(x) <= |x|`) was insufficient; the relative form
`ulp(x) <= |x| * 2^-52` is what makes `nra` close the preservation
chain.

### Step 3 — `b64_plus_abs_bound_with_normal` corollary

```coq
Lemma b64_plus_abs_bound_with_normal :
  forall x y : binary64,
    b64_safe Rplus x y ->
    bpow radix2 (b64_emin + prec - 1) <=
      Rabs (Binary.B2R prec emax (b64_plus x y)) ->
    Rabs (Binary.B2R prec emax (b64_plus x y))
      * (1 - eps_b64 / 2)
      <= Rabs (Binary.B2R prec emax x) + Rabs (Binary.B2R prec emax y).
```

This is the Session 5 outcome's identified "clean form" for feeding
`nra`.  Combines `b64_plus_abs_bound` (Qed-closed in Session 5) with
`ulp_FLT_le_eps_b64` to convert the absolute ulp slack into a
multiplicative `eps_b64` factor, then rearranges to put the result on
one side with a `(1 - eps/2)` coefficient.

The `nra` closes through this form cleanly.

### Step 4 — preservation lemmas (the structural insight)

The Session 5 outcome predicted four preservation cases (within-run
× cross-prov, times from_e × from_f).  Session 6 found these
**collapse to two**:

```coq
Lemma run_bound_absorb_e :
  forall (state : cascade_state) (x : binary64),
    cascade_invariant_run_bound state ->
    Rabs (B2R (cs_e_max state)) <= b64_ulp (B2R x) / 2 ->     (* within-e *)
    b64_safe Rplus x (cs_carry state) ->
    bpow radix2 (b64_emin + prec - 1) <= Rabs (B2R x) ->      (* x normal *)
    bpow radix2 (b64_emin + prec - 1) <=
      Rabs (B2R (b64_plus x (cs_carry state))) ->            (* result normal *)
    Rabs (B2R (cs_f_max state)) <= Rabs (B2R x) ->            (* sorted *)
    cascade_invariant_run_bound (cascade_step_state state x from_e).

Lemma run_bound_absorb_f :  (* symmetric, swap e and f *)
```

**The structural observation**: the within-source hypothesis
`|cs_X_max| <= ulp(x)/2` holds whenever the new `x` is from source
`X`, **regardless of what `cs_prov state` was before** the step.

Reason: in `sort_by_abs_sorted` ascending merge, same-source
elements appear in the same relative order as in their native
source list (since sort is by absolute value).  The within-source
half-ulp chain therefore holds between `OLD cs_X_max` (= largest X
absorbed so far) and the new `x` (= next X to absorb) whether or
not the previous absorption was X or the other source.

This collapses "continue-run X" and "cross-prov to X" to the same
lemma.

The proof structure (within both `absorb_e` and `absorb_f`):

  1. Apply `b64_plus_abs_bound_with_normal` to bound the result
     against operand magnitudes plus a `(1 - eps/2)` factor.
  2. Apply `ulp_FLT_le_eps_b64` on x to convert `ulp(x)` to
     `|x| * eps_b64`.
  3. Combine with clause (d′) on the old state to bound the carry.
  4. Stage a chain of `lra`/`nra` assertions:
       - `Q <= UX + 2*F`  (from clause d + within-source gap)
       - `Q <= X*eps + 2*F`  (from ulp_FLT_le_eps_b64 on x)
       - `A * (1 - eps/2) <= X + X*eps + 2*F`  (from
         `b64_plus_abs_bound_with_normal`)
       - `X*(1 - 2*eps) >= F*eps`  (from sorted + `eps <= 1/4`)
       - `(2*X + 2*F)*(1 - eps/2) >= X + X*eps + 2*F`  (the goal's
         expansion against the chain)
       - `A * (1 - eps/2) <= (2*X + 2*F) * (1 - eps/2)`  (combining)
  5. Apply `Rmult_le_reg_r` with `Hpos_factor : 0 < 1 - eps/2` to
     cancel the factor.

About ~50 lines per case; the `absorb_f` case is a near-copy of
`absorb_e` with E and F swapped.  Both Qed-closed.

### Step 5 — `run_bound_step_preserves` composition

```coq
Lemma run_bound_step_preserves :
  forall (state : cascade_state) (x : binary64) (prov : provenance),
    cascade_invariant_run_bound state ->
    b64_safe Rplus x (cs_carry state) ->
    bpow radix2 (b64_emin + prec - 1) <= Rabs (B2R x) ->
    bpow radix2 (b64_emin + prec - 1) <=
      Rabs (B2R (b64_plus x (cs_carry state))) ->
    match prov with
    | from_e =>
        Rabs (B2R (cs_e_max state)) <= b64_ulp (B2R x) / 2
        /\ Rabs (B2R (cs_f_max state)) <= Rabs (B2R x)
    | from_f =>
        Rabs (B2R (cs_f_max state)) <= b64_ulp (B2R x) / 2
        /\ Rabs (B2R (cs_e_max state)) <= Rabs (B2R x)
    end ->
    cascade_invariant_run_bound (cascade_step_state state x prov).
```

Four-line proof: `destruct prov; destruct Hprov; apply absorb_X`.

## What this gives us

Clause (d′) preservation is now Qed-closed at the magnitude level:
given the run-bound on the old state, the appropriate within-source
and sorted hypotheses, plus normal-range and safety preconditions,
the new state's run-bound holds.

The hypotheses (within-source gap + sorted-ascending + normal range
+ safety) are exactly the kind of structural facts the cascade's
outer driver (`fast_expansion_sum`'s top-level) can supply.

## What remains

`cascade_step_preserves_invariant` still has `Abort.` because:

  - Clause (a) preservation needs `cascade_h_chain` (the h-chain
    link `|h_prev| <= ulp(h_new)/2`), per the Route 1 Session 2
    collapse and `cascade_h_chain_statement`.
  - Clause (b) preservation (magnitude relative to `max_abs_b64
    processed`) needs reconciliation: it's a different bound than
    clause (d′) and may itself need refinement.
  - Clause (c) preservation (handover for the next step) needs
    threading from the cascade-driver's per-step safety+sign
    hypotheses.

The Session 6 deliverables close the most structurally complex of
these — clause (d′) — leaving the h-chain and the other clause
preservations for subsequent sessions.

## Session 7 plan

`cascade_h_chain` proper.  With clause (d′) now Qed-closed,
`cascade_h_chain_statement`'s conclusion `|h_prev| <= ulp(h_new)/2`
can be attempted using:

  - Run-bound on the old state (clause d′).
  - Within-source nonoverlap on each source.
  - `b64_plus_abs_bound_with_normal` and `b64_plus_abs_bound` for
    relating the new h to the operand magnitudes.

The known risk: the round-to-even boundary may surface at this
step, since `cascade_h_chain` is the actual half-ulp chain claim
(not a magnitude bound like clause d′).  The discipline
"stop-and-document if it surfaces" remains.

## Commit summary

  - `theories-flocq/B64_FastExpansionSum_Shewchuk_Route2.v`:
      - `eps_b64` + `eps_b64_pos` + `eps_b64_le_quarter` +
        `eps_b64_eq_bpow` (all Qed-closed).
      - `ulp_FLT_le_eps_b64` (Qed-closed).
      - `b64_plus_abs_bound_with_normal` (Qed-closed).
      - `run_bound_absorb_e` (Qed-closed).
      - `run_bound_absorb_f` (Qed-closed).
      - `run_bound_step_preserves` (Qed-closed).
      - Updated in-file comment block: Session 5 deferral notice
        replaced with Session 6 outcome.
      - Added `Print Assumptions` blocks for the new lemmas.
  - `docs/slice-a-piece-5b-route1-session-6-outcome.md` (this file).

7 new Qed-closed theorems.  Registry unchanged (4 entries).  CI
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
