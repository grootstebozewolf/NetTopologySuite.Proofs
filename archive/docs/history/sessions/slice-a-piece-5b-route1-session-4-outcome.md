# Slice A Piece 5b Route 1 Session 4 — outcome

**Session.** Route 1 Session 4 attempt to land Option B (`cascade_invariant`
clause (d) + `cascade_h_chain`).
Branch `claude/cascade-invariant-bootstrap-8oSDv`.

**Outcome.** PARTIAL — Deliverable 1 closed, Deliverable 2 surfaces a
design refinement.  The `cs_run_max` single-field formulation in the
prompt's analysis fails preservation at cross-prov transitions for any
fixed constant.  Per-source tracking (`cs_e_max` + `cs_f_max`) is the
mathematically correct refinement; verified on paper, deferred to
Session 5 for Coq landing.

This is **not the round-to-even boundary sub-tangent** the prompt
warned about.  It is a more fundamental design issue: the
single-`cs_run_max` invariant cannot survive any cross-prov
transition because the triangle bound on `b64_plus` adds an
unsustainable factor at every step.  The fix is structural (the
right invariant shape), not analytical (a Flocq corner case).

## Deliverable 1 — landed

`theories-flocq/B64_FastExpansionSum_Shewchuk_Route2.v` now carries:

  - `cascade_state` extended with `cs_run_max : binary64` field.
  - `cascade_invariant_run_bound`: clause (d) defined as
    `Rabs (B2R (cs_carry state)) <= 2 * Rabs (B2R (cs_run_max state))`.
  - `cascade_invariant` updated to include clause (d) as its fourth
    conjunct.
  - `cascade_invariant_empty` re-proved (Qed-closed) under the
    augmented invariant; clause (d) holds trivially with the
    initial-state choice `cs_run_max := cs_carry`.
  - `test_invariant_implies_h_prev_bound` regression-checked through
    compile under the new invariant shape (still Qed-closed).
  - `cascade_step_preserves_invariant`'s `Abort.` updated to pass
    `x` as the fourth `mk_cascade_state` argument (so the file
    still compiles).

### Decision 1 — field, not parameter

Blast radius for `cascade_state` is **one file only** (no downstream
consumers via grep).  Field is the cleaner choice.

### Decision 2 — initial `cs_run_max := cs_carry`

The initial carry IS the first absorbed element from the sorted
merge, so it IS the current run's max-magnitude element.  Clause
(d) becomes `|q| <= 2|q|`, trivially true.

## Deliverable 2 — cross-prov preservation fails

Probe (in `/tmp/probe_d.v`, run against the host Rocq) captured the
verbatim goal state of the cross-prov clause-(d) preservation
sub-obligation:

```text
  state : cascade_state
  processed : list binary64
  x : binary64
  prov : provenance
  rest : list tagged_b64
  Hcross : prov <> cs_prov state
  Hsort : Rabs (Binary.B2R prec emax (cs_run_max state)) <=
          Rabs (Binary.B2R prec emax x)
  Hd : Rabs (Binary.B2R prec emax (cs_carry state)) <=
       2 * Rabs (Binary.B2R prec emax (cs_run_max state))
  ============================
  Rabs (Binary.B2R prec emax (fst (b64_TwoSum x (cs_carry state)))) <=
  2 * Rabs (Binary.B2R prec emax x)
```

The hypotheses give `|cs_carry| <= 2|cs_run_max| <= 2|x|`.  The
triangle bound on `b64_plus` (modulo rounding):

```
|fst (b64_TwoSum x (cs_carry state))| = |b64_plus x (cs_carry state)|
                                      <= |B2R x + B2R (cs_carry state)| + ulp/2
                                      <= |x| + |cs_carry| + ulp/2
                                      <= |x| + 2|x| + ulp/2
                                      = 3|x| + ulp/2.
```

Bound target: `2|x|`.  **Fails by a factor of approximately 3/2.**

### Why no fixed constant rescues `cs_run_max`

The triangle bound on `b64_plus` adds `|x|` per step.  With
`|cs_carry| <= C|cs_run_max| <= C|x|`, the post-step bound is
`(1+C)|x|`.  The post-step target with `cs_run_max := x` is `C|x|`.
Preservation requires `1+C <= C`, which has no solution for finite
`C`.

The within-run case escapes this trap because within-source
nonoverlap_shewchuk gives `|OLD cs_run_max| <= ulp(|x|)/2 ≈ |x| *
2^-53`, so `|OLD cs_carry| <= |x| * 2^-52` and `|qnew| <= |x| +
|x| * 2^-52 ≈ |x|`.  This sits comfortably under `2|x|`.

Cross-prov has no within-source structure between `cs_run_max_OLD`
(from previous source) and `x` (from new source); sort only gives
`|cs_run_max_OLD| <= |x|` — a constant factor, not 2^53.  The
triangle bound then dominates.

## Refined clause (d′) — per-source maxes

The correct formulation tracks per-source maxes separately:

```coq
Record cascade_state : Type := mk_cascade_state {
  cs_carry  : binary64;
  cs_prov   : provenance;
  cs_output : list binary64;
  cs_e_max  : binary64;  (* largest e absorbed so far; b64_zero initial *)
  cs_f_max  : binary64   (* largest f absorbed so far; b64_zero initial *)
}.

Definition cascade_invariant_run_bound (state : cascade_state) : Prop :=
  Rabs (Binary.B2R prec emax (cs_carry state)) <=
    2 * Rabs (Binary.B2R prec emax (cs_e_max state)) +
    2 * Rabs (Binary.B2R prec emax (cs_f_max state)).
```

### Preservation under continue-run absorbing x (same prov as cs_prov state)

WLOG x is from e (the from_f case is symmetric).  Cascade step
update: `new cs_e_max := x`; `new cs_f_max := OLD cs_f_max`.

  - Hypothesis (from per-source nonoverlap on e):
    `|OLD cs_e_max| <= ulp(|x|)/2`.
  - `|qnew| <= |x| + |OLD cs_carry|`
            `<= |x| + 2|OLD cs_e_max| + 2|OLD cs_f_max|`
            `<= |x| + ulp(|x|) + 2|OLD cs_f_max|`.
  - New bound: `2|x| + 2|OLD cs_f_max|`.
  - `|x| + ulp(|x|) <= 2|x|` (since `ulp(|x|) <= |x|` for normal
    binary64).  ✓

### Preservation under cross-prov absorbing x (prov ≠ cs_prov state)

WLOG x is from f.  Cascade step update: `new cs_f_max := x`;
`new cs_e_max := OLD cs_e_max`.

  - Hypothesis (from per-source nonoverlap on f, since the previous
    cs_f_max was an earlier f element and x is the next f element):
    `|OLD cs_f_max| <= ulp(|x|)/2`.
  - `|qnew| <= |x| + |OLD cs_carry|`
            `<= |x| + 2|OLD cs_e_max| + 2|OLD cs_f_max|`
            `<= |x| + 2|OLD cs_e_max| + ulp(|x|)`.
  - New bound: `2|OLD cs_e_max| + 2|x|`.
  - `|x| + ulp(|x|) <= 2|x|`.  ✓

### Initial state

`cs_carry := first absorbed x_0`.  WLOG prov_x_0 = from_e:
`cs_e_max := x_0`, `cs_f_max := b64_zero`.

Clause (d′): `|x_0| <= 2|x_0| + 0 = 2|x_0|`.  Holds.  ✓

### Why per-source tracking works where single `cs_run_max` fails

The geometric-sum bound `sum <= 2 * max` holds within a half-ulp
chain.  Each source individually satisfies `nonoverlap_shewchuk`,
so each source's accumulated contribution to `cs_carry` is bounded
by `2 * max-absorbed-in-that-source`.  The two contributions add,
giving the per-source bound.

Single `cs_run_max` collapses the two contributions into one,
losing the structure: it implicitly assumes the cascade has only
ONE source's worth of absorptions, which is false the moment any
cross-prov transition occurs.

## Recommendation for Session 5

  1. **Pivot to per-source clause (d′)** in
     `B64_FastExpansionSum_Shewchuk_Route2.v`:
     replace `cs_run_max` with `cs_e_max` + `cs_f_max` fields,
     rewrite `cascade_invariant_run_bound`, re-prove
     `cascade_invariant_empty`.  Blast radius is still one file
     and ~7 mk_cascade_state references.
  2. **State and prove the within-run cs_e_max preservation** as a
     standalone lemma — this needs the within-e nonoverlap hypothesis
     to provide `|OLD cs_e_max| <= ulp(|x|)/2`.  Estimated ~80 lines.
  3. **State and prove the cross-prov cs_f_max preservation** —
     symmetric to (2) using nonoverlap_shewchuk f.  ~80 lines.
  4. **Compose into `cascade_step_preserves_invariant`'s clause (d′)
     preservation** via case split on the new step's provenance vs
     `cs_prov state`.  ~30 lines.
  5. **Re-attempt `cascade_h_chain` proper** (the h-chain link
     `|h_prev| <= ulp(h_new)/2`) using the refined clause (d′).

Total estimate: 200-280 lines for Session 5.  The math is verified
above; the work is Coq-formalising it.

## Discipline note

The prompt's stopping condition for "sub-tangent on
`run_bound_resets_under_prov_flip`" was: capture goal state, what
was tried, what the round-to-even boundary requires.  This outcome
captures the goal state and what was tried, but the issue is
structural (wrong invariant shape), not analytical (round-to-even
corner case).  The "what is required" answer is the per-source
refinement above, not a Flocq lemma about boundary rounding.

This is a strictly tighter design finding than the prompt
anticipated.  Per-source tracking was implicit in the §4 analysis
but the user's prompt analysis collapsed it into a single
`cs_run_max`; this session's probe (cross-prov clause-(d)
preservation goal) made the collapse mechanical, ruled out any
fixed constant, and identified the structural fix.

## What this session leaves committed

  - `theories-flocq/B64_FastExpansionSum_Shewchuk_Route2.v`:
      - `cascade_state` augmented with `cs_run_max` field.
      - `cascade_invariant_run_bound` (clause d) defined.
      - `cascade_invariant_empty` re-proved (Qed-closed).
      - Existing `cascade_invariant_handover`, `cascade_h_chain_-
        statement`, `test_invariant_implies_h_prev_bound` carry
        through the signature change with no proof regressions.
      - `cascade_step_preserves_invariant`'s `Abort.` updated to
        pass `x` as the fourth `mk_cascade_state` argument.
  - `docs/slice-a-piece-5b-route1-session-4-outcome.md` (this file).

No new `Admitted` markers.  Registry unchanged (4 entries).  CI
gauntlet green (`check_admitted`, `audit_axioms`,
`check_readme_axioms`).

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
