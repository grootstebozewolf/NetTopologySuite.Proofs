# Slice A Piece 5b Route 1 Session 5 — outcome

**Session.** Route 1 Session 5: pivot `cascade_state` to per-source
maxes (the Session 4 outcome's refined clause d′), prove the auxiliary
`b64_plus_abs_bound`, and attempt the preservation lemmas for clause
(d′).  Branch `claude/cascade-invariant-bootstrap-8oSDv`.

**Outcome.** PARTIAL — pivot landed cleanly with `b64_plus_abs_bound`
Qed-closed.  The full clause-(d′) preservation proof for the within-run
case is structurally clear and paper-verified, but the Coq formalisation
requires the tight Flocq ulp bound `ulp_FLT_le` combined with a
nonlinear chain through `b64_plus_abs_bound` + `b64_ulp_le_abs` that
`nra` doesn't close in a single shot.  Two additional auxiliaries
(staged inequality chains) are needed to feed `nra`/`lra` the right
hypotheses.

This is the natural Session-5-to-Session-6 boundary: the design is
right, the auxiliary lemma is done, the four preservation cases need
the Flocq machinery worked through carefully (estimated ~150 lines of
intricate but mechanical proof per case).

## Deliverable 1 — landed (pivot to per-source clause d′)

`theories-flocq/B64_FastExpansionSum_Shewchuk_Route2.v`:

  - `cascade_state` record updated.  `cs_run_max` removed; two new
    fields `cs_e_max` and `cs_f_max` added.
  - `b64_zero : binary64 := Binary.B754_zero prec emax false` defined,
    with the auxiliary `B2R_b64_zero` showing `B2R b64_zero = 0`.
  - `cascade_invariant_run_bound` redefined as the per-source bound:

    ```coq
    Rabs (B2R (cs_carry state)) <=
      2 * Rabs (B2R (cs_e_max state))
      + 2 * Rabs (B2R (cs_f_max state)).
    ```

  - `initial_cascade_state q p : cascade_state` helper introduced.  In
    the `from_e` branch, `cs_e_max := q`, `cs_f_max := b64_zero`;
    symmetric for `from_f`.  Clause (d′) on the initial state becomes
    `|q| <= 2|q| + 0`, trivially true.
  - `cascade_invariant_empty` re-proved (Qed-closed) under the new
    `initial_cascade_state` shape.  Both `from_e` and `from_f` branches
    discharge cleanly via `Rabs_R0` + `Rabs_pos` + `lra`.
  - `cascade_step_state state x prov : cascade_state` defined as the
    cascade step's effect, with the active source's max updating to
    `x` and the other source's max staying unchanged.
  - `cascade_step_preserves_invariant` (still `Abort.`-terminated)
    updated to the new state shape; the abort comment notes the
    deferral to Deliverable 2/3 below.
  - All existing claims regression-checked through compile:
    `cascade_invariant_handover`, `cascade_h_chain_statement`,
    `test_invariant_implies_h_prev_bound` all carry through unchanged.

## Auxiliary lemma — `b64_plus_abs_bound` (Qed-closed)

```coq
Lemma b64_plus_abs_bound :
  forall x y : binary64,
    b64_safe Rplus x y ->
    Rabs (B2R (b64_plus x y)) <=
      Rabs (B2R x) + Rabs (B2R y) + b64_ulp (B2R (b64_plus x y)) / 2.
```

The core absolute-error bound on `b64_plus`: the rounded result is
within a half-ulp of the exact sum.  Proof is ~6 lines via
`b64_plus_correct` + `b64_error_le_half_ulp_round` + `Rabs_triang_inv`
+ `Rabs_triang` + `lra`.

This is the workhorse for the four clause-(d′) preservation cases.

## Deliverable 2 — preservation lemmas (deferred to Session 6)

### Paper math

The within-run from_e preservation proof structure (other three cases
symmetric):

```
Given:
  Hd     : |cs_carry| <= 2|cs_e_max| + 2|cs_f_max|     (clause d')
  Hgap   : |cs_e_max| <= ulp(B2R x) / 2                (within-source)
  Hsafe  : b64_safe Rplus x (cs_carry state)
  Hxn    : bpow(b64_emin + prec - 1) <= |x|            (x normal)
  Hpn    : bpow(b64_emin + prec - 1) <= |b64_plus x q| (result normal)
  Hfsort : |cs_f_max| <= |x|                           (sorted)

Show:
  |b64_plus x (cs_carry state)| <= 2|x| + 2|cs_f_max|
```

Chain:

```
A := |b64_plus x q|
By b64_plus_abs_bound:    A <= |x| + |q| + ulp(b64_plus x q)/2
By ulp_FLT_le on result:  ulp(b64_plus x q) <= A * 2^-52
So:                       A <= |x| + |q| + A * 2^-53
                          A * (1 - 2^-53) <= |x| + |q|

By Hd + Hgap:             |q| <= ulp(B2R x) + 2|cs_f_max|
By ulp_FLT_le on x:       ulp(B2R x) <= |x| * 2^-52
So:                       |q| <= |x| * 2^-52 + 2|cs_f_max|

So:                       A * (1 - 2^-53)
                          <= |x| * (1 + 2^-52) + 2|cs_f_max|

Goal:                     A <= 2|x| + 2|cs_f_max|.

Equivalently:             (2|x| + 2|cs_f_max|) * (1 - 2^-53)
                          >= |x| * (1 + 2^-52) + 2|cs_f_max|.

Expanding LHS:            2|x| - |x| * 2^-52 + 2|cs_f_max| - |cs_f_max| * 2^-52
RHS:                      |x| + |x| * 2^-52 + 2|cs_f_max|

Inequality reduces to:    |x| - 2 * |x| * 2^-52 - |cs_f_max| * 2^-52 >= 0
                          |x| * (1 - 2^-51) >= |cs_f_max| * 2^-52.

With Hfsort:              |cs_f_max| <= |x|.  So RHS <= |x| * 2^-52.
                          |x| * (1 - 2^-51) >= |x| * 2^-52
                          iff 1 - 2^-51 >= 2^-52
                          iff 1 >= 2^-51 + 2^-52.  ✓ (trivially)
```

So the bound holds with margin `1 - 2^-51 - 2^-52 = 1 - 3 * 2^-52` ≈ 1.

### Coq formalisation barrier

The Coq proof requires:

  1. `b64_plus_abs_bound` — DONE (Qed-closed).
  2. Application of `ulp_FLT_le radix2 b64_emin prec` to both `x` and
     `b64_plus x q` to convert `ulp` bounds to `2^-52` multiplicative
     factors.
  3. A staged chain of `assert (H1 : ...) by lra; assert (H2 : ...) by
     lra; ...` driving the nonlinear arithmetic through `nra`.

Attempted in `/tmp/preserve_test.v` (this session's scratch space).
The `lra`/`nra` chain stalls at the first multiplicative step (`UA / 2
<= A * eps52 / 2` from `UA <= A * eps52`) — `nra` doesn't immediately
find the witness, likely because of the `eps52` representation as
`/IZR (Z.pow_pos 2 52)` confusing the heuristic.

**The path forward**: introduce a clean `Definition eps_b64 : R := /
IZR (Z.pow_pos 2 52)` with positivity and bound lemmas, then drive the
chain through `pose proof` + explicit rewriting rather than relying on
nra to find the witness through the unfolded `bpow` form.  This is
mechanical work, ~80-150 lines per case.

### Cost estimate update (Session 6)

| Sub-deliverable                                       | Lines       |
|-------------------------------------------------------|-------------|
| `eps_b64` definition + positivity + bound lemmas      | ~15         |
| `b64_plus_abs_bound_with_normal` corollary            | ~30         |
| Within-run from_e preservation                        | ~80-100     |
| Symmetric within-run from_f                           | ~50 (copy)  |
| Cross-prov to e                                       | ~80-100     |
| Symmetric cross-prov to f                             | ~50 (copy)  |
| `cascade_step_preserves_run_bound` composition        | ~40         |
| **Total**                                             | **~350-400**|

The earlier 200-280 line estimate from Session 4 was optimistic; the
realistic estimate is 350-400 lines once the Flocq ulp machinery is
worked through carefully.

### Sub-tangent risk reassessment

The Session 4 prompt warned about a round-to-even boundary sub-tangent
on the cross-prov lemma.  Re-reading the paper math chain above, the
boundary issue does NOT appear in clause (d′) preservation — clause
(d′) is a magnitude bound, not a half-ulp chain, so the round-to-even
boundary (a half-ulp-chain edge case) is structurally outside its
scope.

The boundary issue is relevant only to the h-chain link
(`cascade_h_chain_statement`), which **is not** what clause (d′)
preservation establishes.  cascade_h_chain composes clause (d′) with
the actual h-chain argument; the boundary issue surfaces in the
h-chain composition, not in clause (d′) itself.

## Deliverable 3 — cascade_h_chain (deferred to Session 7)

Once clause (d′) preservation is Qed-closed (Session 6), the
cascade_h_chain proof from clause (d′) + within-source nonoverlap can
attempt the actual h-chain link.  This is where the round-to-even
boundary tangent may legitimately appear; the prompt's discipline
("stop and document if it surfaces") still applies.

## Session 5 commit summary

  - `theories-flocq/B64_FastExpansionSum_Shewchuk_Route2.v`:
      - `cascade_state` pivot to per-source maxes (cs_e_max, cs_f_max).
      - `b64_zero` + `B2R_b64_zero` Qed-closed.
      - `initial_cascade_state` helper.
      - `cascade_invariant_run_bound` redefined (clause d′).
      - `cascade_invariant_empty` re-proved Qed-closed under new shape.
      - `cascade_step_state` defined as the cascade's step effect.
      - `cascade_step_preserves_invariant` Aborted with updated signature.
      - `b64_plus_abs_bound` Qed-closed (auxiliary).
      - In-file comment block documents the Session 6 sub-obligations.
  - `docs/slice-a-piece-5b-route1-session-5-outcome.md` (this file).

Existing claims (`cascade_invariant_handover`, `cascade_h_chain_statement`,
`test_invariant_implies_h_prev_bound`) carry through compile, no
regressions.

Registry unchanged (4 entries).  CI gauntlet green.

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

## Recommendation for Session 6

Land the four clause-(d′) preservation lemmas as Qed-closed theorems.
The auxiliary `eps_b64` is the unlock; with it, the `nra` chain
should drive through cleanly on each case.

Specifically:

1. Add `Definition eps_b64 : R := / IZR (Z.pow_pos 2 52)` at the top
   of the Route2 file, with `eps_b64_pos`, `eps_b64_le_quarter` (or
   tighter) Qed-closed.
2. Prove `ulp_FLT_le_eps_b64` corollary: under normal-range hypothesis,
   `b64_ulp x <= |B2R x| * eps_b64`.  ~5 lines.
3. Prove `b64_plus_abs_bound_with_normal` corollary: under normal-range
   hypotheses on both operands and the result, `|b64_plus x y| <= (|x|
   + |y|) * (1 + eps_b64) / (1 - eps_b64)` or similar.  ~30 lines.
4. State the four preservation cases as Qed-closed lemmas, each ~80-100
   lines.
5. Compose into `cascade_step_preserves_invariant`'s clause (d)
   sub-obligation.  ~40 lines.

Session 7: `cascade_h_chain` from clause (d′) + within-source
nonoverlap.  The round-to-even boundary may surface here.

Session 8: composition into `fast_expansion_sum_nonoverlap_shewchuk`.
Clears the deferred-proof registry entry.

Stage D headline becomes unconditional at the end of Session 8.
