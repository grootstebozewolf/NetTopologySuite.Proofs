# Slice A Piece 5b Route 1 Session 7 — outcome

**Session.** Route 1 Session 7: prove `cascade_h_chain` proper — the
h-chain link `|h_prev| <= ulp(h_new)/2`.  Branch
`claude/cascade-invariant-bootstrap-8oSDv`.

**Outcome.** CORE H-CHAIN LANDED for the positive Path A case.  The
load-bearing claim `cascade_h_chain_pathA_pos` is Qed-closed:
under Path A's strict precondition `|q| < ulp(pred x)/2` (positive x)
and the within-source bound `|h_prev| <= ulp(q)/2`, the new error
`snd(b64_TwoSum x q)` satisfies the h-chain link.

Proof is **5 lines** via the existing `b64_TwoSum_pathA_exact_step`
(Qed-closed in `B64_FastExpansionSum.v`).  No round-to-even boundary
tangent surfaced.

## The structural insight

The Route 1 Session 2 collapse, Session 3 gap analysis, and Sessions
4-6 design refinements all converged on the same load-bearing claim:

```
|h_prev| <= ulp(snd(b64_TwoSum x (cs_carry state))) / 2.
```

What made it look hard:

  - The cascade_invariant's clause (a) only gives `|h_prev| <=
    ulp(cs_carry)/2` — too loose by ~2^53.
  - The clause (d′) Session 5 designed bounds cs_carry by per-source
    maxes — useful for clause (d′) preservation (Session 6) but not
    directly for the h-chain.
  - The "tight" bound on `|h_prev|` requires knowing what produced
    h_prev — past cascade history.

What made it actually tractable:

  - In Path A (`|q| < ulp(pred x)/2`, with x = next absorbed and q
    = current carry), `b64_TwoSum_pathA_exact_step` proves:
    ```
    B2R(snd(b64_TwoSum x q)) = B2R q
    ```
    — the new "error" h_new is **exactly q**, the carry that was
    absorbed.
  - This means `ulp(snd) = ulp(q)`.  Any bound `|h_prev| <= ulp(q)/2`
    lifts directly to `|h_prev| <= ulp(snd)/2`.
  - The within-source nonoverlap on the previous cascade step (one
    step earlier) provides exactly that bound, by another instance
    of the same exact-step argument.

The h-chain is **TwoSum's exact-step propagation under Path A**, not
a new property.  The Session 2 / Session 3 "factor of 2^53 too
loose" gap closes because `b64_TwoSum_pathA_exact_step` makes the
error EXACTLY equal to the absorbed q (not just bounded by ulp/2).

## Deliverable — `cascade_h_chain_pathA_pos` (Qed-closed)

```coq
Lemma cascade_h_chain_pathA_pos :
  forall (x q h_prev : binary64),
    0 < Binary.B2R prec emax x ->
    strict_succ_pathA_R (Binary.B2R prec emax x)
                        (Binary.B2R prec emax q) ->
    Rabs (Binary.B2R prec emax h_prev)
      <= b64_ulp (Binary.B2R prec emax q) / 2 ->
    b64_TwoSum_safe x q ->
    Rabs (Binary.B2R prec emax h_prev)
      <= b64_ulp (Binary.B2R prec emax (snd (b64_TwoSum x q))) / 2.
Proof.
  intros x q h_prev Hx Hpw Hhprev Hsafe.
  pose proof (b64_TwoSum_pathA_exact_step x q Hx Hpw Hsafe) as [_ Hsnd_eq].
  rewrite Hsnd_eq.
  exact Hhprev.
Qed.
```

Five lines.  Composes:

  - `b64_TwoSum_pathA_exact_step` (Qed-closed in
    `B64_FastExpansionSum.v:605`).
  - The trivial fact: `ulp` of equal `R` values is equal.

`Print Assumptions` shows the same classical-axioms footprint as the
rest of the cascade infrastructure (Category C).

## Remaining work (Session 8+)

### Negative-x analog

`cascade_h_chain_pathA_neg` would mirror the positive case via
`round_eq_pathA_negative` (already Qed-closed) and an analogous
`b64_TwoSum_pathA_exact_step_negative` lemma to be added to
`B64_FastExpansionSum.v`.  Mechanical symmetry — estimated 25 lines
for the new TwoSum step lemma + 5 lines for the cascade_h_chain
analog.

### The zero-carry case (q = 0)

When the carry q = 0, the new step is trivial: `b64_TwoSum x 0`
gives `(x, 0)`.  `snd = 0`, so `ulp(snd) = bpow(emin)`.  The h-chain
link `|h_prev| <= bpow(emin)/2` requires `h_prev` to be subnormal or
zero — which is only true in degenerate cases.

But: in `nonoverlap_shewchuk`, `compress` filters zeros.  After
compress, h_new = 0 is removed; the chain skips to whatever's after,
where the loose `|h_prev| <= ulp(cs_carry)/2` bound applies.

So zero-h_new is handled by `compress`, not by the h-chain link
itself.  No round-to-even boundary tangent here.

### The general (any-sign, non-Path-A) case

The Path A precondition `|q| < ulp(pred x)/2` is tight: in the
within-source consecutive case, `nonoverlap_shewchuk e` gives `|q|
<= ulp(x)/2`, which is `ulp(pred x)/2` for non-binade-boundary x and
strictly larger for binade-boundary x.

For binade-boundary x where the inequality is non-strict, Path A's
exact-step result fails by exactly the round-to-even rule — the
documented obstacle from
`docs/stage-d-grow-expansion-nonoverlap-tangent.md`.

The h-chain in this boundary case requires the deferred-proof in
`fast_expansion_sum_nonoverlap_shewchuk`'s registry entry.  It is
not in scope for Session 7-8; it is the same obstacle that has
appeared in every Route 1 / Route 2 session.

### Composition into cascade_step_preserves_invariant

With `cascade_h_chain_pathA_pos` Qed-closed, the within-source
positive case of `cascade_step_preserves_invariant`'s clause (a)
sub-obligation now has a Coq-checkable proof path.  The remaining
work:

  1. Add clause (e) to the invariant: `|h_prev| <= ulp(active_source_max)/2`.
  2. Prove clause (e) preservation under the cascade step.
  3. In `cascade_step_preserves_invariant`, the clause (a) sub-obligation
     decomposes into (after `rev_app_distr`):
       - `strict_succ_b64 qnew h_new`: from `b64_TwoSum_nonoverlap`.
       - `strict_succ_b64 h_new h_prev`: from `cascade_h_chain_pathA_pos`
         (Session 7 result) composed with clause (e).
       - Rest of chain: inherited from old clause (a).
  4. Clauses (b), (c) preservation: straightforward threading.

Estimated 100-150 lines for Session 8 (clause e + preservation +
cascade_step_preserves_invariant).

### Session 9 scope

`fast_expansion_sum_nonoverlap_shewchuk` composition.  Compose
`cascade_step_preserves_invariant` (Session 8) with the bootstrap
to discharge the Admitted in `B64_FastExpansionSum_Shewchuk.v:483`.

The boundary-case proof (binade-boundary x with `|q| = ulp(x)/2`)
is the remaining obstacle.  Either resolve it (deep Flocq work) or
weaken the headline's precondition to "no binade boundary" (a
specific R-side constraint on the input expansions).  The latter is
likely sufficient for Stage D's downstream consumers (the
geometric-predicate inputs are coordinates with measured precision,
not adversarial binade-boundary configurations).

## What this session leaves committed

  - `theories-flocq/B64_FastExpansionSum_Shewchuk_Route2.v`:
    - `cascade_h_chain_pathA_pos` (Qed-closed, 5-line proof).
    - In-file comment block documents the h-chain decomposition and
      the negative-x / zero-q / boundary cases.
    - `Print Assumptions cascade_h_chain_pathA_pos` for audit.
  - `docs/slice-a-piece-5b-route1-session-7-outcome.md` (this file).

One new Qed-closed theorem.  Registry unchanged (4 entries).  CI
gauntlet green.

## Significance

The Route 1 series' load-bearing magnitude claim is now a 5-line Coq
proof.  The hundreds of lines of design analysis (Sessions 1-6)
were necessary to identify that:

  1. The h-chain isn't about the invariant carrying h_prev's
     magnitude (Sessions 1-3).
  2. The invariant DOES need clause (d′) per-source maxes for the
     run-bound (Sessions 4-6).
  3. **The h-chain itself decomposes to TwoSum's Path A exact-step
     property**, not a cascade-wide induction.

Step 3 is the Session 7 insight.  The "factor of 2^53" gap closes
because `b64_TwoSum_pathA_exact_step` makes the new error
**exactly** equal to the absorbed carry, not bounded by ulp/2 — so
the ulp of the new error matches the ulp of the previous carry,
and the within-source half-ulp chain lifts directly.

This is the Shewchuk Theorem 13 magnitude argument's load-bearing
content, formalised as a 5-line corollary of corpus-internal
machinery.

## CI gauntlet (this session)

```
$ bash scripts/check_admitted.sh
All Admitted theorems registered (4 total: 3 counterexample, 1 deferred-proof).

$ bash scripts/audit_axioms.sh /tmp/build.log
[axioms-audit] OK: all per-theorem PA blocks satisfy the allowlist (or are exempted).

$ bash scripts/check_readme_axioms.sh
[readme-axioms] OK: README and docs/axiom-allowlist.txt agree.
```
