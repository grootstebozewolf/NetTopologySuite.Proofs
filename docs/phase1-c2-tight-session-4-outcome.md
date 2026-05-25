# Phase 1 Scope C.2-tight Session 4 — outcome

**Session.** Layer 3: forward-error bound for `b64_mult s dx`.
Branch `claude/phase1-scope-c2-tight`, commit `b8909f3`.

**Four Qed-closed deliverables:**

```coq
Lemma b64_ulp_le_at_magnitude_uniform :
  forall x n,
    (0 <= n)%Z -> Rabs x <= bpow radix2 n ->
    b64_ulp x <= bpow radix2 (n - prec + 1).

Lemma b64_intersect_mult_x_round_error :
  ... Rabs (B2R(b64_mult s dx) - B2R(s) * B2R(dx)) <= bpow 27.

Lemma b64_intersect_mult_x_carry_error :
  ... Rabs (B2R(s) * B2R(dx) - s_exact * B2R(dx))
    <= bpow 26 + bpow 80 / |den_exact|.

Theorem b64_intersect_mult_x_forward_error :
  ... Rabs (B2R(b64_mult s dx) - s_exact * B2R(dx))
    <= bpow 27 + bpow 26 + bpow 80 / |den_exact|.
```

**Aux generalisation.**  `b64_ulp_le_at_magnitude_uniform` parameterises
the magnitude exponent `n`.  At `n=53` it subsumes Session 3's
specialised `_53_uniform`; at `n=54` it subsumes Session 1's `_54`;
at `n=80` it serves layer 3; at `n=81` it will serve layer 4 (Session
5).  Single aux for all four layers.

**Layer 3 pattern.**  Same `Delta_round + Delta_carry + triangle`
decomposition as Session 3.  Delta_carry composes Session 3's
`b64_intersect_s_forward_error` with `b64_intersect_dx_abs_le_bpow_26`,
giving `bpow 26 + bpow 80 / |den_exact|`.  Delta_round_mul is the
half-ulp bound at magnitude `bpow 80`.

**Single-session layer.**  Layer 3 came in at one session vs Layer 2's
two — the aux pattern from Session 3 carried over directly, validating
the calibration hypothesis (pattern-reuse cuts per-layer cost).

**Lines:** ~206 added.  **Gauntlet:** green.  **Registry:** unchanged at 4.
