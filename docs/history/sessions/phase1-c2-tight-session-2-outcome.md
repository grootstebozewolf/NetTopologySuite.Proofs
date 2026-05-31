# Phase 1 Scope C.2-tight Session 2 — outcome

**Session.** Layer 2 Delta_carry: the pure-R perturbation of the
quotient under denominator rounding.  Branch
`claude/phase1-scope-c2-tight`, commit `3206ab6`.

**Honest scope-down.**  Originally planned to land the full layer 2
bound (Delta_round + Delta_carry).  Hit the subnormal-range ulp
bookkeeping wall on Delta_round and reverted an `Admitted`-using
proof attempt.  Shipped Delta_carry only, deferring Delta_round to
Session 3.

**Deliverable** (Qed-closed):

```coq
Theorem b64_intersect_s_carry_error :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (qp0_R / B2R(den) - qp0_R / (qp0_R - qp1_R))
    <= bpow radix2 54 / |qp0_R - qp1_R|.
```

Algebraic identity:
`qp0_R / den_R - qp0_R / den_exact
 = qp0_R * (den_exact - den_R) / (den_R * den_exact)`.

Bound chain:
- `|qp0_R| <= bpow 53` (cross_R_BP_abs_le_bpow_53).
- `|den_R - den_exact| <= bpow 1` (Session 1).
- `|den_R| >= 1` (b64_intersect_den_B2R_abs_ge_1).
- combined `<= bpow 53 * bpow 1 / (1 * |den_exact|) = bpow 54 / |den_exact|`.

**Lines:** ~115 added.  **Gauntlet:** green.  **Registry:** unchanged at 4.
