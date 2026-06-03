# Phase 1 Scope C.2-tight Session 1 — outcome

**Session.** Layer 1: forward-error bound for the denominator.
Branch `claude/phase1-scope-c2-tight`, commit `379e16a`.

**Deliverable** (Qed-closed):

```coq
Theorem b64_intersect_den_forward_error :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (B2R(b64_minus (b64_orient2d Q0 Q1 P0) (b64_orient2d Q0 Q1 P1))
          - (cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1))
    <= bpow radix2 1.
```

Bound is sharp at one half-ulp of a maximum-magnitude integer
denominator (|den_exact| <= bpow 54 ⇒ ulp ≤ bpow 2 ⇒ half ≤ bpow 1 = 2).

**Aux lemma introduced:** `b64_ulp_le_at_magnitude_54` (later
subsumed by `_uniform` in Session 4).

**Composition:** Scope B.1's `b64_intersect_den_R_round` +
`b64_error_le_half_ulp_round` + `b64_intersect_den_B2R_abs_le_bpow_54`
+ `b64_intersect_den_B2R_abs_ge_1` + Flocq's `ulp_FLT_le`.

**Lines:** ~75 added.  **Gauntlet:** green.  **Registry:** unchanged at 4.
