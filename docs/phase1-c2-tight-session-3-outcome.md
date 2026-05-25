# Phase 1 Scope C.2-tight Session 3 — outcome

**Session.** Layer 2 Delta_round + composition into full layer-2
forward error.  Branch `claude/phase1-scope-c2-tight`, commit
`2e3b9a9`.

**Three Qed-closed deliverables:**

```coq
Lemma b64_ulp_le_at_magnitude_53_uniform :
  forall x : R,
    Rabs x <= bpow radix2 53 -> b64_ulp x <= bpow radix2 1.

Lemma b64_intersect_s_round_error :
  ... Rabs (b64_round (qp0_R / den_R) - qp0_R / den_R) <= 1.

Theorem b64_intersect_s_forward_error :
  ... Rabs (B2R(b64_div ...) - qp0_R / (qp0_R - qp1_R))
    <= 1 + bpow 54 / |qp0_R - qp1_R|.
```

**The Session 2 wall cleared.**  `b64_ulp_le_at_magnitude_53_uniform`
handles the b64_round result uniformly across normal, subnormal, and
zero regimes via the `ulp_FLT_small` / `ulp_FLT_le` case split.  The
case-split is local to this aux lemma, so the layer-2 bound becomes
a clean half-ulp argument.

**Composition:** layer-2 = Delta_round + Delta_carry via triangle
inequality.  Bound `1 + bpow 54 / |den_exact|`: saturates at `~bpow
55` for `|den_exact| = 1` (near-parallel), drops to `1` for large
denominator separation.  The `1/|den_exact|` factor is the classical
Cramer condition number.

(`_53_uniform` is later subsumed by Session 4's general
`b64_ulp_le_at_magnitude_uniform` aux — see retro.)

**Lines:** ~115 added.  **Gauntlet:** green.  **Registry:** unchanged at 4.
