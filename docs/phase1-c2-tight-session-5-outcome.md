# Phase 1 Scope C.2-tight Session 5 — outcome

**Session.** Layer 4 + headline forward-error theorem for the
x-coordinate.  Branch `claude/phase1-scope-c2-tight`, commit
`94fdd0d`.

**Two Qed-closed deliverables:**

```coq
Lemma b64_intersect_plus_x_round_error :
  ... Rabs (B2R(b64_plus (bx P0) (b64_mult s dx))
            - (B2R(bx P0) + B2R(b64_mult s dx)))
    <= bpow 28.

Theorem b64_intersect_point_x_forward_error :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (B2R(b64_intersect_point_x P0 P1 Q0 Q1)
          - (B2R(bx P0)
             + s_exact * B2R(b64_minus (bx P1) (bx P0))))
    <= bpow 29 + bpow 80 / |qp0_R - qp1_R|.
```

**The headline lands.**  Five sessions to ship vs originally
projected six — Layer 4 IS the chain composition, so no separate
composition session was needed.

**Layer 4 structure.**  `b64_round(B2R(bx P0) + b64_mult s dx)` —
final coordinate.  Delta_round_plus bound: half-ulp at magnitude
`bpow 81`, giving `bpow 28`.  Composed with layer 3's bound via
triangle, the constant tightens from `bpow 28 + (bpow 27 + bpow 26)
= 3 * bpow 28 + bpow 26` to `bpow 29` (since `bpow 28 + bpow 27 +
bpow 26 ≤ 4 * bpow 26 = bpow 28 < bpow 29`).  The denominator-condition
factor `bpow 80 / |den_exact|` carries through unchanged.

**Reference identity.**  Under int-safe inputs, `B2R(b64_minus (bx
P1) (bx P0)) = B2R(bx P1) - B2R(bx P0)` exactly (Session 1's
`b64_intersect_dx_R`).  So the reference

```
B2R(bx P0) + s_exact * B2R(b64_minus (bx P1) (bx P0))
```

equals `intersect_x_R (BP2P P0, BP2P P1, BP2P Q0, BP2P Q1)` exactly.
The Session-5 form keeps the b64-finite dx in the reference for
proof-internal cleanliness; an optional Session 6 surfaces the
`intersect_x_R` form for direct caller use.

**Lines:** ~155 added.  **Gauntlet:** green.  **Registry:** unchanged at 4.
