# Phase 1 Scope C.2-tight Session 6 — outcome

**Session.** Reference bridge + `HasIntersect_sound` typeclass +
`HasIntersect_sound_BPoint` instance.  Branch
`claude/phase1-scope-c2-tight`.

**Five Qed-closed deliverables:**

```coq
Lemma c2tight_ref_x_eq_intersect_x_R :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    B2R(bx P0) + s_exact * B2R(b64_minus (bx P1) (bx P0))
    = intersect_x_R (BP2P P0) (BP2P P1) (BP2P Q0) (BP2P Q1).

Lemma c2tight_ref_y_eq_intersect_y_R : (* same, y-coordinate *).

Theorem b64_intersect_point_x_forward_error_vs_intersect_x_R :
  forall P0 P1 Q0 Q1 : BPoint,
    intersect_point_inputs_int_safe P0 P1 Q0 Q1 ->
    Rabs (B2R(b64_intersect_point_x P0 P1 Q0 Q1)
          - intersect_x_R (BP2P P0) (BP2P P1) (BP2P Q0) (BP2P Q1))
    <= bpow 29 + bpow 80 / |cross_R_BP Q0 Q1 P0 - cross_R_BP Q0 Q1 P1|.

Theorem b64_intersect_point_y_forward_error_vs_intersect_y_R :
  (* same, y-coordinate *).

Instance HasIntersect_sound_BPoint : HasIntersect_sound BPoint := { ... }.
```

**The bridge** composes `b64_intersect_dx_R` (bit-exact dx step under
int-safe) with `cross_R_BP_eq_cross_BP2P` (the BPoint -> Point
projection's commutation with `cross`).  Both bridge lemmas were
already in the corpus; Session 6 just threaded them.

**The local `BP2P` duplicate at `Intersect_b64_exact.v:102` was
removed** — `Intersect_b64.BP2P` (imported) is identical and is the
one referenced by `cross_R_BP_eq_cross_BP2P`.  Eliminating the
duplicate makes the bridge apply directly without a `Definition`-vs-
`Definition` equality detour.

**The typeclass `HasIntersect_sound`** layers on top of
`HasIntersect`.  Three fields (`intersect_ref_x`, `intersect_ref_y`,
`intersect_error_bound`) and two soundness obligations.  The
`HasIntersect_sound_BPoint` instance instantiates with the C.2-tight
references and bound:

```coq
intersect_ref_x       := fun A B C D =>
                           intersect_x_R (BP2P A) (BP2P B) (BP2P C) (BP2P D);
intersect_ref_y       := fun A B C D =>
                           intersect_y_R (BP2P A) (BP2P B) (BP2P C) (BP2P D);
intersect_error_bound := fun A B C D =>
                           bpow 29 + bpow 80
                                     / |cross_R_BP C D A - cross_R_BP C D B|;
```

**Phase 1 fully shipped end-to-end.**  The footer's optional
remainder narrows to a K * eps restatement (algebraic, equivalent to
the current bound).

**Lines:** ~110 added.  **Gauntlet:** green.  **Registry:** unchanged at 4.
