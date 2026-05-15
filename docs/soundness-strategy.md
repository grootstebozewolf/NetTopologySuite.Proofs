# Soundness strategy for `b64_orient_sign_filtered`

**Status.** Written 2026-05-15 after pivoting away from a Shewchuk-style
forward-error attempt. This document records the path tried, why it
didn't satisfy the project's "shipping over scaffolding" preference, and
the alternative path now being pursued. Both paths remain technically
viable; the choice between them is a question of effort vs. coverage,
not correctness.

## Goal

Close the cross-product soundness theorem for the Stage A filter:

```coq
Theorem b64_orient_sign_filtered_sound :
  forall P0 P1 Q,
    b64_orient2d_inputs_safe P0 P1 Q ->
    match b64_orient_sign_filtered P0 P1 Q with
    | OrientRPos       => 0 < cross_R_BP P0 P1 Q
    | OrientRNeg       => cross_R_BP P0 P1 Q < 0
    | OrientRZero      => cross_R_BP P0 P1 Q = 0
    | OrientRNan       => True
    | OrientRUncertain => True
    end.
```

Here `cross_R_BP` is the exact mathematical cross product on the
`B2R`-lifted coordinates, with no rounding. The headline says: when the
five-valued sign decoder commits, it agrees with the exact real-valued
sign.

The "internal consistency" half — that the decoder agrees with the sign
of the *rounded* binary64 value `B2R (b64_orient2d P0 P1 Q)` — is already
proved Qed-closed in
[`Orient_b64_sound.v`](../theories-flocq/Orient_b64_sound.v) as
`b64_orient_sign_filtered_consistent_with_b64`. What's missing is the
step from the rounded value's sign to the exact value's sign.

## Path 1 (attempted): Shewchuk-style forward-error analysis

The textbook approach. Bound the rounding error of the whole
`b64_orient2d` evaluation as a function of `b64_detsum`, the magnitude
sum that drives the filter's threshold. When `|B2R det| > errbound *
detsum` (the filter's pass condition) and `|B2R det - cross_R| <=
errbound * detsum` (the forward-error bound), the sign of `cross_R`
necessarily matches the sign of `B2R det` by triangle inequality.

### What got built

In [`B64_bridge.v`](../theories-flocq/B64_bridge.v) (slice 2a, commit
`956070f`):

```coq
Lemma b64_plus_abs_error :
  forall x y, b64_safe Rplus x y ->
    Rabs (B2R (b64_plus x y) - (B2R x + B2R y))
      <= ulp radix2 (SpecFloat.fexp prec emax) (B2R x + B2R y).

Lemma b64_minus_abs_error : (* analogous *)
Lemma b64_mult_abs_error  : (* analogous *)
```

These are *per-operation* absolute error bounds, lifted unconditionally
from Flocq's `error_le_ulp`. They are correct, Qed-closed, and free of
axioms — but they are also the easy part.

### Where it stalled

The headline theorem needs three more layers above these per-op bounds:

- **Slice 2b — relative-error versions.** `ulp v <= bpow(-prec+1) * |v|`
  for normal `v`, but the absolute-error form is loose. Shewchuk's
  analysis works in relative-error space:
  `|round(v) - v| <= (1/2) * bpow(-prec+1) * |v|`. This needs
  `Prop.Relative.relative_error_N_FLT` plus a normal-range precondition.
  Estimated 1–2 sessions.

- **Slice 2c — chain composition.** Thread the per-op errors through
  the four `b64_minus`, two `b64_mult`, and outer `b64_minus` chain of
  `b64_orient2d` to derive Shewchuk's
  `(3 + 16·eps)·eps·(|t1| + |t2|)` bound. The `3·eps` is from three
  rounding operations on the surviving terms; the `16·eps` is
  higher-order cross terms. This is genuine accumulation analysis with
  no obvious shortcut. Estimated 2–3 sessions.

- **Slice 3 — soundness composition.** Trivial once 2c lands: triangle
  inequality, ~20 lines.

### Why it didn't satisfy

The slice 2a lemmas are mechanical wrappers over a single Flocq theorem.
They don't move the substantive ball — the substantive ball is slice 2c,
which is the actual accumulation analysis the corpus invariant exists
to enforce. Shipping 2a as "progress" risks framing the headline as
close when it isn't; the user's reaction (`"this seems to plaster over
what we want to proove"`) was correctly identifying that the scaffolding
multiplication would continue through 2b before any payoff. Three more
sessions of scaffolding to reach the headline is too much
work-in-flight for a single-maintainer project where the cost of a
dropped thread is high.

The slice 2a lemmas stay in `B64_bridge.v`. They are reusable building
blocks for whoever does pick up Path 1 in the future. They are not
deleted, just demoted from "critical path" to "useful primitive".

## Path 2 (in progress): integer-coordinate exact regime

The novel approach. Restrict the soundness claim to a coordinate
*regime* in which `b64_orient2d` is bit-exact — no rounding error at
all — and then the rounded-value sign trivially equals the exact-value
sign because they are the same value.

### The regime

`coord_small_integer x` := `is_finite x = true /\ (exists n : Z,
B2R x = IZR n /\ Z.abs n <= 2^25)`.

That is, coordinates that are integer-valued and fit in 25 bits of
magnitude (so 26 bits including sign).

### Why every operation in `b64_orient2d` is exact in this regime

- **Subtraction `bx P1 - bx P0`.** Sterbenz's theorem: if
  `y/2 <= x <= 2y` (in magnitude), `b64_minus x y` is exact. For
  same-sign integers in `[-2^25, 2^25]` the bound holds. For
  opposite-sign integers the difference is at most `2^26` in magnitude
  and still integer-valued, which is exactly representable (binary64
  represents all integers up to `2^53` exactly).
  In general: any integer-valued difference with `|diff| <= 2^53` is
  exact. Both operands `<= 2^25` give `|diff| <= 2^26 << 2^53`.

- **Multiplication of two such differences.** Each difference is an
  integer with magnitude `<= 2^26`. Their product is an integer with
  magnitude `<= 2^52`. Binary64 represents every integer up to `2^53`
  exactly, so the rounded result equals the exact product.

- **Outer subtraction of two products.** Each product is an integer
  with `|p| <= 2^52`. Their difference is an integer with `|d| <=
  2^53`. Exactly representable.

So `B2R (b64_orient2d P0 P1 Q) = cross_R_BP P0 P1 Q` *on the nose*, no
inequality, no error budget. Composing with the already-proved decoder
consistency gives the headline directly.

### Trade-off

Path 2 covers a strictly smaller regime than Path 1 would: 26-bit
integer coordinates rather than the full `|coord| <= 2^500` bound that
`b64_safe_coord_bound` permits. But:

- 26-bit integer coordinates cover most real-world GIS use cases when
  inputs are gridded (tile coordinates, snapped vertices, integer
  millimetres).
- It ships an end-to-end headline *now*, not in three sessions.
- The `cross_R_BP` soundness for the unrestricted bounded regime is
  not closed off — Path 1 remains available if/when someone wants to
  invest the effort.

### What gets built

In a new file (likely `theories-flocq/Orient_b64_exact.v`):

```coq
Definition coord_small_integer (x : binary64) : Prop := ...

Lemma b64_minus_exact_small_int :
  forall x y, coord_small_integer x -> coord_small_integer y ->
    B2R (b64_minus x y) = B2R x - B2R y.

Lemma b64_mult_exact_of_bounded_int :
  forall x y : binary64,
    (exists nx, B2R x = IZR nx /\ Z.abs nx <= 2^26) ->
    (exists ny, B2R y = IZR ny /\ Z.abs ny <= 2^26) ->
    B2R (b64_mult x y) = B2R x * B2R y.

(* compose through the orient2d chain *)
Theorem b64_orient2d_exact_for_small_integers :
  forall P0 P1 Q,
    (forall c, In c [bx P0; by_ P0; bx P1; by_ P1; bx Q; by_ Q] ->
       coord_small_integer c) ->
    B2R (b64_orient2d P0 P1 Q) = cross_R_BP P0 P1 Q.

Theorem b64_orient_sign_filtered_sound_small_int :
  forall P0 P1 Q,
    (forall c, In c [...] -> coord_small_integer c) ->
    b64_orient2d_safe P0 P1 Q ->
    match b64_orient_sign_filtered P0 P1 Q with
    | OrientRPos       => 0 < cross_R_BP P0 P1 Q
    | OrientRNeg       => cross_R_BP P0 P1 Q < 0
    | OrientRZero      => cross_R_BP P0 P1 Q = 0
    | OrientRNan       => True
    | OrientRUncertain => True
    end.
```

The exactness theorem is independent of the filter — once it's proved,
the headline composes mechanically with
`b64_orient_sign_filtered_consistent_with_b64`.

## Future paths left open

Neither path is exclusive. A future maintainer can take any of:

1. **Complete Path 1.** Slices 2b → 2c → 3 give cross_R soundness for
   the full magnitude-bounded regime. The 2a lemmas in
   `B64_bridge.v` are the starting point.

2. **Extend Path 2's regime.** Sterbenz alone gives exact subtraction
   in much wider ranges than 26-bit integers. With more careful
   bookkeeping, "small floating-point" inputs (any subnormal-free
   inputs whose products land in normal range) can also be made
   exact.

3. **Bridge to Shewchuk Stages B/C/D.** The Stage A filter only commits
   when the sign is unambiguous; Stages B/C/D refine `OrientRUncertain`
   by computing in expansion arithmetic. This is a long-term
   engagement separate from the current soundness gap. See
   [audit-shewchuk-stages.md](audit-shewchuk-stages.md) for the
   library audit.

The corpus invariant — no `Admitted`, no `Axiom`, no `Parameter` —
holds for everything shipped, and is preserved by both paths.
