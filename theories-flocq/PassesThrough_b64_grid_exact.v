(* ============================================================================
   PassesThrough_b64_grid_exact.v
   ----------------------------------------------------------------------------
   Issue #66, the snap-rounding / passes-through RGR pivot (see
   docs/snap-rounding-rgr-pivot.md and docs/oracle-soundness-finding.md).

   GOAL (C1, "grid exactness").  On the integer / unit grid the ROUNDED compute
   filter agrees bit-for-bit with the EXACT R-spec:

       b64_on_grid P0 -> b64_on_grid P1 ->
         b64_passes_through_hot_pixel_compute P0 P1 C
           = b64_passes_through_hot_pixel P0 P1 C.

   This is the constructive payoff of the pivot: the compute filter is
   machine-checked UNSOUND off the grid (PassesThrough_b64_compute_unsound.v),
   but a snap-rounding noder only ever evaluates it on snapped (grid-aligned)
   coordinates -- and there it coincides with the exact spec, which is sound
   (HotPixel_b64.b64_passes_through_sound).  Strongly evidenced: 0 divergence in
   5,000,000 on-grid cases (docs/oracle-soundness-finding.md).

   THIS FILE lands the REDUCTION layer, Qed-closed: on the grid the
   snap-consistency second conjunct of `passes_through` is vacuous (a grid point
   is a fixed point of `b64_snap`), so the full predicate collapses to a single
   Liang-Barsky touch -- for BOTH the rounded compute filter and the exact spec.
   C1 therefore reduces to the single-touch equivalence
       b64_liang_barsky_touches_compute = b64_liang_barsky_touches  (on grid),
   which isolates the remaining obligation to ONE touch: that the
   round-to-nearest errors in the divide-and-clip t-bounds never flip the
   composite `max(..) <= min(..)` comparison on the grid.  That core is the
   genuinely hard, multi-session step (see the OBLIGATION note at the bottom);
   it is NOT discharged here and NO `Admitted` is introduced -- the file is
   Qed-clean and the open core is stated as a comment, not an axiom.

   Corpus invariant preserved: no Admitted / Axiom / Parameter.
   ============================================================================ *)

From Stdlib Require Import Bool.
From Flocq Require Import IEEE754.Binary.

From NTS.Proofs.Flocq Require Import Validate_binary64.
From NTS.Proofs.Flocq Require Import HotPixel_b64.
From NTS.Proofs.Flocq Require Import SnapRounding_b64.
From NTS.Proofs.Flocq Require Import PassesThrough_b64_compute.

(* "On the grid" = a fixed point of the unit-grid snap.  This is exactly the
   regime a snap-rounding noder runs in: by `b64_snap_on_grid` below, every
   snapped coordinate satisfies it. *)
Definition b64_on_grid (P : BPoint) : Prop := b64_snap P = P.

(* Post-snap points are grid-aligned (finite coordinates).  So the grid
   hypotheses of the lemmas below are discharged for any noder input after the
   snap step -- the regime in which the filter is actually consulted. *)
Lemma b64_snap_on_grid :
  forall P : BPoint,
    Binary.is_finite prec emax (bx P)  = true ->
    Binary.is_finite prec emax (by_ P) = true ->
    b64_on_grid (b64_snap P).
Proof.
  intros P Hx Hy. unfold b64_on_grid.
  apply b64_snap_idempotent_finite; assumption.
Qed.

(* On the grid the EXACT-spec passes-through predicate collapses to a single
   Liang-Barsky touch: the snapped endpoints equal the originals, so its
   snap-consistency conjunct repeats the first. *)
Lemma b64_passes_through_collapses_on_grid :
  forall P0 P1 C : BPoint,
    b64_on_grid P0 -> b64_on_grid P1 ->
    b64_passes_through_hot_pixel P0 P1 C = b64_liang_barsky_touches P0 P1 C.
Proof.
  intros P0 P1 C H0 H1.
  unfold b64_passes_through_hot_pixel, b64_on_grid in *.
  rewrite H0, H1. apply Bool.andb_diag.
Qed.

(* Same collapse for the ROUNDED compute filter, using the computational
   `b64_snap` (the very same operator). *)
Lemma b64_passes_through_compute_collapses_on_grid :
  forall P0 P1 C : BPoint,
    b64_on_grid P0 -> b64_on_grid P1 ->
    b64_passes_through_hot_pixel_compute P0 P1 C
      = b64_liang_barsky_touches_compute P0 P1 C.
Proof.
  intros P0 P1 C H0 H1.
  unfold b64_passes_through_hot_pixel_compute, b64_on_grid in *.
  rewrite H0, H1. apply Bool.andb_diag.
Qed.

(* REDUCTION (Qed).  On the grid, full-predicate grid-exactness (C1) is
   EQUIVALENT to the single-touch grid-exactness.  Both snap-consistency
   conjuncts are discharged, so nothing remains but the one rounded-vs-exact
   Liang-Barsky touch. *)
Theorem b64_passes_through_grid_exact_iff_touch :
  forall P0 P1 C : BPoint,
    b64_on_grid P0 -> b64_on_grid P1 ->
    ( b64_passes_through_hot_pixel_compute P0 P1 C
        = b64_passes_through_hot_pixel P0 P1 C
      <->
      b64_liang_barsky_touches_compute P0 P1 C
        = b64_liang_barsky_touches P0 P1 C ).
Proof.
  intros P0 P1 C H0 H1.
  rewrite (b64_passes_through_collapses_on_grid P0 P1 C H0 H1).
  rewrite (b64_passes_through_compute_collapses_on_grid P0 P1 C H0 H1).
  tauto.
Qed.

(* ----------------------------------------------------------------------------
   REMAINING OBLIGATION (the hard, multi-session core -- NOT an axiom).

     Open goal (single-touch grid exactness), strongly evidenced (0/5e6):
       forall P0 P1 C, <P0,P1,C on the integer grid> ->
         b64_liang_barsky_touches_compute P0 P1 C
           = b64_liang_barsky_touches P0 P1 C.

   Why it is hard: on the grid the slab guards and the t-bound NUMERATORS /
   DENOMINATORS (b64_minus of half-integers) are exact, but the t-bounds
   themselves are `b64_div`, which ROUNDS.  Round-to-nearest gives no outward
   guarantee, so the rounded `Rmax 0 (...) <= Rmin 1 (...)` comparison is not
   definitionally the exact one.

   Strategy for the core (next session): rewrite the exact comparison
   `lb_tlo <= lb_thi` etc. by CROSS-MULTIPLYING through the (exact integer)
   denominators, turning each pairwise t-bound comparison into the SIGN of an
   integer determinant -- a decision that does not divide and is exactly
   representable in binary64 on the grid (cf. Orient_b64_exact.v's dyadic
   exactness, b64_minus_int_exact / b64_mult_int_exact).  Then show the rounded
   `b64_div`-based comparison has the same outcome because the integer
   determinant is nonzero-with-gap >= 1 except in the exactly-equal case the
   rounding also preserves.
   ---------------------------------------------------------------------------- *)
