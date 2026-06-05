(* ============================================================================
   NetTopologySuite.Proofs.Flocq.PassesThrough_b64_compute_refine
   ----------------------------------------------------------------------------
   COMPUTE-LEVEL refinement: the half-open computational hot-pixel filter is
   strictly tighter than the closed one.

   The corpus already proves this ordering at the EXACT-SPEC level
   (`b64_liang_barsky_touches_halfopen_implies_closed`,
   PassesThroughHalfopen_b64.v).  The two EXTRACTABLE oracle compute modes
   (`PASSES_THROUGH_HALFOPEN` vs `PASSES_THROUGH_FILTER`,
   PassesThrough_b64_compute.v) deserve the same guarantee: a `true` from the
   half-open compute filter implies a `true` from the closed compute filter.

   This is a purely structural / boolean fact -- no `B2R`, no rounding
   analysis.  The half-open compute predicate's conjuncts are exactly the
   closed predicate's two conjuncts (the SAME `b64_le tmin tmax` overlap test,
   and the per-axis slab guards strengthened from `b64_lt` to `b64_le`) plus
   two extra strict-upper midpoint checks; dropping the extras and weakening
   the guards lands on the closed predicate.
   ========================================================================== *)

From Flocq Require Import IEEE754.Binary.
From NTS.Proofs.Flocq Require Import Validate_binary64.
From NTS.Proofs.Flocq Require Import HotPixel_b64.
From NTS.Proofs.Flocq Require Import PassesThrough_b64_compute.

(* A strict `b64_lt` decides `b64_le`: both route through `b64_compare`, and a
   `Some Lt` verdict satisfies the `Some Lt | Some Eq` pattern of `b64_le`. *)
Lemma b64_lt_implies_le : forall x y : binary64,
  b64_lt x y = true -> b64_le x y = true.
Proof.
  intros x y H. unfold b64_lt in H. unfold b64_le.
  destruct (b64_compare x y) as [c|]; [ destruct c | ]; try discriminate; reflexivity.
Qed.

(* The half-open per-axis slab guard implies the closed one (only the
   degenerate axis-parallel case differs: strict `<` upper vs `<=`). *)
Lemma b64_lb_inslab_halfopen_implies_closed : forall c0 c1 lo hi : binary64,
  b64_lb_inslab_halfopen c0 c1 lo hi = true ->
  b64_lb_inslab_closed   c0 c1 lo hi = true.
Proof.
  intros c0 c1 lo hi H.
  unfold b64_lb_inslab_halfopen in H. unfold b64_lb_inslab_closed.
  destruct (b64_eqb c1 c0).
  - apply Bool.andb_true_iff in H. destruct H as [Hlo Hhi].
    apply Bool.andb_true_iff. split; [ exact Hlo | apply b64_lt_implies_le; exact Hhi ].
  - reflexivity.
Qed.

(* Compute-level half-open ⇒ closed for the single-segment touch. *)
Lemma b64_liang_barsky_touches_halfopen_compute_implies_closed :
  forall P0 P1 C : BPoint,
    b64_liang_barsky_touches_halfopen_compute P0 P1 C = true ->
    b64_liang_barsky_touches_compute          P0 P1 C = true.
Proof.
  intros P0 P1 C H.
  unfold b64_liang_barsky_touches_halfopen_compute in H. cbv zeta in H.
  unfold b64_liang_barsky_touches_compute. cbv zeta.
  apply Bool.andb_true_iff in H. destruct H as [H _Hmid].
  apply Bool.andb_true_iff in H. destruct H as [Hins Hle].
  apply Bool.andb_true_iff in Hins. destruct Hins as [Hix Hiy].
  apply Bool.andb_true_iff. split; [ | exact Hle ].
  apply Bool.andb_true_iff. split;
    [ apply b64_lb_inslab_halfopen_implies_closed; exact Hix
    | apply b64_lb_inslab_halfopen_implies_closed; exact Hiy ].
Qed.

(* The headline: the half-open compute passes-through predicate refines the
   closed one (touch on original AND snapped segment, both refine). *)
Theorem b64_passes_through_hot_pixel_halfopen_compute_implies_closed :
  forall P0 P1 C : BPoint,
    b64_passes_through_hot_pixel_halfopen_compute P0 P1 C = true ->
    b64_passes_through_hot_pixel_compute          P0 P1 C = true.
Proof.
  intros P0 P1 C H.
  unfold b64_passes_through_hot_pixel_halfopen_compute in H.
  unfold b64_passes_through_hot_pixel_compute.
  apply Bool.andb_true_iff in H. destruct H as [Ho Hs].
  apply Bool.andb_true_iff. split;
    apply b64_liang_barsky_touches_halfopen_compute_implies_closed; assumption.
Qed.

Print Assumptions b64_passes_through_hot_pixel_halfopen_compute_implies_closed.
