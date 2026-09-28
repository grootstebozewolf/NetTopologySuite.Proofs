(* ============================================================================
   NetTopologySuite.Proofs.ArcSweepCcw
   ----------------------------------------------------------------------------
   Issue #64 subtask 64-b — GREEN: a circular-arc sweep is counter-clockwise
   iff its signed central angle is strictly positive.

   Reuses the Option-A signed-angle stack (`Atan2.atan2`,
   `AngleBetween.angle_between`, `InArc.central_angle`) and the classical
   orientation cross/dot of the two radius vectors.  No new analytic
   machinery: the biconditional is the atan2 sign reading of
   `angle_between = atan2(cross,dot)`, proved by case analysis on the
   definition (sqrt-free — unit-vector normalisation is never materialised).

     sweep_ccw O A B
       :=  0 < cross(OA,OB)  ∨  (cross = 0 ∧ dot(OA,OB) < 0)
     central_angle O A B
       :=  angle_between (A−O) (B−O)   ∈ (−π, π]

   Headlines (nonzero radius vectors A≠O, B≠O):

     sweep_ccw_iff_signed_central_angle_pos
       :  sweep_ccw O A B  ↔  0 < central_angle O A B

   The cross > 0 arm is the strict left turn (classical CCW orientation).
   The cross = 0 ∧ dot < 0 arm is the antipodal +π cut that atan2 assigns
   to the positive principal branch (e.g. the upper unit semicircle
   (1,0)→(−1,0)).  Complementary arms of the sign trichotomy:

     central_angle = 0  →  ~ sweep_ccw   (zero / collinear same-ray)
     central_angle < 0  →  ~ sweep_ccw   (CW / negative principal sweep)

   Rational unit-circle witnesses (O = origin):
     A=(1,0), B=(0,1)   — CCW quarter, angle = π/2 > 0
     A=(1,0), B=(0,-1)  — CW quarter,  angle = −π/2 < 0
     A=(1,0), B=(-1,0)  — +π semicircle (atan2 cut), still CCW

   3-axiom (IVT atan2 via AngleBetween; allowlist).  No Admitted.

   Refs: issue #64, docs/issue-64-arc-primitives-triage.md (ask #2 / sweep).
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Grok (grok-4.5)
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance Atan2 AngleBetween InArc.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Sqrt-free sign reading of atan2 / angle_between.                       *)
(* -------------------------------------------------------------------------- *)

(** Positive principal polar angle ↔ open upper half-plane, or the negative
    abscissa (atan2's +π cut).  Pure case analysis on [atan2]; no sqrt. *)
Lemma atan2_pos_iff : forall y x : R,
  ~ (x = 0 /\ y = 0) ->
  (0 < atan2 y x) <-> (0 < y \/ (y = 0 /\ x < 0)).
Proof.
  intros y x Hnz. apply Atan2.atan2_pos_iff. exact Hnz.
Qed.

(** Vector form: positive [angle_between] ↔ positive cross, or antipodal cut. *)
Lemma angle_between_pos_iff : forall ux uy vx vy : R,
  ~ (ux = 0 /\ uy = 0) ->
  ~ (vx = 0 /\ vy = 0) ->
  (0 < angle_between ux uy vx vy)
  <->
  (0 < (ux * vy - uy * vx)
   \/ ((ux * vy - uy * vx) = 0 /\ (ux * vx + uy * vy) < 0)).
Proof.
  intros ux uy vx vy Hu Hv.
  unfold angle_between.
  apply atan2_pos_iff.
  apply dotcross_nonzero; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  Sweep CCW predicate (orientation reading of the principal sweep).      *)
(* -------------------------------------------------------------------------- *)

(** Twice-signed area of triangle [O A B] (cross of radius vectors OA, OB).
    Same algebraic shape as [Orientation.cross] / [ArcOrient.cross_R_pt]
    with base point [O]. *)
Definition radius_cross (O A B : Point) : R :=
  (px A - px O) * (py B - py O) - (py A - py O) * (px B - px O).

(** Dot product of radius vectors OA · OB. *)
Definition radius_dot (O A B : Point) : R :=
  (px A - px O) * (px B - px O) + (py A - py O) * (py B - py O).

(** [sweep_ccw O A B]: the principal directed sweep from ray [O]->[A] to
    ray [O]->[B] is counter-clockwise.

    Orientation / cross-sign reading of a strictly positive principal
    central angle:
      - strict left turn: [radius_cross > 0];
      - antipodal +π cut: [radius_cross = 0] and [radius_dot < 0]
        (atan2 lands on +π, not −π). *)
Definition sweep_ccw (O A B : Point) : Prop :=
  0 < radius_cross O A B
  \/ (radius_cross O A B = 0 /\ radius_dot O A B < 0).

(* -------------------------------------------------------------------------- *)
(* §3  Headline biconditional.                                                *)
(* -------------------------------------------------------------------------- *)

(** Counter-clockwise principal sweep ↔ signed central angle strictly
    positive.  Hypotheses: nonzero radius vectors (A and B off the centre). *)
Theorem sweep_ccw_iff_signed_central_angle_pos :
  forall O A B : Point,
    ~ (px A - px O = 0 /\ py A - py O = 0) ->
    ~ (px B - px O = 0 /\ py B - py O = 0) ->
    sweep_ccw O A B <-> 0 < central_angle O A B.
Proof.
  intros O A B Hu Hv.
  unfold sweep_ccw, radius_cross, radius_dot, central_angle.
  (* Both sides are the atan2-positive reading of (cross,dot). *)
  rewrite angle_between_pos_iff by assumption.
  tauto.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Complementary arms (zero-angle and CW) of the sign trichotomy.         *)
(* -------------------------------------------------------------------------- *)

(** Zero principal sweep ⇒ not CCW (same ray, including A = B off centre). *)
Lemma sweep_ccw_false_of_central_angle_zero :
  forall O A B : Point,
    ~ (px A - px O = 0 /\ py A - py O = 0) ->
    ~ (px B - px O = 0 /\ py B - py O = 0) ->
    central_angle O A B = 0 ->
    ~ sweep_ccw O A B.
Proof.
  intros O A B Hu Hv Hz Hccw.
  apply sweep_ccw_iff_signed_central_angle_pos in Hccw; [| assumption | assumption].
  lra.
Qed.

(** Negative (CW) principal sweep ⇒ not CCW. *)
Lemma sweep_ccw_false_of_central_angle_neg :
  forall O A B : Point,
    ~ (px A - px O = 0 /\ py A - py O = 0) ->
    ~ (px B - px O = 0 /\ py B - py O = 0) ->
    central_angle O A B < 0 ->
    ~ sweep_ccw O A B.
Proof.
  intros O A B Hu Hv Hneg Hccw.
  apply sweep_ccw_iff_signed_central_angle_pos in Hccw; [| assumption | assumption].
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Rational unit-circle witnesses.                                        *)
(* -------------------------------------------------------------------------- *)

Definition sweep_O : Point := mkPoint 0 0.
Definition sweep_A : Point := mkPoint 1 0.
Definition sweep_B_ccw : Point := mkPoint 0 1.
Definition sweep_B_cw : Point := mkPoint 0 (-1).
Definition sweep_B_pi : Point := mkPoint (-1) 0.

Lemma sweep_radius_A_nonzero :
  ~ (px sweep_A - px sweep_O = 0 /\ py sweep_A - py sweep_O = 0).
Proof. unfold sweep_A, sweep_O; cbn [px py]. intros [Hx _]. lra. Qed.

Lemma sweep_radius_B_ccw_nonzero :
  ~ (px sweep_B_ccw - px sweep_O = 0 /\ py sweep_B_ccw - py sweep_O = 0).
Proof. unfold sweep_B_ccw, sweep_O; cbn [px py]. intros [_ Hy]. lra. Qed.

Lemma sweep_radius_B_cw_nonzero :
  ~ (px sweep_B_cw - px sweep_O = 0 /\ py sweep_B_cw - py sweep_O = 0).
Proof. unfold sweep_B_cw, sweep_O; cbn [px py]. intros [_ Hy]. lra. Qed.

Lemma sweep_radius_B_pi_nonzero :
  ~ (px sweep_B_pi - px sweep_O = 0 /\ py sweep_B_pi - py sweep_O = 0).
Proof. unfold sweep_B_pi, sweep_O; cbn [px py]. intros [Hx _]. lra. Qed.

Lemma sweep_gamma_ccw_eq :
  central_angle sweep_O sweep_A sweep_B_ccw = PI / 2.
Proof.
  (* Reuse the InArc unit-quarter equality (same points as in_arc_O/A/B). *)
  change (central_angle sweep_O sweep_A sweep_B_ccw)
    with (central_angle in_arc_O in_arc_A in_arc_B).
  exact in_arc_gamma_eq.
Qed.

Lemma sweep_gamma_cw_eq :
  central_angle sweep_O sweep_A sweep_B_cw = - (PI / 2).
Proof.
  unfold central_angle, angle_between, sweep_O, sweep_A, sweep_B_cw.
  cbn [px py].
  replace ((1 - 0) * ((-1) - 0) - (0 - 0) * (0 - 0)) with (-1) by ring.
  replace ((1 - 0) * (0 - 0) + (0 - 0) * ((-1) - 0)) with 0 by ring.
  apply atan2_neg_y_axis. lra.
Qed.

Lemma sweep_gamma_pi_eq :
  central_angle sweep_O sweep_A sweep_B_pi = PI.
Proof.
  change (central_angle sweep_O sweep_A sweep_B_pi)
    with (central_angle in_arc_O in_arc_A in_arc_Q_major).
  exact in_arc_theta_Q_eq.
Qed.

(** Quarter-circle CCW witness: sweep_ccw and positive central angle. *)
Theorem sweep_ccw_unit_quarter :
  sweep_ccw sweep_O sweep_A sweep_B_ccw
  /\ 0 < central_angle sweep_O sweep_A sweep_B_ccw.
Proof.
  split.
  - unfold sweep_ccw, radius_cross, sweep_O, sweep_A, sweep_B_ccw.
    cbn [px py]. left. lra.
  - rewrite sweep_gamma_ccw_eq. pose proof PI_RGT_0. lra.
Qed.

(** Quarter-circle CW witness: not CCW, negative central angle. *)
Theorem sweep_cw_unit_quarter :
  ~ sweep_ccw sweep_O sweep_A sweep_B_cw
  /\ central_angle sweep_O sweep_A sweep_B_cw < 0.
Proof.
  split.
  - apply sweep_ccw_false_of_central_angle_neg.
    + exact sweep_radius_A_nonzero.
    + exact sweep_radius_B_cw_nonzero.
    + rewrite sweep_gamma_cw_eq. pose proof PI_RGT_0. lra.
  - rewrite sweep_gamma_cw_eq. pose proof PI_RGT_0. lra.
Qed.

(** Antipodal +π witness: still CCW under the atan2 cut. *)
Theorem sweep_ccw_unit_semicircle_pi :
  sweep_ccw sweep_O sweep_A sweep_B_pi
  /\ 0 < central_angle sweep_O sweep_A sweep_B_pi.
Proof.
  split.
  - unfold sweep_ccw, radius_cross, radius_dot, sweep_O, sweep_A, sweep_B_pi.
    cbn [px py]. right. split; lra.
  - rewrite sweep_gamma_pi_eq. pose proof PI_RGT_0. lra.
Qed.

(** Headline specialisation on the CCW quarter (both sides of the iff). *)
Corollary sweep_ccw_iff_pos_unit_quarter :
  sweep_ccw sweep_O sweep_A sweep_B_ccw
  <-> 0 < central_angle sweep_O sweep_A sweep_B_ccw.
Proof.
  apply sweep_ccw_iff_signed_central_angle_pos.
  - exact sweep_radius_A_nonzero.
  - exact sweep_radius_B_ccw_nonzero.
Qed.

(* -------------------------------------------------------------------------- *)
(* §6  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions sweep_ccw_iff_signed_central_angle_pos.
Print Assumptions sweep_ccw_unit_quarter.
Print Assumptions sweep_cw_unit_quarter.
Print Assumptions sweep_ccw_unit_semicircle_pi.
