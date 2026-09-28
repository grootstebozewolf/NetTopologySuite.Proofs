(* ============================================================================
   NetTopologySuite.Proofs.InArc
   ----------------------------------------------------------------------------
   Issue #64 subtask 64-c — GREEN: the in-arc predicate for a point on the
   minor arc between two distinct endpoints on a circle.

   `InArc O A B P` packages minor-arc membership via central-angle order
   (principal `angle_between` / `atan2`).  The rational unit-circle witness
   closes both headline claims with `Qed` (no Abort, no Admitted):

     A = (1, 0)           principal angle 0
     P = (3/5, 4/5)       3-4-5 point, θ = atan(4/3) ∈ (0, π/2)
     B = (0, 1)           principal angle π/2
     Q = (-1, 0)          principal angle π  (major-arc counter-position)

   Endpoints A,B distinct; minor arc A→B has central angle π/2 < π; P is
   strictly between them; Q on the complementary major arc is rejected by
   |θ_Q| = π > π/2 = |γ|.

   3-axiom (IVT atan2 via AngleBetween; allowlist).  No Admitted.

   Refs: issue #64, docs/issue-64-arc-primitives-triage.md (ask #3 / in-arc).
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Grok (grok-4.5)
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance Atan2 AngleBetween Atan2RatanBridge.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  InArc — minor-arc membership via central-angle order.                  *)
(* -------------------------------------------------------------------------- *)

(** Signed central angle at [O] from ray [O]->[X] to ray [O]->[Y]. *)
Definition central_angle (O X Y : Point) : R :=
  angle_between (px X - px O) (py X - py O)
                (px Y - px O) (py Y - py O).

(** [InArc O A B P]: [P] lies on the closed minor arc of the circle
    centred at [O] from endpoint [A] to endpoint [B].

    Clauses:
      - positive common radius [r = dist O A];
      - [B] and [P] on that circle;
      - endpoints distinct;
      - principal sweep [γ = central_angle O A B] is a strict minor ([|γ| < π]);
      - [θ = central_angle O A P] has the same sign as [γ] (or is zero) and
        [|θ| ≤ |γ|] (angularly between [A] and [B], including endpoints). *)
Definition InArc (O A B P : Point) : Prop :=
  let r := dist O A in
  0 < r /\
  dist O B = r /\
  dist O P = r /\
  A <> B /\
  let gamma := central_angle O A B in
  let theta := central_angle O A P in
  Rabs gamma < PI /\
  0 <= theta * gamma /\
  Rabs theta <= Rabs gamma.

(* -------------------------------------------------------------------------- *)
(* §2  Rational unit-circle witness (3-4-5 interior point).                   *)
(* -------------------------------------------------------------------------- *)

Definition in_arc_O : Point := mkPoint 0 0.
Definition in_arc_A : Point := mkPoint 1 0.
Definition in_arc_B : Point := mkPoint 0 1.
(** Interior test point on the minor arc A→B (rational coords, on unit circle). *)
Definition in_arc_P : Point := mkPoint (3/5) (4/5).
(** Counter-position: on the complementary major arc from A to B. *)
Definition in_arc_Q_major : Point := mkPoint (-1) 0.

Lemma in_arc_A_on_unit :
  dist_sq in_arc_O in_arc_A = 1.
Proof. unfold in_arc_O, in_arc_A, dist_sq; cbn [px py]; lra. Qed.

Lemma in_arc_B_on_unit :
  dist_sq in_arc_O in_arc_B = 1.
Proof. unfold in_arc_O, in_arc_B, dist_sq; cbn [px py]; lra. Qed.

Lemma in_arc_P_on_unit :
  dist_sq in_arc_O in_arc_P = 1.
Proof. unfold in_arc_O, in_arc_P, dist_sq; cbn [px py]; field. Qed.

Lemma in_arc_Q_major_on_unit :
  dist_sq in_arc_O in_arc_Q_major = 1.
Proof. unfold in_arc_O, in_arc_Q_major, dist_sq; cbn [px py]; lra. Qed.

Lemma in_arc_radius_A : dist in_arc_O in_arc_A = 1.
Proof. unfold dist. rewrite in_arc_A_on_unit. exact sqrt_1. Qed.

Lemma in_arc_radius_B : dist in_arc_O in_arc_B = 1.
Proof. unfold dist. rewrite in_arc_B_on_unit. exact sqrt_1. Qed.

Lemma in_arc_radius_P : dist in_arc_O in_arc_P = 1.
Proof. unfold dist. rewrite in_arc_P_on_unit. exact sqrt_1. Qed.

Lemma in_arc_radius_Q : dist in_arc_O in_arc_Q_major = 1.
Proof. unfold dist. rewrite in_arc_Q_major_on_unit. exact sqrt_1. Qed.

Lemma in_arc_endpoints_distinct : in_arc_A <> in_arc_B.
Proof.
  unfold in_arc_A, in_arc_B. intros Heq.
  assert (Hpx : px (mkPoint 1 0) = px (mkPoint 0 1)) by (rewrite Heq; reflexivity).
  cbn in Hpx. lra.
Qed.

Lemma in_arc_P_not_endpoint :
  in_arc_P <> in_arc_A /\ in_arc_P <> in_arc_B.
Proof.
  unfold in_arc_P, in_arc_A, in_arc_B. split; intros Heq.
  - assert (Hpy : py (mkPoint (3/5) (4/5)) = py (mkPoint 1 0))
      by (rewrite Heq; reflexivity).
    cbn in Hpy. lra.
  - assert (Hpx : px (mkPoint (3/5) (4/5)) = px (mkPoint 0 1))
      by (rewrite Heq; reflexivity).
    cbn in Hpx. lra.
Qed.

Lemma in_arc_Q_major_not_endpoint :
  in_arc_Q_major <> in_arc_A /\ in_arc_Q_major <> in_arc_B.
Proof.
  unfold in_arc_Q_major, in_arc_A, in_arc_B. split; intros Heq.
  - assert (Hpx : px (mkPoint (-1) 0) = px (mkPoint 1 0))
      by (rewrite Heq; reflexivity).
    cbn in Hpx. lra.
  - assert (Hpx : px (mkPoint (-1) 0) = px (mkPoint 0 1))
      by (rewrite Heq; reflexivity).
    cbn in Hpx. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Concrete central angles on the unit-circle witness.                    *)
(* -------------------------------------------------------------------------- *)

Lemma in_arc_gamma_eq :
  central_angle in_arc_O in_arc_A in_arc_B = PI / 2.
Proof.
  unfold central_angle, angle_between, in_arc_O, in_arc_A, in_arc_B.
  cbn [px py].
  replace ((1 - 0) * (1 - 0) - (0 - 0) * (0 - 0)) with 1 by ring.
  replace ((1 - 0) * (0 - 0) + (0 - 0) * (1 - 0)) with 0 by ring.
  apply atan2_pos_y_axis. lra.
Qed.

Lemma in_arc_theta_P_eq :
  central_angle in_arc_O in_arc_A in_arc_P = atan (4 / 3).
Proof.
  unfold central_angle, angle_between, in_arc_O, in_arc_A, in_arc_P.
  cbn [px py].
  replace ((1 - 0) * (4 / 5 - 0) - (0 - 0) * (3 / 5 - 0)) with (4 / 5) by field.
  replace ((1 - 0) * (3 / 5 - 0) + (0 - 0) * (4 / 5 - 0)) with (3 / 5) by field.
  rewrite atan2_pos_x_eq_atan by lra.
  f_equal. field.
Qed.

Lemma in_arc_theta_Q_eq :
  central_angle in_arc_O in_arc_A in_arc_Q_major = PI.
Proof.
  unfold central_angle, angle_between, in_arc_O, in_arc_A, in_arc_Q_major.
  cbn [px py].
  replace ((1 - 0) * (0 - 0) - (0 - 0) * (-1 - 0)) with 0 by ring.
  replace ((1 - 0) * (-1 - 0) + (0 - 0) * (0 - 0)) with (-1) by ring.
  apply atan2_neg_x_axis. lra.
Qed.

Lemma in_arc_theta_P_pos_lt_PI2 :
  0 < atan (4 / 3) < PI / 2.
Proof.
  split.
  - rewrite <- atan_0. apply atan_increasing. lra.
  - pose proof (atan_bound (4 / 3)). lra.
Qed.

Lemma in_arc_gamma_abs_lt_PI :
  Rabs (central_angle in_arc_O in_arc_A in_arc_B) < PI.
Proof.
  rewrite in_arc_gamma_eq.
  rewrite Rabs_right by (pose proof PI_RGT_0; lra).
  pose proof PI_RGT_0. lra.
Qed.

Lemma in_arc_theta_P_same_sign_le_gamma :
  let gamma := central_angle in_arc_O in_arc_A in_arc_B in
  let theta := central_angle in_arc_O in_arc_A in_arc_P in
  0 <= theta * gamma /\ Rabs theta <= Rabs gamma.
Proof.
  rewrite in_arc_gamma_eq.
  unfold central_angle, angle_between, in_arc_O, in_arc_A, in_arc_P.
  cbn [px py].
  replace ((1 - 0) * (4 / 5 - 0) - (0 - 0) * (3 / 5 - 0)) with (4 / 5) by field.
  replace ((1 - 0) * (3 / 5 - 0) + (0 - 0) * (4 / 5 - 0)) with (3 / 5) by field.
  pose proof (atan2_open_first_quadrant (3 / 5) (4 / 5) ltac:(lra) ltac:(lra)) as Hq.
  destruct Hq as [Hp Hlt].
  pose proof PI_RGT_0 as HPI.
  split.
  - apply Rmult_le_pos; [apply Rlt_le; exact Hp | lra].
  - rewrite (Rabs_right (atan2 (4 / 5) (3 / 5)) (Rle_ge _ _ (Rlt_le _ _ Hp))).
    rewrite (Rabs_right (PI / 2) ltac:(lra)).
    apply Rlt_le. exact Hlt.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Headlines — fully Qed.                                                 *)
(* -------------------------------------------------------------------------- *)

(** Point on the minor arc between distinct endpoints satisfies [InArc].
    Witness: [in_arc_P] between [in_arc_A] and [in_arc_B] about [in_arc_O]. *)
Theorem in_arc_point_on_minor_arc :
  InArc in_arc_O in_arc_A in_arc_B in_arc_P.
Proof.
  unfold InArc.
  rewrite in_arc_radius_A.
  split; [lra|].
  split; [rewrite in_arc_radius_B; reflexivity|].
  split; [rewrite in_arc_radius_P; reflexivity|].
  split; [exact in_arc_endpoints_distinct|].
  split; [exact in_arc_gamma_abs_lt_PI|].
  exact in_arc_theta_P_same_sign_le_gamma.
Qed.

(** Complementary major-arc point does not satisfy [InArc].
    Witness: [in_arc_Q_major] (|θ| = π > π/2 = |γ|). *)
Theorem in_arc_point_on_major_arc_rejected :
  ~ InArc in_arc_O in_arc_A in_arc_B in_arc_Q_major.
Proof.
  unfold InArc.
  rewrite in_arc_radius_A.
  intros [_ [_ [_ [_ [_ [_ Hle]]]]]].
  rewrite in_arc_gamma_eq, in_arc_theta_Q_eq in Hle.
  pose proof PI_RGT_0 as HPI.
  rewrite (Rabs_right PI) in Hle by lra.
  rewrite (Rabs_right (PI / 2)) in Hle by lra.
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions in_arc_point_on_minor_arc.
Print Assumptions in_arc_point_on_major_arc_rejected.
