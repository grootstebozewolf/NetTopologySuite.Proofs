(* ============================================================================
   NetTopologySuite.Proofs.InSector
   ----------------------------------------------------------------------------
   Issue #64 subtask 64-e — GREEN: closed minor circular-sector (pie-slice)
   membership.

   `InSector O A B P` packages the closed minor sector determined by centre
   [O] and distinct on-circle endpoints [A], [B]:

     - common positive radius [r = dist O A], with [B] on that circle;
     - [P] in the closed disk: [dist O P ≤ r]  (InDisk shape);
     - principal sweep [γ = central_angle O A B] is a strict minor ([|γ| < π]);
     - either [P] is the centre (sector vertex), or the directed angle
       [θ = central_angle O A P] has the same sign as [γ] (or is zero) and
       [|θ| ≤ |γ|]  (InArc angular order, without requiring [P] on the circle).

   Sibling of 64-c `InArc` (on-circle boundary only) and 64-d `InDisk`
   (full closed disk).  The sector is the angular cone of the minor arc
   clipped to the disk — the geometric region of a circular pie slice.

   Rational unit-quarter witness (O origin, A=(1,0), B=(0,1), γ = π/2):
     P_int   = (3/10, 3/10)   interior (θ = π/4, ‖P‖ < 1)
     P_ray   = (1/2, 0)       on ray OA, closed disk
     P_arc   = (3/5, 4/5)     on minor arc (also InArc)
     P_ctr   = (0, 0)         centre / sector vertex
     P_ang   = (3/10, −3/10)  wrong angle, in disk — rejected
     P_out   = (2, 2)         outside disk — rejected

   Bridge lemmas:
     `in_arc_implies_in_sector`  — every on-arc minor point is in the sector;
     `in_sector_implies_in_disk` — sector ⇒ closed disk of radius r.

   3-axiom (IVT atan2 via InArc / AngleBetween; allowlist).  No Admitted.

   Refs: issue #64, docs/issue-64-arc-primitives-triage.md
         (ask #3/#4 region packaging; sibling of 64-c InArc, 64-d InDisk).
   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
     Assisted-by: Grok (grok-4.5)
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Distance Atan2 AngleBetween InArc InDisk.

Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  InSector — closed minor circular sector (pie slice).                   *)
(* -------------------------------------------------------------------------- *)

(** Radius-vector of [P] relative to [O] is the zero vector (i.e. [P] is the
    centre).  Coordinate form so the angular test can special-case the vertex
    without feeding [atan2 0 0]. *)
Definition is_centre (O P : Point) : Prop :=
  px P - px O = 0 /\ py P - py O = 0.

(** [InSector O A B P]: [P] lies in the closed minor circular sector of centre
    [O] spanning the rays [O]->[A] and [O]->[B].

    Clauses:
      - positive common radius [r = dist O A];
      - [B] on that circle;
      - endpoints distinct;
      - [P] in the closed disk [dist O P ≤ r];
      - principal sweep [γ = central_angle O A B] is a strict minor ([|γ| < π]);
      - either [P] is the centre, or [θ = central_angle O A P] has the same
        sign as [γ] (or is zero) and [|θ| ≤ |γ|]. *)
Definition InSector (O A B P : Point) : Prop :=
  let r := dist O A in
  0 < r /\
  dist O B = r /\
  A <> B /\
  dist O P <= r /\
  let gamma := central_angle O A B in
  Rabs gamma < PI /\
  (is_centre O P
   \/
   (~ is_centre O P /\
    let theta := central_angle O A P in
    0 <= theta * gamma /\
    Rabs theta <= Rabs gamma)).

(* -------------------------------------------------------------------------- *)
(* §2  Structural bridges to InArc / InDisk.                                  *)
(* -------------------------------------------------------------------------- *)

(** Every minor-arc point is a boundary point of the sector. *)
Theorem in_arc_implies_in_sector :
  forall O A B P : Point,
    InArc O A B P -> InSector O A B P.
Proof.
  intros O A B P H.
  unfold InArc in H.
  destruct H as [Hr [HB [HP [Hne [Hmin [Hsign Hle]]]]]].
  unfold InSector.
  split; [exact Hr|].
  split; [exact HB|].
  split; [exact Hne|].
  split; [lra|].
  split; [exact Hmin|].
  (* P on the circle with r > 0 cannot be the centre. *)
  right.
  split.
  - unfold is_centre. intros [Hx Hy].
    assert (Hz : dist O P = 0).
    { apply dist_eq_zero_iff. split; lra. }
    lra.
  - exact (conj Hsign Hle).
Qed.

(** Sector membership implies closed-disk membership of radius [dist O A]. *)
Theorem in_sector_implies_in_disk :
  forall O A B P : Point,
    InSector O A B P -> InDisk O (dist O A) P.
Proof.
  intros O A B P H.
  unfold InSector in H.
  destruct H as [Hr [_ [_ [Hle _]]]].
  unfold InDisk. split; lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Rational unit-quarter sector witness.                                  *)
(* -------------------------------------------------------------------------- *)

Definition sector_O : Point := mkPoint 0 0.
Definition sector_A : Point := mkPoint 1 0.
Definition sector_B : Point := mkPoint 0 1.
(** Strict interior of the sector (rational; on the angle bisector). *)
Definition sector_P_int : Point := mkPoint (3/10) (3/10).
(** On the closed ray OA, inside the disk. *)
Definition sector_P_ray : Point := mkPoint (1/2) 0.
(** On the minor arc (3-4-5; also an InArc point). *)
Definition sector_P_arc : Point := mkPoint (3/5) (4/5).
(** Sector vertex (centre). *)
Definition sector_P_ctr : Point := mkPoint 0 0.
(** Wrong angle, still inside the unit disk — rejected. *)
Definition sector_P_ang : Point := mkPoint (3/10) (-3/10).
(** Outside the disk — rejected. *)
Definition sector_P_out : Point := mkPoint 2 2.

Lemma sector_radius_A : dist sector_O sector_A = 1.
Proof.
  unfold dist, dist_sq, sector_O, sector_A; cbn [px py].
  replace (0 - 1) with (-1) by ring.
  replace (0 - 0) with 0 by ring.
  replace ((-1) * (-1) + 0 * 0) with 1 by ring.
  exact sqrt_1.
Qed.

Lemma sector_radius_B : dist sector_O sector_B = 1.
Proof.
  unfold dist, dist_sq, sector_O, sector_B; cbn [px py].
  replace (0 - 0) with 0 by ring.
  replace (0 - 1) with (-1) by ring.
  replace (0 * 0 + (-1) * (-1)) with 1 by ring.
  exact sqrt_1.
Qed.

Lemma sector_endpoints_distinct : sector_A <> sector_B.
Proof.
  unfold sector_A, sector_B. intros Heq.
  assert (Hpx : px (mkPoint 1 0) = px (mkPoint 0 1)) by (rewrite Heq; reflexivity).
  cbn in Hpx. lra.
Qed.

Lemma sector_gamma_eq :
  central_angle sector_O sector_A sector_B = PI / 2.
Proof.
  change (central_angle sector_O sector_A sector_B)
    with (central_angle in_arc_O in_arc_A in_arc_B).
  exact in_arc_gamma_eq.
Qed.

Lemma sector_gamma_abs_lt_PI :
  Rabs (central_angle sector_O sector_A sector_B) < PI.
Proof.
  rewrite sector_gamma_eq.
  rewrite Rabs_right by (pose proof PI_RGT_0; lra).
  pose proof PI_RGT_0. lra.
Qed.

Lemma sector_P_int_dist_sq :
  dist_sq sector_O sector_P_int = (9/100) + (9/100).
Proof.
  unfold dist_sq, sector_O, sector_P_int; cbn [px py]. field.
Qed.

Lemma sector_P_int_in_disk : dist sector_O sector_P_int <= 1.
Proof.
  apply (proj2 (dist_le_iff_dist_sq_le sector_O sector_P_int 1 ltac:(lra))).
  rewrite sector_P_int_dist_sq. lra.
Qed.

Lemma sector_P_int_not_centre : ~ is_centre sector_O sector_P_int.
Proof.
  unfold is_centre, sector_O, sector_P_int; cbn [px py]. intros [Hx _]. lra.
Qed.

Lemma sector_theta_P_int_eq :
  central_angle sector_O sector_A sector_P_int = PI / 4.
Proof.
  unfold central_angle, angle_between, sector_O, sector_A, sector_P_int.
  cbn [px py].
  replace ((1 - 0) * (3 / 10 - 0) - (0 - 0) * (3 / 10 - 0)) with (3 / 10) by field.
  replace ((1 - 0) * (3 / 10 - 0) + (0 - 0) * (3 / 10 - 0)) with (3 / 10) by field.
  apply atan2_diag_PI4. lra.
Qed.

Lemma sector_theta_P_int_same_sign_le_gamma :
  let gamma := central_angle sector_O sector_A sector_B in
  let theta := central_angle sector_O sector_A sector_P_int in
  0 <= theta * gamma /\ Rabs theta <= Rabs gamma.
Proof.
  rewrite sector_gamma_eq, sector_theta_P_int_eq.
  pose proof PI_RGT_0 as HPI.
  split.
  - nra.
  - rewrite (Rabs_right (PI / 4)) by lra.
    rewrite (Rabs_right (PI / 2)) by lra.
    lra.
Qed.

Lemma sector_P_ray_dist_sq :
  dist_sq sector_O sector_P_ray = 1/4.
Proof.
  unfold dist_sq, sector_O, sector_P_ray; cbn [px py]. field.
Qed.

Lemma sector_P_ray_in_disk : dist sector_O sector_P_ray <= 1.
Proof.
  apply (proj2 (dist_le_iff_dist_sq_le sector_O sector_P_ray 1 ltac:(lra))).
  rewrite sector_P_ray_dist_sq. lra.
Qed.

Lemma sector_P_ray_not_centre : ~ is_centre sector_O sector_P_ray.
Proof.
  unfold is_centre, sector_O, sector_P_ray; cbn [px py]. intros [Hx _]. lra.
Qed.

Lemma sector_theta_P_ray_eq :
  central_angle sector_O sector_A sector_P_ray = 0.
Proof.
  unfold central_angle, angle_between, sector_O, sector_A, sector_P_ray.
  cbn [px py].
  replace ((1 - 0) * (0 - 0) - (0 - 0) * (1 / 2 - 0)) with 0 by field.
  replace ((1 - 0) * (1 / 2 - 0) + (0 - 0) * (0 - 0)) with (1 / 2) by field.
  apply atan2_pos_x_axis. lra.
Qed.

Lemma sector_theta_P_ray_same_sign_le_gamma :
  let gamma := central_angle sector_O sector_A sector_B in
  let theta := central_angle sector_O sector_A sector_P_ray in
  0 <= theta * gamma /\ Rabs theta <= Rabs gamma.
Proof.
  rewrite sector_gamma_eq, sector_theta_P_ray_eq.
  pose proof PI_RGT_0 as HPI.
  split.
  - nra.
  - rewrite (Rabs_R0).
    rewrite (Rabs_right (PI / 2)) by lra.
    lra.
Qed.

Lemma sector_P_arc_in_disk : dist sector_O sector_P_arc <= 1.
Proof.
  (* Reuse the InArc unit-circle equality: P_arc = in_arc_P. *)
  change sector_O with in_arc_O.
  change sector_P_arc with in_arc_P.
  rewrite in_arc_radius_P. lra.
Qed.

Lemma sector_P_ctr_is_centre : is_centre sector_O sector_P_ctr.
Proof.
  unfold is_centre, sector_O, sector_P_ctr; cbn [px py]. split; ring.
Qed.

Lemma sector_P_ctr_in_disk : dist sector_O sector_P_ctr <= 1.
Proof.
  unfold dist, dist_sq, sector_O, sector_P_ctr; cbn [px py].
  replace (0 - 0) with 0 by ring.
  replace (0 * 0 + 0 * 0) with 0 by ring.
  rewrite sqrt_0. lra.
Qed.

Lemma sector_P_ang_dist_sq :
  dist_sq sector_O sector_P_ang = (9/100) + (9/100).
Proof.
  unfold dist_sq, sector_O, sector_P_ang; cbn [px py]. field.
Qed.

Lemma sector_P_ang_in_disk : dist sector_O sector_P_ang <= 1.
Proof.
  apply (proj2 (dist_le_iff_dist_sq_le sector_O sector_P_ang 1 ltac:(lra))).
  rewrite sector_P_ang_dist_sq. lra.
Qed.

Lemma sector_P_ang_not_centre : ~ is_centre sector_O sector_P_ang.
Proof.
  unfold is_centre, sector_O, sector_P_ang; cbn [px py]. intros [Hx _]. lra.
Qed.

Lemma sector_theta_P_ang_eq :
  central_angle sector_O sector_A sector_P_ang = - (PI / 4).
Proof.
  unfold central_angle, angle_between, sector_O, sector_A, sector_P_ang.
  cbn [px py].
  replace ((1 - 0) * ((-3) / 10 - 0) - (0 - 0) * (3 / 10 - 0))
    with (- (3 / 10)) by field.
  replace ((1 - 0) * (3 / 10 - 0) + (0 - 0) * ((-3) / 10 - 0))
    with (3 / 10) by field.
  apply atan2_neg_diag. lra.
Qed.

Lemma sector_P_out_dist_sq :
  dist_sq sector_O sector_P_out = 8.
Proof.
  unfold dist_sq, sector_O, sector_P_out; cbn [px py]. ring.
Qed.

Lemma sector_P_out_not_in_disk : ~ (dist sector_O sector_P_out <= 1).
Proof.
  intros Hle.
  pose proof (proj1 (dist_le_iff_dist_sq_le sector_O sector_P_out 1 ltac:(lra)) Hle)
    as Hsq.
  rewrite sector_P_out_dist_sq in Hsq. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §4  Headlines — fully Qed.                                                 *)
(* -------------------------------------------------------------------------- *)

(** Strict-interior rational point of the unit quarter-sector. *)
Theorem in_sector_strict_interior_witness :
  InSector sector_O sector_A sector_B sector_P_int.
Proof.
  unfold InSector.
  rewrite sector_radius_A.
  split; [lra|].
  split; [exact sector_radius_B|].
  split; [exact sector_endpoints_distinct|].
  split; [exact sector_P_int_in_disk|].
  split; [exact sector_gamma_abs_lt_PI|].
  right.
  split; [exact sector_P_int_not_centre|].
  exact sector_theta_P_int_same_sign_le_gamma.
Qed.

(** Closed ray OA (half-open from centre to A) lies in the sector. *)
Theorem in_sector_boundary_ray_witness :
  InSector sector_O sector_A sector_B sector_P_ray.
Proof.
  unfold InSector.
  rewrite sector_radius_A.
  split; [lra|].
  split; [exact sector_radius_B|].
  split; [exact sector_endpoints_distinct|].
  split; [exact sector_P_ray_in_disk|].
  split; [exact sector_gamma_abs_lt_PI|].
  right.
  split; [exact sector_P_ray_not_centre|].
  exact sector_theta_P_ray_same_sign_le_gamma.
Qed.

(** Minor-arc boundary point (3-4-5) lies in the sector; via InArc bridge. *)
Theorem in_sector_boundary_arc_witness :
  InSector sector_O sector_A sector_B sector_P_arc.
Proof.
  apply in_arc_implies_in_sector.
  change sector_O with in_arc_O.
  change sector_A with in_arc_A.
  change sector_B with in_arc_B.
  change sector_P_arc with in_arc_P.
  exact in_arc_point_on_minor_arc.
Qed.

(** Sector centre (vertex) is included. *)
Theorem in_sector_centre_witness :
  InSector sector_O sector_A sector_B sector_P_ctr.
Proof.
  unfold InSector.
  rewrite sector_radius_A.
  split; [lra|].
  split; [exact sector_radius_B|].
  split; [exact sector_endpoints_distinct|].
  split; [exact sector_P_ctr_in_disk|].
  split; [exact sector_gamma_abs_lt_PI|].
  left. exact sector_P_ctr_is_centre.
Qed.

(** Wrong-angle point inside the disk is rejected. *)
Theorem in_sector_wrong_angle_rejected :
  ~ InSector sector_O sector_A sector_B sector_P_ang.
Proof.
  unfold InSector.
  rewrite sector_radius_A.
  intros [_ [_ [_ [_ [_ Hang]]]]].
  destruct Hang as [Hc | [Hnc Hord]].
  - apply sector_P_ang_not_centre. exact Hc.
  - destruct Hord as [Hsign Hle].
    rewrite sector_gamma_eq, sector_theta_P_ang_eq in Hsign.
    (* θ = −π/4, γ = π/2 ⇒ θ·γ = −π²/8 < 0 *)
    pose proof PI_RGT_0 as HPI.
    nra.
Qed.

(** Exterior point (outside the disk) is rejected. *)
Theorem in_sector_exterior_rejected :
  ~ InSector sector_O sector_A sector_B sector_P_out.
Proof.
  unfold InSector.
  rewrite sector_radius_A.
  intros [_ [_ [_ [Hle _]]]].
  apply sector_P_out_not_in_disk. exact Hle.
Qed.

(** Bridge specialisation: unit-quarter InArc point implies sector. *)
Corollary in_arc_implies_in_sector_unit_quarter :
  InArc sector_O sector_A sector_B sector_P_arc ->
  InSector sector_O sector_A sector_B sector_P_arc.
Proof. apply in_arc_implies_in_sector. Qed.

(** Bridge specialisation: sector interior implies InDisk of radius 1. *)
Corollary in_sector_implies_in_disk_unit_quarter :
  InSector sector_O sector_A sector_B sector_P_int ->
  InDisk sector_O 1 sector_P_int.
Proof.
  intro H. rewrite <- sector_radius_A.
  eapply in_sector_implies_in_disk. exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* §5  Audit footprint.                                                       *)
(* -------------------------------------------------------------------------- *)

Print Assumptions in_sector_strict_interior_witness.
Print Assumptions in_sector_boundary_ray_witness.
Print Assumptions in_sector_boundary_arc_witness.
Print Assumptions in_sector_centre_witness.
Print Assumptions in_sector_wrong_angle_rejected.
Print Assumptions in_sector_exterior_rejected.
Print Assumptions in_arc_implies_in_sector.
Print Assumptions in_sector_implies_in_disk.
