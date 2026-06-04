(* ============================================================================
   NetTopologySuite.Proofs.BufferBridgeComplete
   ----------------------------------------------------------------------------
   The COMPLETENESS half of H_bridge, at the buffer-boundary distance level --
   the symmetric mirror of BufferBridgeSound.v.

   `BufferBridge.v` split the buffer headline's H_bridge into
   `buffer_extract_sound` (result within d) and `buffer_extract_complete`
   (the d-neighbourhood is covered).  BufferBridgeSound.v pinned the soundness
   side: the offset/bevel boundary stays inside the corner's d-ball, while the
   miter apex OVERSHOOTS it (`miter_apex_dist_sq_90 = 2 d^2 > d^2`).

   This file pins the completeness side with the dual obstruction: the
   chord-approximated (bevel) join UNDERSHOOTS the corner's d-ball.  The chord
   between the two offset endpoints -- each on the radius-d circle about the
   corner -- dips strictly inside that circle (its midpoint is the median foot,
   nearer than d for any genuine turn).  So the chord-buffer's corner boundary
   falls short of the d-neighbourhood, leaving an uncovered annular sliver
   between the chord and the true arc: completeness fails for the
   chord-approximated buffer.

   Concretely, mirroring `miter_apex_dist_sq_90 = 2 d^2`:
       chord_midpoint_dist_sq_90 = d^2 / 2   (the chord midpoint at d/sqrt 2),
   so the corner of the d-neighbourhood (distance exactly d) lies strictly
   beyond the chord (d/sqrt 2) and strictly inside the miter apex (sqrt 2 * d).
   Only the exact arc meets the d-circle; that is precisely why H_bridge holds
   exactly only for the idealised round buffer, and is carried as
   `buffer_extract_complete` / `buffer_extract_sound` otherwise.

   Bridgeheaded on the closed `BufferBevel.bevel_length_sq_dot` and
   `BufferOffset.vmag_sq_unit_perp`.  Pure-R; three-axiom footprint.
   No `Admitted` / `Axiom` / `Parameter`.

   Author: NetTopologySuite.Proofs contributors
   License: BSD-3-Clause (see LICENSE)
   AI assistance disclosure: AI-drafted, human-reviewed.
   ========================================================================== *)

From Stdlib Require Import Reals Lra.
From NTS.Proofs Require Import Real Vec Distance Direction HotPixel
                               BufferOffset BufferBevel BufferBridgeSound.
Local Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* §1  Helpers: squared offset radius and the median (parallelogram) law.     *)
(* -------------------------------------------------------------------------- *)

(* Each bevel/offset endpoint is at squared distance d^2 from the corner. *)
Lemma bevel_point_dist_sq :
  forall (V : Point) (ein : Vec) (d : R),
    ein <> vzero -> dist_sq V (bevel_point V ein d) = d * d.
Proof.
  intros V ein d Hne. unfold bevel_point. rewrite dist_sq_translate.
  replace ((d * vx (unit_perp ein)) * (d * vx (unit_perp ein)) +
           (d * vy (unit_perp ein)) * (d * vy (unit_perp ein)))
    with (d * d * vmag_sq (unit_perp ein)) by (unfold vmag_sq, vdot; ring).
  rewrite (vmag_sq_unit_perp ein Hne). ring.
Qed.

(* The median length law: the foot of the median from V to chord AB. *)
Lemma median_dist_sq_half :
  forall V A B : Point,
    4 * dist_sq V (segment_point A B (1 / 2))
    = 2 * dist_sq V A + 2 * dist_sq V B - dist_sq A B.
Proof.
  intros V A B. unfold dist_sq, segment_point. simpl. field.
Qed.

(* -------------------------------------------------------------------------- *)
(* §2  The general chord undershoot.                                          *)
(* -------------------------------------------------------------------------- *)

(* For any genuine corner (nondegenerate chord), the chord midpoint is
   STRICTLY inside the corner's d-ball -- the chord-buffer boundary falls
   short of the d-neighbourhood.  The dual of miter_apex_overshoots_vertex. *)
Theorem chord_midpoint_undershoots_vertex :
  forall (V : Point) (ein eout : Vec) (d : R),
    ein <> vzero -> eout <> vzero ->
    0 < dist_sq (bevel_point V ein d) (bevel_point V eout d) ->
    dist_sq V (segment_point (bevel_point V ein d) (bevel_point V eout d) (1 / 2))
      < d * d.
Proof.
  intros V ein eout d Hin Hout Hchord.
  pose proof (median_dist_sq_half V (bevel_point V ein d) (bevel_point V eout d)) as Hmed.
  rewrite (bevel_point_dist_sq V ein d Hin),
          (bevel_point_dist_sq V eout d Hout) in Hmed.
  lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* §3  Concrete unit right-angle corner: chord midpoint at d^2 / 2.           *)
(* -------------------------------------------------------------------------- *)

Lemma mkVec10_nonzero : mkVec 1 0 <> vzero.
Proof. intro H. apply (f_equal vx) in H. unfold vzero in H. simpl in H. lra. Qed.

Lemma mkVec01_nonzero : mkVec 0 1 <> vzero.
Proof. intro H. apply (f_equal vy) in H. unfold vzero in H. simpl in H. lra. Qed.

(* The bevel chord of the unit right-angle corner has squared length 2 d^2
   (the two offset endpoints are at right angles about V). *)
Lemma chord_len_sq_90 :
  forall d : R,
    dist_sq (bevel_point (mkPoint 0 0) (mkVec 1 0) d)
            (bevel_point (mkPoint 0 0) (mkVec 0 1) d) = 2 * (d * d).
Proof.
  intros d.
  rewrite (bevel_length_sq_dot (mkPoint 0 0) (mkVec 1 0) (mkVec 0 1) d
             mkVec10_nonzero mkVec01_nonzero).
  rewrite vmag_unit_x, vmag_unit_y. unfold vdot. simpl. field.
Qed.

(* Hence the chord midpoint is at squared distance d^2 / 2 from the corner --
   strictly inside the d-ball (compare miter_apex_dist_sq_90 = 2 d^2). *)
Lemma chord_midpoint_dist_sq_90 :
  forall d : R,
    dist_sq (mkPoint 0 0)
            (segment_point (bevel_point (mkPoint 0 0) (mkVec 1 0) d)
                           (bevel_point (mkPoint 0 0) (mkVec 0 1) d) (1 / 2))
    = (d * d) / 2.
Proof.
  intros d.
  pose proof (median_dist_sq_half (mkPoint 0 0)
                (bevel_point (mkPoint 0 0) (mkVec 1 0) d)
                (bevel_point (mkPoint 0 0) (mkVec 0 1) d)) as Hmed.
  rewrite (bevel_point_dist_sq (mkPoint 0 0) (mkVec 1 0) d mkVec10_nonzero),
          (bevel_point_dist_sq (mkPoint 0 0) (mkVec 0 1) d mkVec01_nonzero),
          (chord_len_sq_90 d) in Hmed.
  lra.
Qed.

(* The chord-buffer corner strictly undershoots the d-neighbourhood. *)
Theorem chord_midpoint_undershoots_90 :
  forall d : R,
    0 < d ->
    dist_sq (mkPoint 0 0)
            (segment_point (bevel_point (mkPoint 0 0) (mkVec 1 0) d)
                           (bevel_point (mkPoint 0 0) (mkVec 0 1) d) (1 / 2))
      < d * d.
Proof.
  intros d Hd. rewrite chord_midpoint_dist_sq_90. nra.
Qed.

Print Assumptions chord_midpoint_undershoots_vertex.
Print Assumptions chord_midpoint_undershoots_90.
